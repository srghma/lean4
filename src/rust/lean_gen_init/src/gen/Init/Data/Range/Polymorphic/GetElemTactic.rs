// Lean compiler output
// Module: Init.Data.Range.Polymorphic.GetElemTactic
// Imports: Init.Grind.Tactics Init.Data.Range.Polymorphic.Basic Init.Data.Vector.Basic Init.Data.Slice.Array.Lemmas
use crate::r#gen::Init::Data::Range::Polymorphic::Basic::{
    initialize_Init_Data_Range_Polymorphic_Basic,
    runtime_initialize_Init_Data_Range_Polymorphic_Basic,
};
use crate::r#gen::Init::Data::Slice::Array::Lemmas::{
    initialize_Init_Data_Slice_Array_Lemmas, runtime_initialize_Init_Data_Slice_Array_Lemmas,
};
use crate::r#gen::Init::Data::Vector::Basic::{
    initialize_Init_Data_Vector_Basic, runtime_initialize_Init_Data_Vector_Basic,
};
use crate::r#gen::Init::Grind::Tactics::{
    initialize_Init_Grind_Tactics, runtime_initialize_Init_Grind_Tactics,
};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_isOfKind, l_Lean_Syntax_node1,
    l_Lean_Syntax_node2, l_Lean_Syntax_node3, l_Lean_Syntax_node4, l_Lean_Syntax_node6,
    l_Lean_addMacroScope, l_String_toRawSubstring_x27,
};
use crate::lean_imports_rs::Init::Prelude::{lean_array_push, lean_mk_empty_array_with_capacity};
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__0_value: crate::leanh::LeanStringObject<33> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [116, 97, 99, 116, 105, 99, 71, 101, 116, 95, 101, 108, 101, 109, 95, 116, 97, 99, 116, 105, 99, 95, 101, 120, 116, 101, 110, 115, 105, 98, 108, 101, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__0_value) as *mut crate::leanh::LeanObject,7705027380931481693 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__5_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [102, 105, 114, 115, 116, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__5_value) as *mut crate::leanh::LeanObject;
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__6_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__6_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__6_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__6_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__6_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__5_value) as *mut crate::leanh::LeanObject,12551601070224435259 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__7_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__7_value) as *mut crate::leanh::LeanObject,9855511589286918680 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__9_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [103, 114, 111, 117, 112, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__10_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__9_value) as *mut crate::leanh::LeanObject,2214559063752339918 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__11_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [124, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__12_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__12_value) as *mut crate::leanh::LeanObject;
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__13_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__13_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__13_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__13_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__13_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__13_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__13_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__12_value) as *mut crate::leanh::LeanObject,8504843326314613972 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__14_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__14_value) as *mut crate::leanh::LeanObject;
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__14_value) as *mut crate::leanh::LeanObject,17228437386856258271 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__16_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [116, 97, 99, 116, 105, 99, 84, 114, 121, 95, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__16_value) as *mut crate::leanh::LeanObject;
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__16_value) as *mut crate::leanh::LeanObject,10962186005905108258 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__18_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [116, 114, 121, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__18_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__19_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [114, 119, 83, 101, 113, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__19: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__19_value) as *mut crate::leanh::LeanObject;
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__20_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__20_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__20_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__20_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__20_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__20_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__20_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__19_value) as *mut crate::leanh::LeanObject,11075965128531316786 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__20: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__20_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__21_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [114, 119, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__21: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__21_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__22_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [111, 112, 116, 67, 111, 110, 102, 105, 103, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__22: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__22_value) as *mut crate::leanh::LeanObject;
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__23_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__23_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__23_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__23_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__23_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__23_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__23_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__22_value) as *mut crate::leanh::LeanObject,3488656302031949961 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__23: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__23_value) as *mut crate::leanh::LeanObject;
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__24_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__24: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__25_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [114, 119, 82, 117, 108, 101, 83, 101, 113, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__25: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__25_value) as *mut crate::leanh::LeanObject;
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__26_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__26_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__26_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__26_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__26_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__26_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__26_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__25_value) as *mut crate::leanh::LeanObject,7234207980690920618 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__26: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__26_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__27_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [91, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__27: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__27_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__28_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [114, 119, 82, 117, 108, 101, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__28: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__28_value) as *mut crate::leanh::LeanObject;
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__29_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__29_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__29_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__29_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__29_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__29_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__29_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__28_value) as *mut crate::leanh::LeanObject,8860902369834437795 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__29: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__29_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__30_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [83, 116, 100, 46, 82, 99, 99, 46, 109, 101, 109, 95, 105, 102, 102, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__30: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__30_value) as *mut crate::leanh::LeanObject;
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__31_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__31: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__32_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [83, 116, 100, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__32: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__32_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__33_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [82, 99, 99, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__33: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__33_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__34_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [109, 101, 109, 95, 105, 102, 102, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__34: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__34_value) as *mut crate::leanh::LeanObject;
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__35_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__32_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__35_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__35_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__33_value) as *mut crate::leanh::LeanObject,16437420457889295896 as *mut crate::leanh::LeanObject] };
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__35_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__35_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__34_value) as *mut crate::leanh::LeanObject,12281829995128736985 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__35: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__35_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__36_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__35_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__36: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__36_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__37_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__36_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__37: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__37_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__38_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__38: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__38_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__39_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [108, 111, 99, 97, 116, 105, 111, 110, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__39: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__39_value) as *mut crate::leanh::LeanObject;
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__40_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__40_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__40_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__40_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__40_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__40_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__40_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__39_value) as *mut crate::leanh::LeanObject,1767494567867404924 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__40: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__40_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__41_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [97, 116, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__41: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__41_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__42_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [108, 111, 99, 97, 116, 105, 111, 110, 87, 105, 108, 100, 99, 97, 114, 100, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__42: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__42_value) as *mut crate::leanh::LeanObject;
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__43_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__43_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__43_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__43_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__43_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__43_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__43_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__42_value) as *mut crate::leanh::LeanObject,1262264483427375750 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__43: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__43_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__44_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [42, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__44: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__44_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__45_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [83, 116, 100, 46, 82, 99, 111, 46, 109, 101, 109, 95, 105, 102, 102, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__45: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__45_value) as *mut crate::leanh::LeanObject;
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__46_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__46: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__47_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [82, 99, 111, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__47: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__47_value) as *mut crate::leanh::LeanObject;
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__48_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__32_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__48_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__48_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__47_value) as *mut crate::leanh::LeanObject,36003929318889298 as *mut crate::leanh::LeanObject] };
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__48_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__48_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__34_value) as *mut crate::leanh::LeanObject,928736995045147883 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__48: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__48_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__49_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__48_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__49: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__49_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__50_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__49_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__50: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__50_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__51_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [83, 116, 100, 46, 82, 99, 105, 46, 109, 101, 109, 95, 105, 102, 102, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__51: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__51_value) as *mut crate::leanh::LeanObject;
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__52_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__52: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__53_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [82, 99, 105, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__53: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__53_value) as *mut crate::leanh::LeanObject;
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__54_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__32_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__54_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__54_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__53_value) as *mut crate::leanh::LeanObject,1178185768520342099 as *mut crate::leanh::LeanObject] };
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__54_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__54_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__34_value) as *mut crate::leanh::LeanObject,17702854388927448150 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__54: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__54_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__55_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__54_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__55: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__55_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__56_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__55_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__56: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__56_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__57_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [83, 116, 100, 46, 82, 111, 99, 46, 109, 101, 109, 95, 105, 102, 102, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__57: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__57_value) as *mut crate::leanh::LeanObject;
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__58_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__58: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__59_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [82, 111, 99, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__59: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__59_value) as *mut crate::leanh::LeanObject;
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__60_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__32_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__60_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__60_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__59_value) as *mut crate::leanh::LeanObject,16615662997495850524 as *mut crate::leanh::LeanObject] };
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__60_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__60_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__34_value) as *mut crate::leanh::LeanObject,11433193217098006149 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__60: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__60_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__61_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__60_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__61: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__61_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__62_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__61_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__62: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__62_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__63_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [83, 116, 100, 46, 82, 111, 111, 46, 109, 101, 109, 95, 105, 102, 102, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__63: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__63_value) as *mut crate::leanh::LeanObject;
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__64_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__64: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__65_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [82, 111, 111, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__65: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__65_value) as *mut crate::leanh::LeanObject;
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__66_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__32_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__66_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__66_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__65_value) as *mut crate::leanh::LeanObject,17971250720669795982 as *mut crate::leanh::LeanObject] };
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__66_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__66_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__34_value) as *mut crate::leanh::LeanObject,16504686654980465375 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__66: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__66_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__67_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__66_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__67: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__67_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__68_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__67_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__68: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__68_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__69_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [83, 116, 100, 46, 82, 111, 105, 46, 109, 101, 109, 95, 105, 102, 102, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__69: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__69_value) as *mut crate::leanh::LeanObject;
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__70_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__70: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__71_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [82, 111, 105, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__71: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__71_value) as *mut crate::leanh::LeanObject;
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__72_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__32_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__72_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__72_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__71_value) as *mut crate::leanh::LeanObject,16217565746838389087 as *mut crate::leanh::LeanObject] };
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__72_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__72_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__34_value) as *mut crate::leanh::LeanObject,8831110726530625114 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__72: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__72_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__73_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__72_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__73: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__73_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__74_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__73_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__74: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__74_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__75_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [83, 116, 100, 46, 82, 105, 99, 46, 109, 101, 109, 95, 105, 102, 102, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__75: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__75_value) as *mut crate::leanh::LeanObject;
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__76_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__76: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__77_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [82, 105, 99, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__77: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__77_value) as *mut crate::leanh::LeanObject;
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__78_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__32_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__78_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__78_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__77_value) as *mut crate::leanh::LeanObject,8649810267064386489 as *mut crate::leanh::LeanObject] };
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__78_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__78_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__34_value) as *mut crate::leanh::LeanObject,7977557830016682532 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__78: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__78_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__79_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__78_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__79: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__79_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__80_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__79_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__80: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__80_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__81_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [83, 116, 100, 46, 82, 105, 111, 46, 109, 101, 109, 95, 105, 102, 102, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__81: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__81_value) as *mut crate::leanh::LeanObject;
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__82_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__82: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__83_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [82, 105, 111, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__83: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__83_value) as *mut crate::leanh::LeanObject;
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__84_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__32_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__84_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__84_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__83_value) as *mut crate::leanh::LeanObject,10504416010916204673 as *mut crate::leanh::LeanObject] };
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__84_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__84_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__34_value) as *mut crate::leanh::LeanObject,7709041994438704924 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__84: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__84_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__85_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__84_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__85: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__85_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__86_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__85_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__86: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__86_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__87_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [83, 116, 100, 46, 82, 105, 105, 46, 109, 101, 109, 95, 105, 102, 102, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__87: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__87_value) as *mut crate::leanh::LeanObject;
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__88_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__88: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__89_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [82, 105, 105, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__89: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__89_value) as *mut crate::leanh::LeanObject;
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__90_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__32_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__90_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__90_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__89_value) as *mut crate::leanh::LeanObject,15880302354919066316 as *mut crate::leanh::LeanObject] };
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__90_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__90_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__34_value) as *mut crate::leanh::LeanObject,9223845264041314549 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__90: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__90_value) as *mut crate::leanh::LeanObject;
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__91_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__32_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__91_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__91_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__89_value) as *mut crate::leanh::LeanObject,15880302354919066316 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__91: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__91_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__92_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__34_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__92: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__92_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__93_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__91_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__92_value) as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__93: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__93_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__94_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__93_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__94: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__94_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__95_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [100, 115, 105, 109, 112, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__95: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__95_value) as *mut crate::leanh::LeanObject;
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__96_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__96_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__96_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__96_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__96_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__96_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__96_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__95_value) as *mut crate::leanh::LeanObject,5511199417188169206 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__96: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__96_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__97_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [99, 111, 110, 102, 105, 103, 73, 116, 101, 109, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__97: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__97_value) as *mut crate::leanh::LeanObject;
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__98_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__98_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__98_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__98_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__98_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__98_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__98_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__97_value) as *mut crate::leanh::LeanObject,10138443044734372301 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__98: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__98_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__99_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [112, 111, 115, 67, 111, 110, 102, 105, 103, 73, 116, 101, 109, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__99: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__99_value) as *mut crate::leanh::LeanObject;
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__100_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__100_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__100_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__100_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__100_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__100_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__100_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__99_value) as *mut crate::leanh::LeanObject,9555431800314169832 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__100: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__100_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__101_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [43, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__101: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__101_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__102_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [122, 101, 116, 97, 68, 101, 108, 116, 97, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__102: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__102_value) as *mut crate::leanh::LeanObject;
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__103_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__103: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__104_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__102_value) as *mut crate::leanh::LeanObject,1066184292711288961 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__104: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__104_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__105_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [111, 110, 108, 121, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__105: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__105_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__106_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [115, 105, 109, 112, 76, 101, 109, 109, 97, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__106: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__106_value) as *mut crate::leanh::LeanObject;
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__107_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__107_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__107_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__107_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__107_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__107_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__107_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__106_value) as *mut crate::leanh::LeanObject,7383208167966365478 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__107: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__107_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__108_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [86, 101, 99, 116, 111, 114, 46, 115, 105, 122, 101, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__108: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__108_value) as *mut crate::leanh::LeanObject;
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__109_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__109: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__110_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [86, 101, 99, 116, 111, 114, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__110: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__110_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__111_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 105, 122, 101, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__111: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__111_value) as *mut crate::leanh::LeanObject;
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__112_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__110_value) as *mut crate::leanh::LeanObject,2228683986675333841 as *mut crate::leanh::LeanObject] };
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__112_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__112_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__111_value) as *mut crate::leanh::LeanObject,1999725115487179436 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__112: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__112_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__113_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__112_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__113: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__113_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__114_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__113_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__114: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__114_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__115_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 105, 109, 112, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__115: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__115_value) as *mut crate::leanh::LeanObject;
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__116_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__116_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__116_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__116_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__116_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__116_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__116_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__115_value) as *mut crate::leanh::LeanObject,12783917532758215986 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__116: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__116_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__117_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 114, 114, 97, 121, 46, 115, 105, 122, 101, 95, 109, 107, 83, 108, 105, 99, 101, 95, 114, 99, 111, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__117: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__117_value) as *mut crate::leanh::LeanObject;
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__118_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__118: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__119_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [65, 114, 114, 97, 121, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__119: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__119_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__120_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 105, 122, 101, 95, 109, 107, 83, 108, 105, 99, 101, 95, 114, 99, 111, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__120: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__120_value) as *mut crate::leanh::LeanObject;
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__121_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__119_value) as *mut crate::leanh::LeanObject,8749134177695247953 as *mut crate::leanh::LeanObject] };
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__121_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__121_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__120_value) as *mut crate::leanh::LeanObject,18249220446175315914 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__121: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__121_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__122_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__121_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__122: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__122_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__123_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__122_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__123: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__123_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__124_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [44, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__124: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__124_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__125_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 114, 114, 97, 121, 46, 115, 105, 122, 101, 95, 109, 107, 83, 108, 105, 99, 101, 95, 114, 99, 99, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__125: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__125_value) as *mut crate::leanh::LeanObject;
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__126_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__126: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__127_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 105, 122, 101, 95, 109, 107, 83, 108, 105, 99, 101, 95, 114, 99, 99, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__127: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__127_value) as *mut crate::leanh::LeanObject;
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__128_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__119_value) as *mut crate::leanh::LeanObject,8749134177695247953 as *mut crate::leanh::LeanObject] };
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__128_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__128_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__127_value) as *mut crate::leanh::LeanObject,16229177324683056447 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__128: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__128_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__129_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__128_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__129: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__129_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__130_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__129_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__130: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__130_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__131_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 114, 114, 97, 121, 46, 115, 105, 122, 101, 95, 109, 107, 83, 108, 105, 99, 101, 95, 114, 99, 105, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__131: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__131_value) as *mut crate::leanh::LeanObject;
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__132_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__132: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__133_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 105, 122, 101, 95, 109, 107, 83, 108, 105, 99, 101, 95, 114, 99, 105, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__133: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__133_value) as *mut crate::leanh::LeanObject;
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__134_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__119_value) as *mut crate::leanh::LeanObject,8749134177695247953 as *mut crate::leanh::LeanObject] };
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__134_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__134_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__133_value) as *mut crate::leanh::LeanObject,8089418641471207174 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__134: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__134_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__135_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__134_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__135: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__135_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__136_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__135_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__136: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__136_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__137_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 114, 114, 97, 121, 46, 115, 105, 122, 101, 95, 109, 107, 83, 108, 105, 99, 101, 95, 114, 111, 111, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__137: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__137_value) as *mut crate::leanh::LeanObject;
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__138_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__138: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__139_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 105, 122, 101, 95, 109, 107, 83, 108, 105, 99, 101, 95, 114, 111, 111, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__139: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__139_value) as *mut crate::leanh::LeanObject;
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__140_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__119_value) as *mut crate::leanh::LeanObject,8749134177695247953 as *mut crate::leanh::LeanObject] };
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__140_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__140_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__139_value) as *mut crate::leanh::LeanObject,826823846374397552 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__140: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__140_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__141_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__140_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__141: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__141_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__142_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__141_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__142: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__142_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__143_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 114, 114, 97, 121, 46, 115, 105, 122, 101, 95, 109, 107, 83, 108, 105, 99, 101, 95, 114, 111, 99, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__143: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__143_value) as *mut crate::leanh::LeanObject;
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__144_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__144: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__145_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 105, 122, 101, 95, 109, 107, 83, 108, 105, 99, 101, 95, 114, 111, 99, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__145: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__145_value) as *mut crate::leanh::LeanObject;
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__146_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__119_value) as *mut crate::leanh::LeanObject,8749134177695247953 as *mut crate::leanh::LeanObject] };
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__146_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__146_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__145_value) as *mut crate::leanh::LeanObject,1943828791449064610 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__146: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__146_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__147_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__146_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__147: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__147_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__148_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__147_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__148: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__148_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__149_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 114, 114, 97, 121, 46, 115, 105, 122, 101, 95, 109, 107, 83, 108, 105, 99, 101, 95, 114, 111, 105, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__149: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__149_value) as *mut crate::leanh::LeanObject;
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__150_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__150: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__151_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 105, 122, 101, 95, 109, 107, 83, 108, 105, 99, 101, 95, 114, 111, 105, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__151: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__151_value) as *mut crate::leanh::LeanObject;
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__152_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__119_value) as *mut crate::leanh::LeanObject,8749134177695247953 as *mut crate::leanh::LeanObject] };
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__152_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__152_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__151_value) as *mut crate::leanh::LeanObject,9287060749115205262 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__152: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__152_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__153_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__152_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__153: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__153_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__154_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__153_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__154: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__154_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__155_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 114, 114, 97, 121, 46, 115, 105, 122, 101, 95, 109, 107, 83, 108, 105, 99, 101, 95, 114, 105, 111, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__155: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__155_value) as *mut crate::leanh::LeanObject;
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__156_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__156: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__157_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 105, 122, 101, 95, 109, 107, 83, 108, 105, 99, 101, 95, 114, 105, 111, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__157: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__157_value) as *mut crate::leanh::LeanObject;
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__158_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__119_value) as *mut crate::leanh::LeanObject,8749134177695247953 as *mut crate::leanh::LeanObject] };
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__158_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__158_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__157_value) as *mut crate::leanh::LeanObject,2317446182483457163 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__158: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__158_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__159_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__158_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__159: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__159_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__160_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__159_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__160: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__160_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__161_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 114, 114, 97, 121, 46, 115, 105, 122, 101, 95, 109, 107, 83, 108, 105, 99, 101, 95, 114, 105, 99, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__161: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__161_value) as *mut crate::leanh::LeanObject;
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__162_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__162: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__163_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 105, 122, 101, 95, 109, 107, 83, 108, 105, 99, 101, 95, 114, 105, 99, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__163: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__163_value) as *mut crate::leanh::LeanObject;
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__164_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__119_value) as *mut crate::leanh::LeanObject,8749134177695247953 as *mut crate::leanh::LeanObject] };
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__164_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__164_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__163_value) as *mut crate::leanh::LeanObject,12594725173538112283 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__164: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__164_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__165_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__164_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__165: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__165_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__166_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__165_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__166: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__166_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__167_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 114, 114, 97, 121, 46, 115, 105, 122, 101, 95, 109, 107, 83, 108, 105, 99, 101, 95, 114, 105, 105, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__167: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__167_value) as *mut crate::leanh::LeanObject;
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__168_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__168: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__169_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 105, 122, 101, 95, 109, 107, 83, 108, 105, 99, 101, 95, 114, 105, 105, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__169: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__169_value) as *mut crate::leanh::LeanObject;
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__170_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__119_value) as *mut crate::leanh::LeanObject,8749134177695247953 as *mut crate::leanh::LeanObject] };
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__170_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__170_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__169_value) as *mut crate::leanh::LeanObject,1021830332027298700 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__170: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__170_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__171_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__170_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__171: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__171_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__172_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__171_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__172: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__172_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__173_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [111, 109, 101, 103, 97, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__173: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__173_value) as *mut crate::leanh::LeanObject;
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__174_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__174_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__174_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__174_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__174_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__174_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__174_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__173_value) as *mut crate::leanh::LeanObject,14893461734720614794 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__174: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__174_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__175_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [100, 111, 110, 101, 0]};
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__175: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__175_value) as *mut crate::leanh::LeanObject;
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__176_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__176_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__176_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__176_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__176_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__176_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__176_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__175_value) as *mut crate::leanh::LeanObject,8876691400619696497 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__176: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__176_value) as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__24()
-> *mut crate::leanh::LeanObject {
    let mut v___x_777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_777_ = l_Array_mkArray0(crate::leanh::lean_box(0));
    return v___x_777_;
}
pub unsafe fn _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__31()
-> *mut crate::leanh::LeanObject {
    let mut v___x_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_792_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__30;
    v___x_793_ = l_String_toRawSubstring_x27(v___x_792_);
    return v___x_793_;
}
pub unsafe fn _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__46()
-> *mut crate::leanh::LeanObject {
    let mut v___x_823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_823_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__45;
    v___x_824_ = l_String_toRawSubstring_x27(v___x_823_);
    return v___x_824_;
}
pub unsafe fn _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__52()
-> *mut crate::leanh::LeanObject {
    let mut v___x_837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_837_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__51;
    v___x_838_ = l_String_toRawSubstring_x27(v___x_837_);
    return v___x_838_;
}
pub unsafe fn _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__58()
-> *mut crate::leanh::LeanObject {
    let mut v___x_851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_851_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__57;
    v___x_852_ = l_String_toRawSubstring_x27(v___x_851_);
    return v___x_852_;
}
pub unsafe fn _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__64()
-> *mut crate::leanh::LeanObject {
    let mut v___x_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_865_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__63;
    v___x_866_ = l_String_toRawSubstring_x27(v___x_865_);
    return v___x_866_;
}
pub unsafe fn _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__70()
-> *mut crate::leanh::LeanObject {
    let mut v___x_879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_879_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__69;
    v___x_880_ = l_String_toRawSubstring_x27(v___x_879_);
    return v___x_880_;
}
pub unsafe fn _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__76()
-> *mut crate::leanh::LeanObject {
    let mut v___x_893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_893_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__75;
    v___x_894_ = l_String_toRawSubstring_x27(v___x_893_);
    return v___x_894_;
}
pub unsafe fn _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__82()
-> *mut crate::leanh::LeanObject {
    let mut v___x_907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_907_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__81;
    v___x_908_ = l_String_toRawSubstring_x27(v___x_907_);
    return v___x_908_;
}
pub unsafe fn _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__88()
-> *mut crate::leanh::LeanObject {
    let mut v___x_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_921_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__87;
    v___x_922_ = l_String_toRawSubstring_x27(v___x_921_);
    return v___x_922_;
}
pub unsafe fn _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__103()
-> *mut crate::leanh::LeanObject {
    let mut v___x_960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_960_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__102;
    v___x_961_ = l_String_toRawSubstring_x27(v___x_960_);
    return v___x_961_;
}
pub unsafe fn _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__109()
-> *mut crate::leanh::LeanObject {
    let mut v___x_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_972_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__108;
    v___x_973_ = l_String_toRawSubstring_x27(v___x_972_);
    return v___x_973_;
}
pub unsafe fn _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__118()
-> *mut crate::leanh::LeanObject {
    let mut v___x_992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_992_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__117;
    v___x_993_ = l_String_toRawSubstring_x27(v___x_992_);
    return v___x_993_;
}
pub unsafe fn _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__126()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1007_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__125;
    v___x_1008_ = l_String_toRawSubstring_x27(v___x_1007_);
    return v___x_1008_;
}
pub unsafe fn _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__132()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1020_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__131;
    v___x_1021_ = l_String_toRawSubstring_x27(v___x_1020_);
    return v___x_1021_;
}
pub unsafe fn _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__138()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1033_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__137;
    v___x_1034_ = l_String_toRawSubstring_x27(v___x_1033_);
    return v___x_1034_;
}
pub unsafe fn _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__144()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1046_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__143;
    v___x_1047_ = l_String_toRawSubstring_x27(v___x_1046_);
    return v___x_1047_;
}
pub unsafe fn _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__150()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1059_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__149;
    v___x_1060_ = l_String_toRawSubstring_x27(v___x_1059_);
    return v___x_1060_;
}
pub unsafe fn _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__156()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1072_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__155;
    v___x_1073_ = l_String_toRawSubstring_x27(v___x_1072_);
    return v___x_1073_;
}
pub unsafe fn _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__162()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1085_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__161;
    v___x_1086_ = l_String_toRawSubstring_x27(v___x_1085_);
    return v___x_1086_;
}
pub unsafe fn _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__168()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1098_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__167;
    v___x_1099_ = l_String_toRawSubstring_x27(v___x_1098_);
    return v___x_1099_;
}
pub unsafe fn l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1(
    mut v_x_1122_: *mut crate::leanh::LeanObject,
    mut v_a_1123_: *mut crate::leanh::LeanObject,
    mut v_a_1124_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1126_: u8 = 0;
    v___x_1125_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__1;
    v___x_1126_ = l_Lean_Syntax_isOfKind(v_x_1122_, v___x_1125_);
    if v___x_1126_ == 0 {
        let mut v___x_1127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1127_ = crate::leanh::lean_box(1);
        v___x_1128_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1128_, 0, v___x_1127_);
        crate::leanh::lean_ctor_set(v___x_1128_, 1, v_a_1124_);
        return v___x_1128_;
    } else {
        let mut v_quotContext_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_1130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1132_: u8 = 0;
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
        let mut v___x_1244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
        let mut v___x_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
        v_quotContext_1129_ = crate::leanh::lean_ctor_get(v_a_1123_, 1);
        v_currMacroScope_1130_ = crate::leanh::lean_ctor_get(v_a_1123_, 2);
        v_ref_1131_ = crate::leanh::lean_ctor_get(v_a_1123_, 5);
        v___x_1132_ = 0;
        v___x_1133_ = l_Lean_SourceInfo_fromRef(v_ref_1131_, v___x_1132_);
        v___x_1134_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__5;
        v___x_1135_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__6;
        crate::leanh::lean_inc_n(v___x_1133_, 152);
        v___x_1136_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1136_, 0, v___x_1133_);
        crate::leanh::lean_ctor_set(v___x_1136_, 1, v___x_1134_);
        v___x_1137_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__8;
        v___x_1138_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__10;
        v___x_1139_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__11;
        v___x_1140_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1140_, 0, v___x_1133_);
        crate::leanh::lean_ctor_set(v___x_1140_, 1, v___x_1139_);
        v___x_1141_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__13;
        v___x_1142_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15;
        v___x_1143_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17;
        v___x_1144_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__18;
        v___x_1145_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1145_, 0, v___x_1133_);
        crate::leanh::lean_ctor_set(v___x_1145_, 1, v___x_1144_);
        v___x_1146_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__20;
        v___x_1147_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__21;
        v___x_1148_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1148_, 0, v___x_1133_);
        crate::leanh::lean_ctor_set(v___x_1148_, 1, v___x_1147_);
        v___x_1149_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__23;
        v___x_1150_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__24), core::ptr::addr_of_mut!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__24_once), _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__24);
        v___x_1151_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1151_, 0, v___x_1133_);
        crate::leanh::lean_ctor_set(v___x_1151_, 1, v___x_1137_);
        crate::leanh::lean_ctor_set(v___x_1151_, 2, v___x_1150_);
        crate::leanh::lean_inc_ref_n(v___x_1151_, 43);
        v___x_1152_ = l_Lean_Syntax_node1(v___x_1133_, v___x_1149_, v___x_1151_);
        v___x_1153_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__26;
        v___x_1154_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__27;
        v___x_1155_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1155_, 0, v___x_1133_);
        crate::leanh::lean_ctor_set(v___x_1155_, 1, v___x_1154_);
        v___x_1156_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__29;
        v___x_1157_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__31), core::ptr::addr_of_mut!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__31_once), _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__31);
        v___x_1158_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__35;
        crate::leanh::lean_inc_n(v_currMacroScope_1130_, 20);
        crate::leanh::lean_inc_n(v_quotContext_1129_, 20);
        v___x_1159_ =
            l_Lean_addMacroScope(v_quotContext_1129_, v___x_1158_, v_currMacroScope_1130_);
        v___x_1160_ = crate::leanh::lean_box(0);
        v___x_1161_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__37;
        v___x_1162_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1162_, 0, v___x_1133_);
        crate::leanh::lean_ctor_set(v___x_1162_, 1, v___x_1157_);
        crate::leanh::lean_ctor_set(v___x_1162_, 2, v___x_1159_);
        crate::leanh::lean_ctor_set(v___x_1162_, 3, v___x_1161_);
        v___x_1163_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1156_, v___x_1151_, v___x_1162_);
        v___x_1164_ = l_Lean_Syntax_node1(v___x_1133_, v___x_1137_, v___x_1163_);
        v___x_1165_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__38;
        v___x_1166_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1166_, 0, v___x_1133_);
        crate::leanh::lean_ctor_set(v___x_1166_, 1, v___x_1165_);
        crate::leanh::lean_inc_ref_n(v___x_1166_, 10);
        crate::leanh::lean_inc_ref_n(v___x_1155_, 10);
        v___x_1167_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1153_,
            v___x_1155_,
            v___x_1164_,
            v___x_1166_,
        );
        v___x_1168_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__40;
        v___x_1169_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__41;
        v___x_1170_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1170_, 0, v___x_1133_);
        crate::leanh::lean_ctor_set(v___x_1170_, 1, v___x_1169_);
        v___x_1171_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__43;
        v___x_1172_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__44;
        v___x_1173_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1173_, 0, v___x_1133_);
        crate::leanh::lean_ctor_set(v___x_1173_, 1, v___x_1172_);
        v___x_1174_ = l_Lean_Syntax_node1(v___x_1133_, v___x_1171_, v___x_1173_);
        v___x_1175_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1168_, v___x_1170_, v___x_1174_);
        v___x_1176_ = l_Lean_Syntax_node1(v___x_1133_, v___x_1137_, v___x_1175_);
        crate::leanh::lean_inc_n(v___x_1176_, 9);
        crate::leanh::lean_inc_n(v___x_1152_, 10);
        crate::leanh::lean_inc_ref_n(v___x_1148_, 8);
        v___x_1177_ = l_Lean_Syntax_node4(
            v___x_1133_,
            v___x_1146_,
            v___x_1148_,
            v___x_1152_,
            v___x_1167_,
            v___x_1176_,
        );
        v___x_1178_ = l_Lean_Syntax_node1(v___x_1133_, v___x_1137_, v___x_1177_);
        v___x_1179_ = l_Lean_Syntax_node1(v___x_1133_, v___x_1142_, v___x_1178_);
        v___x_1180_ = l_Lean_Syntax_node1(v___x_1133_, v___x_1141_, v___x_1179_);
        crate::leanh::lean_inc_ref_n(v___x_1145_, 10);
        v___x_1181_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1143_, v___x_1145_, v___x_1180_);
        v___x_1182_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__46), core::ptr::addr_of_mut!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__46_once), _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__46);
        v___x_1183_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__48;
        v___x_1184_ =
            l_Lean_addMacroScope(v_quotContext_1129_, v___x_1183_, v_currMacroScope_1130_);
        v___x_1185_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__50;
        v___x_1186_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1186_, 0, v___x_1133_);
        crate::leanh::lean_ctor_set(v___x_1186_, 1, v___x_1182_);
        crate::leanh::lean_ctor_set(v___x_1186_, 2, v___x_1184_);
        crate::leanh::lean_ctor_set(v___x_1186_, 3, v___x_1185_);
        v___x_1187_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1156_, v___x_1151_, v___x_1186_);
        v___x_1188_ = l_Lean_Syntax_node1(v___x_1133_, v___x_1137_, v___x_1187_);
        v___x_1189_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1153_,
            v___x_1155_,
            v___x_1188_,
            v___x_1166_,
        );
        v___x_1190_ = l_Lean_Syntax_node4(
            v___x_1133_,
            v___x_1146_,
            v___x_1148_,
            v___x_1152_,
            v___x_1189_,
            v___x_1176_,
        );
        v___x_1191_ = l_Lean_Syntax_node1(v___x_1133_, v___x_1137_, v___x_1190_);
        v___x_1192_ = l_Lean_Syntax_node1(v___x_1133_, v___x_1142_, v___x_1191_);
        v___x_1193_ = l_Lean_Syntax_node1(v___x_1133_, v___x_1141_, v___x_1192_);
        v___x_1194_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1143_, v___x_1145_, v___x_1193_);
        v___x_1195_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__52), core::ptr::addr_of_mut!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__52_once), _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__52);
        v___x_1196_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__54;
        v___x_1197_ =
            l_Lean_addMacroScope(v_quotContext_1129_, v___x_1196_, v_currMacroScope_1130_);
        v___x_1198_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__56;
        v___x_1199_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1199_, 0, v___x_1133_);
        crate::leanh::lean_ctor_set(v___x_1199_, 1, v___x_1195_);
        crate::leanh::lean_ctor_set(v___x_1199_, 2, v___x_1197_);
        crate::leanh::lean_ctor_set(v___x_1199_, 3, v___x_1198_);
        v___x_1200_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1156_, v___x_1151_, v___x_1199_);
        v___x_1201_ = l_Lean_Syntax_node1(v___x_1133_, v___x_1137_, v___x_1200_);
        v___x_1202_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1153_,
            v___x_1155_,
            v___x_1201_,
            v___x_1166_,
        );
        v___x_1203_ = l_Lean_Syntax_node4(
            v___x_1133_,
            v___x_1146_,
            v___x_1148_,
            v___x_1152_,
            v___x_1202_,
            v___x_1176_,
        );
        v___x_1204_ = l_Lean_Syntax_node1(v___x_1133_, v___x_1137_, v___x_1203_);
        v___x_1205_ = l_Lean_Syntax_node1(v___x_1133_, v___x_1142_, v___x_1204_);
        v___x_1206_ = l_Lean_Syntax_node1(v___x_1133_, v___x_1141_, v___x_1205_);
        v___x_1207_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1143_, v___x_1145_, v___x_1206_);
        v___x_1208_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__58), core::ptr::addr_of_mut!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__58_once), _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__58);
        v___x_1209_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__60;
        v___x_1210_ =
            l_Lean_addMacroScope(v_quotContext_1129_, v___x_1209_, v_currMacroScope_1130_);
        v___x_1211_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__62;
        v___x_1212_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1212_, 0, v___x_1133_);
        crate::leanh::lean_ctor_set(v___x_1212_, 1, v___x_1208_);
        crate::leanh::lean_ctor_set(v___x_1212_, 2, v___x_1210_);
        crate::leanh::lean_ctor_set(v___x_1212_, 3, v___x_1211_);
        v___x_1213_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1156_, v___x_1151_, v___x_1212_);
        v___x_1214_ = l_Lean_Syntax_node1(v___x_1133_, v___x_1137_, v___x_1213_);
        v___x_1215_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1153_,
            v___x_1155_,
            v___x_1214_,
            v___x_1166_,
        );
        v___x_1216_ = l_Lean_Syntax_node4(
            v___x_1133_,
            v___x_1146_,
            v___x_1148_,
            v___x_1152_,
            v___x_1215_,
            v___x_1176_,
        );
        v___x_1217_ = l_Lean_Syntax_node1(v___x_1133_, v___x_1137_, v___x_1216_);
        v___x_1218_ = l_Lean_Syntax_node1(v___x_1133_, v___x_1142_, v___x_1217_);
        v___x_1219_ = l_Lean_Syntax_node1(v___x_1133_, v___x_1141_, v___x_1218_);
        v___x_1220_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1143_, v___x_1145_, v___x_1219_);
        v___x_1221_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__64), core::ptr::addr_of_mut!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__64_once), _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__64);
        v___x_1222_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__66;
        v___x_1223_ =
            l_Lean_addMacroScope(v_quotContext_1129_, v___x_1222_, v_currMacroScope_1130_);
        v___x_1224_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__68;
        v___x_1225_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1225_, 0, v___x_1133_);
        crate::leanh::lean_ctor_set(v___x_1225_, 1, v___x_1221_);
        crate::leanh::lean_ctor_set(v___x_1225_, 2, v___x_1223_);
        crate::leanh::lean_ctor_set(v___x_1225_, 3, v___x_1224_);
        v___x_1226_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1156_, v___x_1151_, v___x_1225_);
        v___x_1227_ = l_Lean_Syntax_node1(v___x_1133_, v___x_1137_, v___x_1226_);
        v___x_1228_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1153_,
            v___x_1155_,
            v___x_1227_,
            v___x_1166_,
        );
        v___x_1229_ = l_Lean_Syntax_node4(
            v___x_1133_,
            v___x_1146_,
            v___x_1148_,
            v___x_1152_,
            v___x_1228_,
            v___x_1176_,
        );
        v___x_1230_ = l_Lean_Syntax_node1(v___x_1133_, v___x_1137_, v___x_1229_);
        v___x_1231_ = l_Lean_Syntax_node1(v___x_1133_, v___x_1142_, v___x_1230_);
        v___x_1232_ = l_Lean_Syntax_node1(v___x_1133_, v___x_1141_, v___x_1231_);
        v___x_1233_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1143_, v___x_1145_, v___x_1232_);
        v___x_1234_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__70), core::ptr::addr_of_mut!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__70_once), _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__70);
        v___x_1235_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__72;
        v___x_1236_ =
            l_Lean_addMacroScope(v_quotContext_1129_, v___x_1235_, v_currMacroScope_1130_);
        v___x_1237_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__74;
        v___x_1238_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1238_, 0, v___x_1133_);
        crate::leanh::lean_ctor_set(v___x_1238_, 1, v___x_1234_);
        crate::leanh::lean_ctor_set(v___x_1238_, 2, v___x_1236_);
        crate::leanh::lean_ctor_set(v___x_1238_, 3, v___x_1237_);
        v___x_1239_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1156_, v___x_1151_, v___x_1238_);
        v___x_1240_ = l_Lean_Syntax_node1(v___x_1133_, v___x_1137_, v___x_1239_);
        v___x_1241_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1153_,
            v___x_1155_,
            v___x_1240_,
            v___x_1166_,
        );
        v___x_1242_ = l_Lean_Syntax_node4(
            v___x_1133_,
            v___x_1146_,
            v___x_1148_,
            v___x_1152_,
            v___x_1241_,
            v___x_1176_,
        );
        v___x_1243_ = l_Lean_Syntax_node1(v___x_1133_, v___x_1137_, v___x_1242_);
        v___x_1244_ = l_Lean_Syntax_node1(v___x_1133_, v___x_1142_, v___x_1243_);
        v___x_1245_ = l_Lean_Syntax_node1(v___x_1133_, v___x_1141_, v___x_1244_);
        v___x_1246_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1143_, v___x_1145_, v___x_1245_);
        v___x_1247_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__76), core::ptr::addr_of_mut!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__76_once), _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__76);
        v___x_1248_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__78;
        v___x_1249_ =
            l_Lean_addMacroScope(v_quotContext_1129_, v___x_1248_, v_currMacroScope_1130_);
        v___x_1250_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__80;
        v___x_1251_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1251_, 0, v___x_1133_);
        crate::leanh::lean_ctor_set(v___x_1251_, 1, v___x_1247_);
        crate::leanh::lean_ctor_set(v___x_1251_, 2, v___x_1249_);
        crate::leanh::lean_ctor_set(v___x_1251_, 3, v___x_1250_);
        v___x_1252_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1156_, v___x_1151_, v___x_1251_);
        v___x_1253_ = l_Lean_Syntax_node1(v___x_1133_, v___x_1137_, v___x_1252_);
        v___x_1254_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1153_,
            v___x_1155_,
            v___x_1253_,
            v___x_1166_,
        );
        v___x_1255_ = l_Lean_Syntax_node4(
            v___x_1133_,
            v___x_1146_,
            v___x_1148_,
            v___x_1152_,
            v___x_1254_,
            v___x_1176_,
        );
        v___x_1256_ = l_Lean_Syntax_node1(v___x_1133_, v___x_1137_, v___x_1255_);
        v___x_1257_ = l_Lean_Syntax_node1(v___x_1133_, v___x_1142_, v___x_1256_);
        v___x_1258_ = l_Lean_Syntax_node1(v___x_1133_, v___x_1141_, v___x_1257_);
        v___x_1259_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1143_, v___x_1145_, v___x_1258_);
        v___x_1260_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__82), core::ptr::addr_of_mut!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__82_once), _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__82);
        v___x_1261_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__84;
        v___x_1262_ =
            l_Lean_addMacroScope(v_quotContext_1129_, v___x_1261_, v_currMacroScope_1130_);
        v___x_1263_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__86;
        v___x_1264_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1264_, 0, v___x_1133_);
        crate::leanh::lean_ctor_set(v___x_1264_, 1, v___x_1260_);
        crate::leanh::lean_ctor_set(v___x_1264_, 2, v___x_1262_);
        crate::leanh::lean_ctor_set(v___x_1264_, 3, v___x_1263_);
        v___x_1265_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1156_, v___x_1151_, v___x_1264_);
        v___x_1266_ = l_Lean_Syntax_node1(v___x_1133_, v___x_1137_, v___x_1265_);
        v___x_1267_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1153_,
            v___x_1155_,
            v___x_1266_,
            v___x_1166_,
        );
        v___x_1268_ = l_Lean_Syntax_node4(
            v___x_1133_,
            v___x_1146_,
            v___x_1148_,
            v___x_1152_,
            v___x_1267_,
            v___x_1176_,
        );
        v___x_1269_ = l_Lean_Syntax_node1(v___x_1133_, v___x_1137_, v___x_1268_);
        v___x_1270_ = l_Lean_Syntax_node1(v___x_1133_, v___x_1142_, v___x_1269_);
        v___x_1271_ = l_Lean_Syntax_node1(v___x_1133_, v___x_1141_, v___x_1270_);
        v___x_1272_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1143_, v___x_1145_, v___x_1271_);
        v___x_1273_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__88), core::ptr::addr_of_mut!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__88_once), _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__88);
        v___x_1274_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__90;
        v___x_1275_ =
            l_Lean_addMacroScope(v_quotContext_1129_, v___x_1274_, v_currMacroScope_1130_);
        v___x_1276_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__94;
        v___x_1277_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1277_, 0, v___x_1133_);
        crate::leanh::lean_ctor_set(v___x_1277_, 1, v___x_1273_);
        crate::leanh::lean_ctor_set(v___x_1277_, 2, v___x_1275_);
        crate::leanh::lean_ctor_set(v___x_1277_, 3, v___x_1276_);
        v___x_1278_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1156_, v___x_1151_, v___x_1277_);
        v___x_1279_ = l_Lean_Syntax_node1(v___x_1133_, v___x_1137_, v___x_1278_);
        v___x_1280_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1153_,
            v___x_1155_,
            v___x_1279_,
            v___x_1166_,
        );
        v___x_1281_ = l_Lean_Syntax_node4(
            v___x_1133_,
            v___x_1146_,
            v___x_1148_,
            v___x_1152_,
            v___x_1280_,
            v___x_1176_,
        );
        v___x_1282_ = l_Lean_Syntax_node1(v___x_1133_, v___x_1137_, v___x_1281_);
        v___x_1283_ = l_Lean_Syntax_node1(v___x_1133_, v___x_1142_, v___x_1282_);
        v___x_1284_ = l_Lean_Syntax_node1(v___x_1133_, v___x_1141_, v___x_1283_);
        v___x_1285_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1143_, v___x_1145_, v___x_1284_);
        v___x_1286_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__95;
        v___x_1287_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__96;
        v___x_1288_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1288_, 0, v___x_1133_);
        crate::leanh::lean_ctor_set(v___x_1288_, 1, v___x_1286_);
        v___x_1289_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__98;
        v___x_1290_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__100;
        v___x_1291_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__101;
        v___x_1292_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1292_, 0, v___x_1133_);
        crate::leanh::lean_ctor_set(v___x_1292_, 1, v___x_1291_);
        v___x_1293_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__103), core::ptr::addr_of_mut!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__103_once), _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__103);
        v___x_1294_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__104;
        v___x_1295_ =
            l_Lean_addMacroScope(v_quotContext_1129_, v___x_1294_, v_currMacroScope_1130_);
        v___x_1296_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1296_, 0, v___x_1133_);
        crate::leanh::lean_ctor_set(v___x_1296_, 1, v___x_1293_);
        crate::leanh::lean_ctor_set(v___x_1296_, 2, v___x_1295_);
        crate::leanh::lean_ctor_set(v___x_1296_, 3, v___x_1160_);
        v___x_1297_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1290_, v___x_1292_, v___x_1296_);
        v___x_1298_ = l_Lean_Syntax_node1(v___x_1133_, v___x_1289_, v___x_1297_);
        v___x_1299_ = l_Lean_Syntax_node1(v___x_1133_, v___x_1137_, v___x_1298_);
        v___x_1300_ = l_Lean_Syntax_node1(v___x_1133_, v___x_1149_, v___x_1299_);
        v___x_1301_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__105;
        v___x_1302_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1302_, 0, v___x_1133_);
        crate::leanh::lean_ctor_set(v___x_1302_, 1, v___x_1301_);
        v___x_1303_ = l_Lean_Syntax_node1(v___x_1133_, v___x_1137_, v___x_1302_);
        v___x_1304_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__107;
        v___x_1305_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__109), core::ptr::addr_of_mut!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__109_once), _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__109);
        v___x_1306_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__112;
        v___x_1307_ =
            l_Lean_addMacroScope(v_quotContext_1129_, v___x_1306_, v_currMacroScope_1130_);
        v___x_1308_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__114;
        v___x_1309_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1309_, 0, v___x_1133_);
        crate::leanh::lean_ctor_set(v___x_1309_, 1, v___x_1305_);
        crate::leanh::lean_ctor_set(v___x_1309_, 2, v___x_1307_);
        crate::leanh::lean_ctor_set(v___x_1309_, 3, v___x_1308_);
        v___x_1310_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1304_,
            v___x_1151_,
            v___x_1151_,
            v___x_1309_,
        );
        v___x_1311_ = l_Lean_Syntax_node1(v___x_1133_, v___x_1137_, v___x_1310_);
        v___x_1312_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1137_,
            v___x_1155_,
            v___x_1311_,
            v___x_1166_,
        );
        crate::leanh::lean_inc(v___x_1303_);
        v___x_1313_ = l_Lean_Syntax_node6(
            v___x_1133_,
            v___x_1287_,
            v___x_1288_,
            v___x_1300_,
            v___x_1151_,
            v___x_1303_,
            v___x_1312_,
            v___x_1176_,
        );
        v___x_1314_ = l_Lean_Syntax_node1(v___x_1133_, v___x_1137_, v___x_1313_);
        v___x_1315_ = l_Lean_Syntax_node1(v___x_1133_, v___x_1142_, v___x_1314_);
        v___x_1316_ = l_Lean_Syntax_node1(v___x_1133_, v___x_1141_, v___x_1315_);
        v___x_1317_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1143_, v___x_1145_, v___x_1316_);
        v___x_1318_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__115;
        v___x_1319_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__116;
        v___x_1320_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1320_, 0, v___x_1133_);
        crate::leanh::lean_ctor_set(v___x_1320_, 1, v___x_1318_);
        v___x_1321_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__118), core::ptr::addr_of_mut!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__118_once), _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__118);
        v___x_1322_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__121;
        v___x_1323_ =
            l_Lean_addMacroScope(v_quotContext_1129_, v___x_1322_, v_currMacroScope_1130_);
        v___x_1324_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__123;
        v___x_1325_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1325_, 0, v___x_1133_);
        crate::leanh::lean_ctor_set(v___x_1325_, 1, v___x_1321_);
        crate::leanh::lean_ctor_set(v___x_1325_, 2, v___x_1323_);
        crate::leanh::lean_ctor_set(v___x_1325_, 3, v___x_1324_);
        v___x_1326_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1304_,
            v___x_1151_,
            v___x_1151_,
            v___x_1325_,
        );
        v___x_1327_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__124;
        v___x_1328_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1328_, 0, v___x_1133_);
        crate::leanh::lean_ctor_set(v___x_1328_, 1, v___x_1327_);
        v___x_1329_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__126), core::ptr::addr_of_mut!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__126_once), _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__126);
        v___x_1330_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__128;
        v___x_1331_ =
            l_Lean_addMacroScope(v_quotContext_1129_, v___x_1330_, v_currMacroScope_1130_);
        v___x_1332_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__130;
        v___x_1333_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1333_, 0, v___x_1133_);
        crate::leanh::lean_ctor_set(v___x_1333_, 1, v___x_1329_);
        crate::leanh::lean_ctor_set(v___x_1333_, 2, v___x_1331_);
        crate::leanh::lean_ctor_set(v___x_1333_, 3, v___x_1332_);
        v___x_1334_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1304_,
            v___x_1151_,
            v___x_1151_,
            v___x_1333_,
        );
        v___x_1335_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__132), core::ptr::addr_of_mut!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__132_once), _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__132);
        v___x_1336_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__134;
        v___x_1337_ =
            l_Lean_addMacroScope(v_quotContext_1129_, v___x_1336_, v_currMacroScope_1130_);
        v___x_1338_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__136;
        v___x_1339_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1339_, 0, v___x_1133_);
        crate::leanh::lean_ctor_set(v___x_1339_, 1, v___x_1335_);
        crate::leanh::lean_ctor_set(v___x_1339_, 2, v___x_1337_);
        crate::leanh::lean_ctor_set(v___x_1339_, 3, v___x_1338_);
        v___x_1340_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1304_,
            v___x_1151_,
            v___x_1151_,
            v___x_1339_,
        );
        v___x_1341_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__138), core::ptr::addr_of_mut!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__138_once), _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__138);
        v___x_1342_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__140;
        v___x_1343_ =
            l_Lean_addMacroScope(v_quotContext_1129_, v___x_1342_, v_currMacroScope_1130_);
        v___x_1344_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__142;
        v___x_1345_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1345_, 0, v___x_1133_);
        crate::leanh::lean_ctor_set(v___x_1345_, 1, v___x_1341_);
        crate::leanh::lean_ctor_set(v___x_1345_, 2, v___x_1343_);
        crate::leanh::lean_ctor_set(v___x_1345_, 3, v___x_1344_);
        v___x_1346_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1304_,
            v___x_1151_,
            v___x_1151_,
            v___x_1345_,
        );
        v___x_1347_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__144), core::ptr::addr_of_mut!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__144_once), _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__144);
        v___x_1348_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__146;
        v___x_1349_ =
            l_Lean_addMacroScope(v_quotContext_1129_, v___x_1348_, v_currMacroScope_1130_);
        v___x_1350_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__148;
        v___x_1351_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1351_, 0, v___x_1133_);
        crate::leanh::lean_ctor_set(v___x_1351_, 1, v___x_1347_);
        crate::leanh::lean_ctor_set(v___x_1351_, 2, v___x_1349_);
        crate::leanh::lean_ctor_set(v___x_1351_, 3, v___x_1350_);
        v___x_1352_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1304_,
            v___x_1151_,
            v___x_1151_,
            v___x_1351_,
        );
        v___x_1353_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__150), core::ptr::addr_of_mut!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__150_once), _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__150);
        v___x_1354_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__152;
        v___x_1355_ =
            l_Lean_addMacroScope(v_quotContext_1129_, v___x_1354_, v_currMacroScope_1130_);
        v___x_1356_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__154;
        v___x_1357_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1357_, 0, v___x_1133_);
        crate::leanh::lean_ctor_set(v___x_1357_, 1, v___x_1353_);
        crate::leanh::lean_ctor_set(v___x_1357_, 2, v___x_1355_);
        crate::leanh::lean_ctor_set(v___x_1357_, 3, v___x_1356_);
        v___x_1358_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1304_,
            v___x_1151_,
            v___x_1151_,
            v___x_1357_,
        );
        v___x_1359_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__156), core::ptr::addr_of_mut!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__156_once), _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__156);
        v___x_1360_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__158;
        v___x_1361_ =
            l_Lean_addMacroScope(v_quotContext_1129_, v___x_1360_, v_currMacroScope_1130_);
        v___x_1362_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__160;
        v___x_1363_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1363_, 0, v___x_1133_);
        crate::leanh::lean_ctor_set(v___x_1363_, 1, v___x_1359_);
        crate::leanh::lean_ctor_set(v___x_1363_, 2, v___x_1361_);
        crate::leanh::lean_ctor_set(v___x_1363_, 3, v___x_1362_);
        v___x_1364_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1304_,
            v___x_1151_,
            v___x_1151_,
            v___x_1363_,
        );
        v___x_1365_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__162), core::ptr::addr_of_mut!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__162_once), _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__162);
        v___x_1366_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__164;
        v___x_1367_ =
            l_Lean_addMacroScope(v_quotContext_1129_, v___x_1366_, v_currMacroScope_1130_);
        v___x_1368_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__166;
        v___x_1369_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1369_, 0, v___x_1133_);
        crate::leanh::lean_ctor_set(v___x_1369_, 1, v___x_1365_);
        crate::leanh::lean_ctor_set(v___x_1369_, 2, v___x_1367_);
        crate::leanh::lean_ctor_set(v___x_1369_, 3, v___x_1368_);
        v___x_1370_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1304_,
            v___x_1151_,
            v___x_1151_,
            v___x_1369_,
        );
        v___x_1371_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__168), core::ptr::addr_of_mut!(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__168_once), _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__168);
        v___x_1372_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__170;
        v___x_1373_ =
            l_Lean_addMacroScope(v_quotContext_1129_, v___x_1372_, v_currMacroScope_1130_);
        v___x_1374_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__172;
        v___x_1375_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1375_, 0, v___x_1133_);
        crate::leanh::lean_ctor_set(v___x_1375_, 1, v___x_1371_);
        crate::leanh::lean_ctor_set(v___x_1375_, 2, v___x_1373_);
        crate::leanh::lean_ctor_set(v___x_1375_, 3, v___x_1374_);
        v___x_1376_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1304_,
            v___x_1151_,
            v___x_1151_,
            v___x_1375_,
        );
        v___x_1377_ = crate::leanh::lean_unsigned_to_nat(17);
        v___x_1378_ = lean_mk_empty_array_with_capacity(v___x_1377_);
        v___x_1379_ = lean_array_push(v___x_1378_, v___x_1326_);
        crate::leanh::lean_inc_ref_n(v___x_1328_, 7);
        v___x_1380_ = lean_array_push(v___x_1379_, v___x_1328_);
        v___x_1381_ = lean_array_push(v___x_1380_, v___x_1334_);
        v___x_1382_ = lean_array_push(v___x_1381_, v___x_1328_);
        v___x_1383_ = lean_array_push(v___x_1382_, v___x_1340_);
        v___x_1384_ = lean_array_push(v___x_1383_, v___x_1328_);
        v___x_1385_ = lean_array_push(v___x_1384_, v___x_1346_);
        v___x_1386_ = lean_array_push(v___x_1385_, v___x_1328_);
        v___x_1387_ = lean_array_push(v___x_1386_, v___x_1352_);
        v___x_1388_ = lean_array_push(v___x_1387_, v___x_1328_);
        v___x_1389_ = lean_array_push(v___x_1388_, v___x_1358_);
        v___x_1390_ = lean_array_push(v___x_1389_, v___x_1328_);
        v___x_1391_ = lean_array_push(v___x_1390_, v___x_1364_);
        v___x_1392_ = lean_array_push(v___x_1391_, v___x_1328_);
        v___x_1393_ = lean_array_push(v___x_1392_, v___x_1370_);
        v___x_1394_ = lean_array_push(v___x_1393_, v___x_1328_);
        v___x_1395_ = lean_array_push(v___x_1394_, v___x_1376_);
        v___x_1396_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1396_, 0, v___x_1133_);
        crate::leanh::lean_ctor_set(v___x_1396_, 1, v___x_1137_);
        crate::leanh::lean_ctor_set(v___x_1396_, 2, v___x_1395_);
        v___x_1397_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1137_,
            v___x_1155_,
            v___x_1396_,
            v___x_1166_,
        );
        v___x_1398_ = l_Lean_Syntax_node6(
            v___x_1133_,
            v___x_1319_,
            v___x_1320_,
            v___x_1152_,
            v___x_1151_,
            v___x_1303_,
            v___x_1397_,
            v___x_1151_,
        );
        v___x_1399_ = l_Lean_Syntax_node1(v___x_1133_, v___x_1137_, v___x_1398_);
        v___x_1400_ = l_Lean_Syntax_node1(v___x_1133_, v___x_1142_, v___x_1399_);
        v___x_1401_ = l_Lean_Syntax_node1(v___x_1133_, v___x_1141_, v___x_1400_);
        v___x_1402_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1143_, v___x_1145_, v___x_1401_);
        v___x_1403_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__173;
        v___x_1404_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__174;
        v___x_1405_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1405_, 0, v___x_1133_);
        crate::leanh::lean_ctor_set(v___x_1405_, 1, v___x_1403_);
        v___x_1406_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1404_, v___x_1405_, v___x_1152_);
        v___x_1407_ = crate::leanh::lean_unsigned_to_nat(23);
        v___x_1408_ = lean_mk_empty_array_with_capacity(v___x_1407_);
        v___x_1409_ = lean_array_push(v___x_1408_, v___x_1181_);
        v___x_1410_ = lean_array_push(v___x_1409_, v___x_1151_);
        v___x_1411_ = lean_array_push(v___x_1410_, v___x_1194_);
        v___x_1412_ = lean_array_push(v___x_1411_, v___x_1151_);
        v___x_1413_ = lean_array_push(v___x_1412_, v___x_1207_);
        v___x_1414_ = lean_array_push(v___x_1413_, v___x_1151_);
        v___x_1415_ = lean_array_push(v___x_1414_, v___x_1220_);
        v___x_1416_ = lean_array_push(v___x_1415_, v___x_1151_);
        v___x_1417_ = lean_array_push(v___x_1416_, v___x_1233_);
        v___x_1418_ = lean_array_push(v___x_1417_, v___x_1151_);
        v___x_1419_ = lean_array_push(v___x_1418_, v___x_1246_);
        v___x_1420_ = lean_array_push(v___x_1419_, v___x_1151_);
        v___x_1421_ = lean_array_push(v___x_1420_, v___x_1259_);
        v___x_1422_ = lean_array_push(v___x_1421_, v___x_1151_);
        v___x_1423_ = lean_array_push(v___x_1422_, v___x_1272_);
        v___x_1424_ = lean_array_push(v___x_1423_, v___x_1151_);
        v___x_1425_ = lean_array_push(v___x_1424_, v___x_1285_);
        v___x_1426_ = lean_array_push(v___x_1425_, v___x_1151_);
        v___x_1427_ = lean_array_push(v___x_1426_, v___x_1317_);
        v___x_1428_ = lean_array_push(v___x_1427_, v___x_1151_);
        v___x_1429_ = lean_array_push(v___x_1428_, v___x_1402_);
        v___x_1430_ = lean_array_push(v___x_1429_, v___x_1151_);
        v___x_1431_ = lean_array_push(v___x_1430_, v___x_1406_);
        v___x_1432_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1432_, 0, v___x_1133_);
        crate::leanh::lean_ctor_set(v___x_1432_, 1, v___x_1137_);
        crate::leanh::lean_ctor_set(v___x_1432_, 2, v___x_1431_);
        v___x_1433_ = l_Lean_Syntax_node1(v___x_1133_, v___x_1142_, v___x_1432_);
        v___x_1434_ = l_Lean_Syntax_node1(v___x_1133_, v___x_1141_, v___x_1433_);
        crate::leanh::lean_inc_ref(v___x_1140_);
        v___x_1435_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1138_, v___x_1140_, v___x_1434_);
        v___x_1436_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__175;
        v___x_1437_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__176;
        v___x_1438_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1438_, 0, v___x_1133_);
        crate::leanh::lean_ctor_set(v___x_1438_, 1, v___x_1436_);
        v___x_1439_ = l_Lean_Syntax_node1(v___x_1133_, v___x_1437_, v___x_1438_);
        v___x_1440_ = l_Lean_Syntax_node1(v___x_1133_, v___x_1137_, v___x_1439_);
        v___x_1441_ = l_Lean_Syntax_node1(v___x_1133_, v___x_1142_, v___x_1440_);
        v___x_1442_ = l_Lean_Syntax_node1(v___x_1133_, v___x_1141_, v___x_1441_);
        v___x_1443_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1138_, v___x_1140_, v___x_1442_);
        v___x_1444_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1137_, v___x_1435_, v___x_1443_);
        v___x_1445_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1135_, v___x_1136_, v___x_1444_);
        v___x_1446_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1446_, 0, v___x_1445_);
        crate::leanh::lean_ctor_set(v___x_1446_, 1, v_a_1124_);
        return v___x_1446_;
    }
}
pub unsafe fn l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___boxed(
    mut v_x_1447_: *mut crate::leanh::LeanObject,
    mut v_a_1448_: *mut crate::leanh::LeanObject,
    mut v_a_1449_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1450_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1(v_x_1447_, v_a_1448_, v_a_1449_);
    crate::leanh::lean_dec_ref(v_a_1448_);
    return v_res_1450_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Range_Polymorphic_GetElemTactic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Range_Polymorphic_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Vector_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Slice_Array_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Range_Polymorphic_GetElemTactic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Init_Grind_Tactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Range_Polymorphic_GetElemTactic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Grind_Tactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Vector_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Slice_Array_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_GetElemTactic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Range_Polymorphic_GetElemTactic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Range_Polymorphic_GetElemTactic(builtin);
}
