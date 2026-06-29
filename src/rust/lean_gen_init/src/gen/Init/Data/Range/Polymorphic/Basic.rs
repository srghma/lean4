// Lean compiler output
// Module: Init.Data.Range.Polymorphic.Basic
// Imports: Init.Data.Range.Polymorphic.PRange Init.Data.Option.Instances
use crate::r#gen::Init::Data::Option::Instances::{
    initialize_Init_Data_Option_Instances, l_Option_decidableForallMem___redArg,
    runtime_initialize_Init_Data_Option_Instances,
};
use crate::r#gen::Init::Data::Range::Polymorphic::PRange::{
    initialize_Init_Data_Range_Polymorphic_PRange,
    runtime_initialize_Init_Data_Range_Polymorphic_PRange,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_SourceInfo_fromRef, l_Lean_Syntax_isOfKind, l_Lean_Syntax_node1, l_Lean_Syntax_node2,
    l_Lean_Syntax_node3, l_Lean_Syntax_node4, l_Lean_addMacroScope, l_String_toRawSubstring_x27,
};
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__0_value: crate::leanh::LeanStringObject<33> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [116, 97, 99, 116, 105, 99, 71, 101, 116, 95, 101, 108, 101, 109, 95, 116, 97, 99, 116, 105, 99, 95, 101, 120, 116, 101, 110, 115, 105, 98, 108, 101, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__0_value) as *mut crate::leanh::LeanObject,7705027380931481693 as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__5_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [102, 105, 114, 115, 116, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__5_value) as *mut crate::leanh::LeanObject;
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__6_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__6_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__6_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__6_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__6_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__5_value) as *mut crate::leanh::LeanObject,12551601070224435259 as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__7_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__7_value) as *mut crate::leanh::LeanObject,9855511589286918680 as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__9_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [103, 114, 111, 117, 112, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__10_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__9_value) as *mut crate::leanh::LeanObject,2214559063752339918 as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__11_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [124, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__12_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__12_value) as *mut crate::leanh::LeanObject;
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__13_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__13_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__13_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__13_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__13_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__13_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__13_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__12_value) as *mut crate::leanh::LeanObject,8504843326314613972 as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__14_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__14_value) as *mut crate::leanh::LeanObject;
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__14_value) as *mut crate::leanh::LeanObject,17228437386856258271 as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__16_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [97, 112, 112, 108, 121, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__16_value) as *mut crate::leanh::LeanObject;
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__16_value) as *mut crate::leanh::LeanObject,5826123769708379594 as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__18_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__18_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__19_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__19: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__19_value) as *mut crate::leanh::LeanObject;
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__20_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__20_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__20_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__20_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__20_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__18_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__20_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__20_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__19_value) as *mut crate::leanh::LeanObject,12966880221525079621 as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__20: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__20_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__21_value: crate::leanh::LeanStringObject<44> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 44, m_capacity: 44, m_length: 43, m_data: [83, 116, 100, 46, 82, 99, 111, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 103, 101, 116, 95, 101, 108, 101, 109, 95, 104, 101, 108, 112, 101, 114, 95, 117, 112, 112, 101, 114, 95, 111, 112, 101, 110, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__21: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__21_value) as *mut crate::leanh::LeanObject;
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__22_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__22: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__23_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [83, 116, 100, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__23: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__23_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__24_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [82, 99, 111, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__24: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__24_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__25_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [73, 110, 116, 101, 114, 110, 97, 108, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__25: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__25_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__26_value: crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [103, 101, 116, 95, 101, 108, 101, 109, 95, 104, 101, 108, 112, 101, 114, 95, 117, 112, 112, 101, 114, 95, 111, 112, 101, 110, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__26: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__26_value) as *mut crate::leanh::LeanObject;
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__27_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__23_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__27_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__27_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__24_value) as *mut crate::leanh::LeanObject,36003929318889298 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__27_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__27_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__25_value) as *mut crate::leanh::LeanObject,8015440497992668395 as *mut crate::leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__27_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__27_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__26_value) as *mut crate::leanh::LeanObject,8588407234422212448 as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__27: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__27_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__28_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__27_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__28: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__28_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__29_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__28_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__29: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__29_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__30_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 7, m_data: [116, 101, 114, 109, 226, 128, 185, 95, 226, 128, 186, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__30: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__30_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__31_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__30_value) as *mut crate::leanh::LeanObject,8315864120963730325 as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__31: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__31_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__32_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 128, 185, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__32: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__32_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__33_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 111, 108, 101, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__33: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__33_value) as *mut crate::leanh::LeanObject;
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__34_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__34_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__34_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__34_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__34_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__18_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__34_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__34_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__33_value) as *mut crate::leanh::LeanObject,3984140175429830279 as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__34: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__34_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__35_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [95, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__35: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__35_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__36_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 128, 186, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__36: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__36_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__37_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [112, 97, 114, 101, 110, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__37: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__37_value) as *mut crate::leanh::LeanObject;
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__38_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__38_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__38_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__38_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__38_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__18_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__38_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__38_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__37_value) as *mut crate::leanh::LeanObject,7932075773091973500 as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__38: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__38_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__39_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [104, 121, 103, 105, 101, 110, 105, 99, 76, 80, 97, 114, 101, 110, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__39: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__39_value) as *mut crate::leanh::LeanObject;
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__40_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__40_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__40_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__40_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__40_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__18_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__40_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__40_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__39_value) as *mut crate::leanh::LeanObject,7306243862518720553 as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__40: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__40_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__41_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__41: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__41_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__42_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__42: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__42_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__43_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__42_value) as *mut crate::leanh::LeanObject,9871775667037945883 as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__43: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__43_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__44_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__44: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__44_value) as *mut crate::leanh::LeanObject;
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__45_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__45: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__46_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__23_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__46: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__46_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__47_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__46_value) as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__47: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__47_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__48_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 82, 97, 110, 103, 101, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__48: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__48_value) as *mut crate::leanh::LeanObject;
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__49_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__23_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__49_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__49_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__48_value) as *mut crate::leanh::LeanObject,9849097416327629642 as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__49: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__49_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__50_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__49_value) as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__50: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__50_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__51_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__50_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__51: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__51_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__52_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__47_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__51_value) as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__52: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__52_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__53_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [98, 121, 84, 97, 99, 116, 105, 99, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__53: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__53_value) as *mut crate::leanh::LeanObject;
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__54_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__54_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__54_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__54_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__54_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__18_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__54_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__54_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__53_value) as *mut crate::leanh::LeanObject,16173796135615239867 as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__54: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__54_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__55_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [98, 121, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__55: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__55_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__56_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [116, 97, 99, 116, 105, 99, 84, 114, 105, 118, 105, 97, 108, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__56: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__56_value) as *mut crate::leanh::LeanObject;
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__57_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__57_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__57_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__57_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__57_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__57_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__57_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__56_value) as *mut crate::leanh::LeanObject,2766452847008772443 as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__57: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__57_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__58_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [116, 114, 105, 118, 105, 97, 108, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__58: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__58_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__59_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__59: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__59_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__60_value: crate::leanh::LeanStringObject<44> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 44, m_capacity: 44, m_length: 43, m_data: [83, 116, 100, 46, 82, 111, 111, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 103, 101, 116, 95, 101, 108, 101, 109, 95, 104, 101, 108, 112, 101, 114, 95, 117, 112, 112, 101, 114, 95, 111, 112, 101, 110, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__60: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__60_value) as *mut crate::leanh::LeanObject;
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__61_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__61: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__62_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [82, 111, 111, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__62: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__62_value) as *mut crate::leanh::LeanObject;
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__63_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__23_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__63_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__63_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__62_value) as *mut crate::leanh::LeanObject,17971250720669795982 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__63_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__63_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__25_value) as *mut crate::leanh::LeanObject,17821413486542541535 as *mut crate::leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__63_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__63_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__26_value) as *mut crate::leanh::LeanObject,13586587588939731556 as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__63: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__63_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__64_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__63_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__64: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__64_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__65_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__64_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__65: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__65_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__66_value: crate::leanh::LeanStringObject<44> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 44, m_capacity: 44, m_length: 43, m_data: [83, 116, 100, 46, 82, 105, 111, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 103, 101, 116, 95, 101, 108, 101, 109, 95, 104, 101, 108, 112, 101, 114, 95, 117, 112, 112, 101, 114, 95, 111, 112, 101, 110, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__66: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__66_value) as *mut crate::leanh::LeanObject;
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__67_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__67: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__68_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [82, 105, 111, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__68: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__68_value) as *mut crate::leanh::LeanObject;
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__69_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__23_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__69_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__69_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__68_value) as *mut crate::leanh::LeanObject,10504416010916204673 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__69_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__69_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__25_value) as *mut crate::leanh::LeanObject,14499228462873218844 as *mut crate::leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__69_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__69_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__26_value) as *mut crate::leanh::LeanObject,9086931729220931171 as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__69: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__69_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__70_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__69_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__70: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__70_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__71_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__70_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__71: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__71_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__72_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [100, 111, 110, 101, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__72: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__72_value) as *mut crate::leanh::LeanObject;
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__73_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__73_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__73_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__73_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__73_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__73_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__73_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__72_value) as *mut crate::leanh::LeanObject,8876691400619696497 as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__73: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__73_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Std_Rcc_isEmpty___redArg(
    mut v_inst_499_: *mut crate::leanh::LeanObject,
    mut v_r_500_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_lower_501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_504_: u8 = 0;
    v_lower_501_ = crate::leanh::lean_ctor_get(v_r_500_, 0);
    crate::leanh::lean_inc(v_lower_501_);
    v_upper_502_ = crate::leanh::lean_ctor_get(v_r_500_, 1);
    crate::leanh::lean_inc(v_upper_502_);
    crate::leanh::lean_dec_ref(v_r_500_);
    v___x_503_ = crate::leanh::lean_apply_2(v_inst_499_, v_lower_501_, v_upper_502_);
    v___x_504_ = (crate::leanh::lean_unbox(v___x_503_) as u8);
    if v___x_504_ == 0 {
        let mut v___x_505_: u8 = 0;
        v___x_505_ = 1;
        return v___x_505_;
    } else {
        let mut v___x_506_: u8 = 0;
        v___x_506_ = 0;
        return v___x_506_;
    }
}
pub unsafe fn l_Std_Rcc_isEmpty___redArg___boxed(
    mut v_inst_507_: *mut crate::leanh::LeanObject,
    mut v_r_508_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_509_: u8 = 0;
    let mut v_r_510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_509_ = l_Std_Rcc_isEmpty___redArg(v_inst_507_, v_r_508_);
    v_r_510_ = crate::leanh::lean_box((v_res_509_) as usize);
    return v_r_510_;
}
pub unsafe fn l_Std_Rcc_isEmpty(
    mut v_00_u03b1_511_: *mut crate::leanh::LeanObject,
    mut v_inst_512_: *mut crate::leanh::LeanObject,
    mut v_inst_513_: *mut crate::leanh::LeanObject,
    mut v_inst_514_: *mut crate::leanh::LeanObject,
    mut v_r_515_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_lower_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_519_: u8 = 0;
    v_lower_516_ = crate::leanh::lean_ctor_get(v_r_515_, 0);
    crate::leanh::lean_inc(v_lower_516_);
    v_upper_517_ = crate::leanh::lean_ctor_get(v_r_515_, 1);
    crate::leanh::lean_inc(v_upper_517_);
    crate::leanh::lean_dec_ref(v_r_515_);
    v___x_518_ = crate::leanh::lean_apply_2(v_inst_513_, v_lower_516_, v_upper_517_);
    v___x_519_ = (crate::leanh::lean_unbox(v___x_518_) as u8);
    if v___x_519_ == 0 {
        let mut v___x_520_: u8 = 0;
        v___x_520_ = 1;
        return v___x_520_;
    } else {
        let mut v___x_521_: u8 = 0;
        v___x_521_ = 0;
        return v___x_521_;
    }
}
pub unsafe fn l_Std_Rcc_isEmpty___boxed(
    mut v_00_u03b1_522_: *mut crate::leanh::LeanObject,
    mut v_inst_523_: *mut crate::leanh::LeanObject,
    mut v_inst_524_: *mut crate::leanh::LeanObject,
    mut v_inst_525_: *mut crate::leanh::LeanObject,
    mut v_r_526_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_527_: u8 = 0;
    let mut v_r_528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_527_ = l_Std_Rcc_isEmpty(
        v_00_u03b1_522_,
        v_inst_523_,
        v_inst_524_,
        v_inst_525_,
        v_r_526_,
    );
    crate::leanh::lean_dec_ref(v_inst_525_);
    v_r_528_ = crate::leanh::lean_box((v_res_527_) as usize);
    return v_r_528_;
}
pub unsafe fn l_Std_Rco_isEmpty___redArg(
    mut v_inst_529_: *mut crate::leanh::LeanObject,
    mut v_r_530_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_lower_531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_534_: u8 = 0;
    v_lower_531_ = crate::leanh::lean_ctor_get(v_r_530_, 0);
    crate::leanh::lean_inc(v_lower_531_);
    v_upper_532_ = crate::leanh::lean_ctor_get(v_r_530_, 1);
    crate::leanh::lean_inc(v_upper_532_);
    crate::leanh::lean_dec_ref(v_r_530_);
    v___x_533_ = crate::leanh::lean_apply_2(v_inst_529_, v_lower_531_, v_upper_532_);
    v___x_534_ = (crate::leanh::lean_unbox(v___x_533_) as u8);
    if v___x_534_ == 0 {
        let mut v___x_535_: u8 = 0;
        v___x_535_ = 1;
        return v___x_535_;
    } else {
        let mut v___x_536_: u8 = 0;
        v___x_536_ = 0;
        return v___x_536_;
    }
}
pub unsafe fn l_Std_Rco_isEmpty___redArg___boxed(
    mut v_inst_537_: *mut crate::leanh::LeanObject,
    mut v_r_538_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_539_: u8 = 0;
    let mut v_r_540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_539_ = l_Std_Rco_isEmpty___redArg(v_inst_537_, v_r_538_);
    v_r_540_ = crate::leanh::lean_box((v_res_539_) as usize);
    return v_r_540_;
}
pub unsafe fn l_Std_Rco_isEmpty(
    mut v_00_u03b1_541_: *mut crate::leanh::LeanObject,
    mut v_inst_542_: *mut crate::leanh::LeanObject,
    mut v_inst_543_: *mut crate::leanh::LeanObject,
    mut v_inst_544_: *mut crate::leanh::LeanObject,
    mut v_r_545_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_lower_546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_549_: u8 = 0;
    v_lower_546_ = crate::leanh::lean_ctor_get(v_r_545_, 0);
    crate::leanh::lean_inc(v_lower_546_);
    v_upper_547_ = crate::leanh::lean_ctor_get(v_r_545_, 1);
    crate::leanh::lean_inc(v_upper_547_);
    crate::leanh::lean_dec_ref(v_r_545_);
    v___x_548_ = crate::leanh::lean_apply_2(v_inst_543_, v_lower_546_, v_upper_547_);
    v___x_549_ = (crate::leanh::lean_unbox(v___x_548_) as u8);
    if v___x_549_ == 0 {
        let mut v___x_550_: u8 = 0;
        v___x_550_ = 1;
        return v___x_550_;
    } else {
        let mut v___x_551_: u8 = 0;
        v___x_551_ = 0;
        return v___x_551_;
    }
}
pub unsafe fn l_Std_Rco_isEmpty___boxed(
    mut v_00_u03b1_552_: *mut crate::leanh::LeanObject,
    mut v_inst_553_: *mut crate::leanh::LeanObject,
    mut v_inst_554_: *mut crate::leanh::LeanObject,
    mut v_inst_555_: *mut crate::leanh::LeanObject,
    mut v_r_556_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_557_: u8 = 0;
    let mut v_r_558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_557_ = l_Std_Rco_isEmpty(
        v_00_u03b1_552_,
        v_inst_553_,
        v_inst_554_,
        v_inst_555_,
        v_r_556_,
    );
    crate::leanh::lean_dec_ref(v_inst_555_);
    v_r_558_ = crate::leanh::lean_box((v_res_557_) as usize);
    return v_r_558_;
}
pub unsafe fn l_Std_Rci_isEmpty(
    mut v_00_u03b1_559_: *mut crate::leanh::LeanObject,
    mut v_inst_560_: *mut crate::leanh::LeanObject,
    mut v_x_561_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_562_: u8 = 0;
    v___x_562_ = 0;
    return v___x_562_;
}
pub unsafe fn l_Std_Rci_isEmpty___boxed(
    mut v_00_u03b1_563_: *mut crate::leanh::LeanObject,
    mut v_inst_564_: *mut crate::leanh::LeanObject,
    mut v_x_565_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_566_: u8 = 0;
    let mut v_r_567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_566_ = l_Std_Rci_isEmpty(v_00_u03b1_563_, v_inst_564_, v_x_565_);
    crate::leanh::lean_dec(v_x_565_);
    crate::leanh::lean_dec_ref(v_inst_564_);
    v_r_567_ = crate::leanh::lean_box((v_res_566_) as usize);
    return v_r_567_;
}
pub unsafe fn l_Std_Roc_isEmpty___redArg(
    mut v_inst_568_: *mut crate::leanh::LeanObject,
    mut v_r_569_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_lower_570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_573_: u8 = 0;
    v_lower_570_ = crate::leanh::lean_ctor_get(v_r_569_, 0);
    crate::leanh::lean_inc(v_lower_570_);
    v_upper_571_ = crate::leanh::lean_ctor_get(v_r_569_, 1);
    crate::leanh::lean_inc(v_upper_571_);
    crate::leanh::lean_dec_ref(v_r_569_);
    v___x_572_ = crate::leanh::lean_apply_2(v_inst_568_, v_lower_570_, v_upper_571_);
    v___x_573_ = (crate::leanh::lean_unbox(v___x_572_) as u8);
    if v___x_573_ == 0 {
        let mut v___x_574_: u8 = 0;
        v___x_574_ = 1;
        return v___x_574_;
    } else {
        let mut v___x_575_: u8 = 0;
        v___x_575_ = 0;
        return v___x_575_;
    }
}
pub unsafe fn l_Std_Roc_isEmpty___redArg___boxed(
    mut v_inst_576_: *mut crate::leanh::LeanObject,
    mut v_r_577_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_578_: u8 = 0;
    let mut v_r_579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_578_ = l_Std_Roc_isEmpty___redArg(v_inst_576_, v_r_577_);
    v_r_579_ = crate::leanh::lean_box((v_res_578_) as usize);
    return v_r_579_;
}
pub unsafe fn l_Std_Roc_isEmpty(
    mut v_00_u03b1_580_: *mut crate::leanh::LeanObject,
    mut v_inst_581_: *mut crate::leanh::LeanObject,
    mut v_inst_582_: *mut crate::leanh::LeanObject,
    mut v_inst_583_: *mut crate::leanh::LeanObject,
    mut v_r_584_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_lower_585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_588_: u8 = 0;
    v_lower_585_ = crate::leanh::lean_ctor_get(v_r_584_, 0);
    crate::leanh::lean_inc(v_lower_585_);
    v_upper_586_ = crate::leanh::lean_ctor_get(v_r_584_, 1);
    crate::leanh::lean_inc(v_upper_586_);
    crate::leanh::lean_dec_ref(v_r_584_);
    v___x_587_ = crate::leanh::lean_apply_2(v_inst_582_, v_lower_585_, v_upper_586_);
    v___x_588_ = (crate::leanh::lean_unbox(v___x_587_) as u8);
    if v___x_588_ == 0 {
        let mut v___x_589_: u8 = 0;
        v___x_589_ = 1;
        return v___x_589_;
    } else {
        let mut v___x_590_: u8 = 0;
        v___x_590_ = 0;
        return v___x_590_;
    }
}
pub unsafe fn l_Std_Roc_isEmpty___boxed(
    mut v_00_u03b1_591_: *mut crate::leanh::LeanObject,
    mut v_inst_592_: *mut crate::leanh::LeanObject,
    mut v_inst_593_: *mut crate::leanh::LeanObject,
    mut v_inst_594_: *mut crate::leanh::LeanObject,
    mut v_r_595_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_596_: u8 = 0;
    let mut v_r_597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_596_ = l_Std_Roc_isEmpty(
        v_00_u03b1_591_,
        v_inst_592_,
        v_inst_593_,
        v_inst_594_,
        v_r_595_,
    );
    crate::leanh::lean_dec_ref(v_inst_594_);
    v_r_597_ = crate::leanh::lean_box((v_res_596_) as usize);
    return v_r_597_;
}
pub unsafe fn l_Std_Roo_isEmpty___redArg___lam__0(
    mut v_inst_598_: *mut crate::leanh::LeanObject,
    mut v_upper_599_: *mut crate::leanh::LeanObject,
    mut v_a_600_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_602_: u8 = 0;
    v___x_601_ = crate::leanh::lean_apply_2(v_inst_598_, v_a_600_, v_upper_599_);
    v___x_602_ = (crate::leanh::lean_unbox(v___x_601_) as u8);
    if v___x_602_ == 0 {
        let mut v___x_603_: u8 = 0;
        v___x_603_ = 1;
        return v___x_603_;
    } else {
        let mut v___x_604_: u8 = 0;
        v___x_604_ = 0;
        return v___x_604_;
    }
}
pub unsafe fn l_Std_Roo_isEmpty___redArg___lam__0___boxed(
    mut v_inst_605_: *mut crate::leanh::LeanObject,
    mut v_upper_606_: *mut crate::leanh::LeanObject,
    mut v_a_607_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_608_: u8 = 0;
    let mut v_r_609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_608_ = l_Std_Roo_isEmpty___redArg___lam__0(v_inst_605_, v_upper_606_, v_a_607_);
    v_r_609_ = crate::leanh::lean_box((v_res_608_) as usize);
    return v_r_609_;
}
pub unsafe fn l_Std_Roo_isEmpty___redArg(
    mut v_inst_610_: *mut crate::leanh::LeanObject,
    mut v_inst_611_: *mut crate::leanh::LeanObject,
    mut v_r_612_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_succ_x3f_613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_618_: u8 = 0;
    v_succ_x3f_613_ = crate::leanh::lean_ctor_get(v_inst_611_, 0);
    crate::leanh::lean_inc_ref(v_succ_x3f_613_);
    crate::leanh::lean_dec_ref(v_inst_611_);
    v_lower_614_ = crate::leanh::lean_ctor_get(v_r_612_, 0);
    crate::leanh::lean_inc(v_lower_614_);
    v_upper_615_ = crate::leanh::lean_ctor_get(v_r_612_, 1);
    crate::leanh::lean_inc(v_upper_615_);
    crate::leanh::lean_dec_ref(v_r_612_);
    v___f_616_ = crate::leanh::lean_alloc_closure(
        l_Std_Roo_isEmpty___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_616_, 0, v_inst_610_);
    crate::leanh::lean_closure_set(v___f_616_, 1, v_upper_615_);
    v___x_617_ = crate::leanh::lean_apply_1(v_succ_x3f_613_, v_lower_614_);
    v___x_618_ = l_Option_decidableForallMem___redArg(v___f_616_, v___x_617_);
    return v___x_618_;
}
pub unsafe fn l_Std_Roo_isEmpty___redArg___boxed(
    mut v_inst_619_: *mut crate::leanh::LeanObject,
    mut v_inst_620_: *mut crate::leanh::LeanObject,
    mut v_r_621_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_622_: u8 = 0;
    let mut v_r_623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_622_ = l_Std_Roo_isEmpty___redArg(v_inst_619_, v_inst_620_, v_r_621_);
    v_r_623_ = crate::leanh::lean_box((v_res_622_) as usize);
    return v_r_623_;
}
pub unsafe fn l_Std_Roo_isEmpty(
    mut v_00_u03b1_624_: *mut crate::leanh::LeanObject,
    mut v_inst_625_: *mut crate::leanh::LeanObject,
    mut v_inst_626_: *mut crate::leanh::LeanObject,
    mut v_inst_627_: *mut crate::leanh::LeanObject,
    mut v_r_628_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_succ_x3f_629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_634_: u8 = 0;
    v_succ_x3f_629_ = crate::leanh::lean_ctor_get(v_inst_627_, 0);
    crate::leanh::lean_inc_ref(v_succ_x3f_629_);
    crate::leanh::lean_dec_ref(v_inst_627_);
    v_lower_630_ = crate::leanh::lean_ctor_get(v_r_628_, 0);
    crate::leanh::lean_inc(v_lower_630_);
    v_upper_631_ = crate::leanh::lean_ctor_get(v_r_628_, 1);
    crate::leanh::lean_inc(v_upper_631_);
    crate::leanh::lean_dec_ref(v_r_628_);
    v___f_632_ = crate::leanh::lean_alloc_closure(
        l_Std_Roo_isEmpty___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_632_, 0, v_inst_626_);
    crate::leanh::lean_closure_set(v___f_632_, 1, v_upper_631_);
    v___x_633_ = crate::leanh::lean_apply_1(v_succ_x3f_629_, v_lower_630_);
    v___x_634_ = l_Option_decidableForallMem___redArg(v___f_632_, v___x_633_);
    return v___x_634_;
}
pub unsafe fn l_Std_Roo_isEmpty___boxed(
    mut v_00_u03b1_635_: *mut crate::leanh::LeanObject,
    mut v_inst_636_: *mut crate::leanh::LeanObject,
    mut v_inst_637_: *mut crate::leanh::LeanObject,
    mut v_inst_638_: *mut crate::leanh::LeanObject,
    mut v_r_639_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_640_: u8 = 0;
    let mut v_r_641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_640_ = l_Std_Roo_isEmpty(
        v_00_u03b1_635_,
        v_inst_636_,
        v_inst_637_,
        v_inst_638_,
        v_r_639_,
    );
    v_r_641_ = crate::leanh::lean_box((v_res_640_) as usize);
    return v_r_641_;
}
pub unsafe fn l_Std_Roi_isEmpty___redArg(
    mut v_inst_642_: *mut crate::leanh::LeanObject,
    mut v_r_643_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_succ_x3f_644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_succ_x3f_644_ = crate::leanh::lean_ctor_get(v_inst_642_, 0);
    crate::leanh::lean_inc_ref(v_succ_x3f_644_);
    crate::leanh::lean_dec_ref(v_inst_642_);
    v___x_645_ = crate::leanh::lean_apply_1(v_succ_x3f_644_, v_r_643_);
    if crate::leanh::lean_obj_tag(v___x_645_) == 0 {
        let mut v___x_646_: u8 = 0;
        v___x_646_ = 1;
        return v___x_646_;
    } else {
        let mut v___x_647_: u8 = 0;
        crate::leanh::lean_dec_ref_known(v___x_645_, 1);
        v___x_647_ = 0;
        return v___x_647_;
    }
}
pub unsafe fn l_Std_Roi_isEmpty___redArg___boxed(
    mut v_inst_648_: *mut crate::leanh::LeanObject,
    mut v_r_649_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_650_: u8 = 0;
    let mut v_r_651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_650_ = l_Std_Roi_isEmpty___redArg(v_inst_648_, v_r_649_);
    v_r_651_ = crate::leanh::lean_box((v_res_650_) as usize);
    return v_r_651_;
}
pub unsafe fn l_Std_Roi_isEmpty(
    mut v_00_u03b1_652_: *mut crate::leanh::LeanObject,
    mut v_inst_653_: *mut crate::leanh::LeanObject,
    mut v_r_654_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_succ_x3f_655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_succ_x3f_655_ = crate::leanh::lean_ctor_get(v_inst_653_, 0);
    crate::leanh::lean_inc_ref(v_succ_x3f_655_);
    crate::leanh::lean_dec_ref(v_inst_653_);
    v___x_656_ = crate::leanh::lean_apply_1(v_succ_x3f_655_, v_r_654_);
    if crate::leanh::lean_obj_tag(v___x_656_) == 0 {
        let mut v___x_657_: u8 = 0;
        v___x_657_ = 1;
        return v___x_657_;
    } else {
        let mut v___x_658_: u8 = 0;
        crate::leanh::lean_dec_ref_known(v___x_656_, 1);
        v___x_658_ = 0;
        return v___x_658_;
    }
}
pub unsafe fn l_Std_Roi_isEmpty___boxed(
    mut v_00_u03b1_659_: *mut crate::leanh::LeanObject,
    mut v_inst_660_: *mut crate::leanh::LeanObject,
    mut v_r_661_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_662_: u8 = 0;
    let mut v_r_663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_662_ = l_Std_Roi_isEmpty(v_00_u03b1_659_, v_inst_660_, v_r_661_);
    v_r_663_ = crate::leanh::lean_box((v_res_662_) as usize);
    return v_r_663_;
}
pub unsafe fn l_Std_Ric_isEmpty(
    mut v_00_u03b1_664_: *mut crate::leanh::LeanObject,
    mut v_inst_665_: *mut crate::leanh::LeanObject,
    mut v_x_666_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_667_: u8 = 0;
    v___x_667_ = 0;
    return v___x_667_;
}
pub unsafe fn l_Std_Ric_isEmpty___boxed(
    mut v_00_u03b1_668_: *mut crate::leanh::LeanObject,
    mut v_inst_669_: *mut crate::leanh::LeanObject,
    mut v_x_670_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_671_: u8 = 0;
    let mut v_r_672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_671_ = l_Std_Ric_isEmpty(v_00_u03b1_668_, v_inst_669_, v_x_670_);
    crate::leanh::lean_dec(v_x_670_);
    crate::leanh::lean_dec_ref(v_inst_669_);
    v_r_672_ = crate::leanh::lean_box((v_res_671_) as usize);
    return v_r_672_;
}
pub unsafe fn l_Std_Rio_isEmpty___redArg___lam__0(
    mut v_inst_673_: *mut crate::leanh::LeanObject,
    mut v_r_674_: *mut crate::leanh::LeanObject,
    mut v_a_675_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_677_: u8 = 0;
    v___x_676_ = crate::leanh::lean_apply_2(v_inst_673_, v_a_675_, v_r_674_);
    v___x_677_ = (crate::leanh::lean_unbox(v___x_676_) as u8);
    if v___x_677_ == 0 {
        let mut v___x_678_: u8 = 0;
        v___x_678_ = 1;
        return v___x_678_;
    } else {
        let mut v___x_679_: u8 = 0;
        v___x_679_ = 0;
        return v___x_679_;
    }
}
pub unsafe fn l_Std_Rio_isEmpty___redArg___lam__0___boxed(
    mut v_inst_680_: *mut crate::leanh::LeanObject,
    mut v_r_681_: *mut crate::leanh::LeanObject,
    mut v_a_682_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_683_: u8 = 0;
    let mut v_r_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_683_ = l_Std_Rio_isEmpty___redArg___lam__0(v_inst_680_, v_r_681_, v_a_682_);
    v_r_684_ = crate::leanh::lean_box((v_res_683_) as usize);
    return v_r_684_;
}
pub unsafe fn l_Std_Rio_isEmpty___redArg(
    mut v_inst_685_: *mut crate::leanh::LeanObject,
    mut v_inst_686_: *mut crate::leanh::LeanObject,
    mut v_r_687_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___f_688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_689_: u8 = 0;
    v___f_688_ = crate::leanh::lean_alloc_closure(
        l_Std_Rio_isEmpty___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_688_, 0, v_inst_685_);
    crate::leanh::lean_closure_set(v___f_688_, 1, v_r_687_);
    v___x_689_ = l_Option_decidableForallMem___redArg(v___f_688_, v_inst_686_);
    return v___x_689_;
}
pub unsafe fn l_Std_Rio_isEmpty___redArg___boxed(
    mut v_inst_690_: *mut crate::leanh::LeanObject,
    mut v_inst_691_: *mut crate::leanh::LeanObject,
    mut v_r_692_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_693_: u8 = 0;
    let mut v_r_694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_693_ = l_Std_Rio_isEmpty___redArg(v_inst_690_, v_inst_691_, v_r_692_);
    v_r_694_ = crate::leanh::lean_box((v_res_693_) as usize);
    return v_r_694_;
}
pub unsafe fn l_Std_Rio_isEmpty(
    mut v_00_u03b1_695_: *mut crate::leanh::LeanObject,
    mut v_inst_696_: *mut crate::leanh::LeanObject,
    mut v_inst_697_: *mut crate::leanh::LeanObject,
    mut v_inst_698_: *mut crate::leanh::LeanObject,
    mut v_inst_699_: *mut crate::leanh::LeanObject,
    mut v_r_700_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___f_701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_702_: u8 = 0;
    v___f_701_ = crate::leanh::lean_alloc_closure(
        l_Std_Rio_isEmpty___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_701_, 0, v_inst_697_);
    crate::leanh::lean_closure_set(v___f_701_, 1, v_r_700_);
    v___x_702_ = l_Option_decidableForallMem___redArg(v___f_701_, v_inst_699_);
    return v___x_702_;
}
pub unsafe fn l_Std_Rio_isEmpty___boxed(
    mut v_00_u03b1_703_: *mut crate::leanh::LeanObject,
    mut v_inst_704_: *mut crate::leanh::LeanObject,
    mut v_inst_705_: *mut crate::leanh::LeanObject,
    mut v_inst_706_: *mut crate::leanh::LeanObject,
    mut v_inst_707_: *mut crate::leanh::LeanObject,
    mut v_r_708_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_709_: u8 = 0;
    let mut v_r_710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_709_ = l_Std_Rio_isEmpty(
        v_00_u03b1_703_,
        v_inst_704_,
        v_inst_705_,
        v_inst_706_,
        v_inst_707_,
        v_r_708_,
    );
    crate::leanh::lean_dec_ref(v_inst_706_);
    v_r_710_ = crate::leanh::lean_box((v_res_709_) as usize);
    return v_r_710_;
}
pub unsafe fn l_Std_Rii_isEmpty___redArg(mut v_inst_711_: *mut crate::leanh::LeanObject) -> u8 {
    if crate::leanh::lean_obj_tag(v_inst_711_) == 0 {
        let mut v___x_712_: u8 = 0;
        v___x_712_ = 1;
        return v___x_712_;
    } else {
        let mut v___x_713_: u8 = 0;
        v___x_713_ = 0;
        return v___x_713_;
    }
}
pub unsafe fn l_Std_Rii_isEmpty___redArg___boxed(
    mut v_inst_714_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_715_: u8 = 0;
    let mut v_r_716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_715_ = l_Std_Rii_isEmpty___redArg(v_inst_714_);
    crate::leanh::lean_dec(v_inst_714_);
    v_r_716_ = crate::leanh::lean_box((v_res_715_) as usize);
    return v_r_716_;
}
pub unsafe fn l_Std_Rii_isEmpty(
    mut v_00_u03b1_717_: *mut crate::leanh::LeanObject,
    mut v_inst_718_: *mut crate::leanh::LeanObject,
    mut v_x_719_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_inst_718_) == 0 {
        let mut v___x_720_: u8 = 0;
        v___x_720_ = 1;
        return v___x_720_;
    } else {
        let mut v___x_721_: u8 = 0;
        v___x_721_ = 0;
        return v___x_721_;
    }
}
pub unsafe fn l_Std_Rii_isEmpty___boxed(
    mut v_00_u03b1_722_: *mut crate::leanh::LeanObject,
    mut v_inst_723_: *mut crate::leanh::LeanObject,
    mut v_x_724_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_725_: u8 = 0;
    let mut v_r_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_725_ = l_Std_Rii_isEmpty(v_00_u03b1_722_, v_inst_723_, v_x_724_);
    crate::leanh::lean_dec(v_inst_723_);
    v_r_726_ = crate::leanh::lean_box((v_res_725_) as usize);
    return v_r_726_;
}
pub unsafe fn _init_l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__22()
-> *mut crate::leanh::LeanObject {
    let mut v___x_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_772_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__21;
    v___x_773_ = l_String_toRawSubstring_x27(v___x_772_);
    return v___x_773_;
}
pub unsafe fn _init_l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__45()
-> *mut crate::leanh::LeanObject {
    let mut v___x_818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_818_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__44;
    v___x_819_ = l_String_toRawSubstring_x27(v___x_818_);
    return v___x_819_;
}
pub unsafe fn _init_l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__61()
-> *mut crate::leanh::LeanObject {
    let mut v___x_852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_852_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__60;
    v___x_853_ = l_String_toRawSubstring_x27(v___x_852_);
    return v___x_853_;
}
pub unsafe fn _init_l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__67()
-> *mut crate::leanh::LeanObject {
    let mut v___x_867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_867_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__66;
    v___x_868_ = l_String_toRawSubstring_x27(v___x_867_);
    return v___x_868_;
}
pub unsafe fn l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1(
    mut v_x_887_: *mut crate::leanh::LeanObject,
    mut v_a_888_: *mut crate::leanh::LeanObject,
    mut v_a_889_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_891_: u8 = 0;
    v___x_890_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__1;
    v___x_891_ = l_Lean_Syntax_isOfKind(v_x_887_, v___x_890_);
    if v___x_891_ == 0 {
        let mut v___x_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_892_ = crate::leanh::lean_box(1);
        v___x_893_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_893_, 0, v___x_892_);
        crate::leanh::lean_ctor_set(v___x_893_, 1, v_a_889_);
        return v___x_893_;
    } else {
        let mut v_quotContext_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_897_: u8 = 0;
        let mut v___x_898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
        v_quotContext_894_ = crate::leanh::lean_ctor_get(v_a_888_, 1);
        v_currMacroScope_895_ = crate::leanh::lean_ctor_get(v_a_888_, 2);
        v_ref_896_ = crate::leanh::lean_ctor_get(v_a_888_, 5);
        v___x_897_ = 0;
        v___x_898_ = l_Lean_SourceInfo_fromRef(v_ref_896_, v___x_897_);
        v___x_899_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__5;
        v___x_900_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__6;
        crate::leanh::lean_inc_n(v___x_898_, 50);
        v___x_901_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_901_, 0, v___x_898_);
        crate::leanh::lean_ctor_set(v___x_901_, 1, v___x_899_);
        v___x_902_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__8;
        v___x_903_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__10;
        v___x_904_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__11;
        v___x_905_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_905_, 0, v___x_898_);
        crate::leanh::lean_ctor_set(v___x_905_, 1, v___x_904_);
        v___x_906_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__13;
        v___x_907_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15;
        v___x_908_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__16;
        v___x_909_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17;
        v___x_910_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_910_, 0, v___x_898_);
        crate::leanh::lean_ctor_set(v___x_910_, 1, v___x_908_);
        v___x_911_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__20;
        v___x_912_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__22), core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__22_once), _init_l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__22);
        v___x_913_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__27;
        crate::leanh::lean_inc_n(v_currMacroScope_895_, 4);
        crate::leanh::lean_inc_n(v_quotContext_894_, 4);
        v___x_914_ = l_Lean_addMacroScope(v_quotContext_894_, v___x_913_, v_currMacroScope_895_);
        v___x_915_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__29;
        v___x_916_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_916_, 0, v___x_898_);
        crate::leanh::lean_ctor_set(v___x_916_, 1, v___x_912_);
        crate::leanh::lean_ctor_set(v___x_916_, 2, v___x_914_);
        crate::leanh::lean_ctor_set(v___x_916_, 3, v___x_915_);
        v___x_917_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__31;
        v___x_918_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__32;
        v___x_919_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_919_, 0, v___x_898_);
        crate::leanh::lean_ctor_set(v___x_919_, 1, v___x_918_);
        v___x_920_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__34;
        v___x_921_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__35;
        v___x_922_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_922_, 0, v___x_898_);
        crate::leanh::lean_ctor_set(v___x_922_, 1, v___x_921_);
        v___x_923_ = l_Lean_Syntax_node1(v___x_898_, v___x_920_, v___x_922_);
        v___x_924_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__36;
        v___x_925_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_925_, 0, v___x_898_);
        crate::leanh::lean_ctor_set(v___x_925_, 1, v___x_924_);
        v___x_926_ =
            l_Lean_Syntax_node3(v___x_898_, v___x_917_, v___x_919_, v___x_923_, v___x_925_);
        v___x_927_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__38;
        v___x_928_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__40;
        v___x_929_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__41;
        v___x_930_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_930_, 0, v___x_898_);
        crate::leanh::lean_ctor_set(v___x_930_, 1, v___x_929_);
        v___x_931_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__43;
        v___x_932_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__45), core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__45_once), _init_l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__45);
        v___x_933_ = crate::leanh::lean_box(0);
        v___x_934_ = l_Lean_addMacroScope(v_quotContext_894_, v___x_933_, v_currMacroScope_895_);
        v___x_935_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__52;
        v___x_936_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_936_, 0, v___x_898_);
        crate::leanh::lean_ctor_set(v___x_936_, 1, v___x_932_);
        crate::leanh::lean_ctor_set(v___x_936_, 2, v___x_934_);
        crate::leanh::lean_ctor_set(v___x_936_, 3, v___x_935_);
        v___x_937_ = l_Lean_Syntax_node1(v___x_898_, v___x_931_, v___x_936_);
        v___x_938_ = l_Lean_Syntax_node2(v___x_898_, v___x_928_, v___x_930_, v___x_937_);
        v___x_939_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__54;
        v___x_940_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__55;
        v___x_941_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_941_, 0, v___x_898_);
        crate::leanh::lean_ctor_set(v___x_941_, 1, v___x_940_);
        v___x_942_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__57;
        v___x_943_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__58;
        v___x_944_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_944_, 0, v___x_898_);
        crate::leanh::lean_ctor_set(v___x_944_, 1, v___x_943_);
        v___x_945_ = l_Lean_Syntax_node1(v___x_898_, v___x_942_, v___x_944_);
        v___x_946_ = l_Lean_Syntax_node1(v___x_898_, v___x_902_, v___x_945_);
        v___x_947_ = l_Lean_Syntax_node1(v___x_898_, v___x_907_, v___x_946_);
        v___x_948_ = l_Lean_Syntax_node1(v___x_898_, v___x_906_, v___x_947_);
        v___x_949_ = l_Lean_Syntax_node2(v___x_898_, v___x_939_, v___x_941_, v___x_948_);
        v___x_950_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__59;
        v___x_951_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_951_, 0, v___x_898_);
        crate::leanh::lean_ctor_set(v___x_951_, 1, v___x_950_);
        v___x_952_ =
            l_Lean_Syntax_node3(v___x_898_, v___x_927_, v___x_938_, v___x_949_, v___x_951_);
        v___x_953_ = l_Lean_Syntax_node2(v___x_898_, v___x_902_, v___x_926_, v___x_952_);
        crate::leanh::lean_inc_n(v___x_953_, 2);
        v___x_954_ = l_Lean_Syntax_node2(v___x_898_, v___x_911_, v___x_916_, v___x_953_);
        crate::leanh::lean_inc_ref_n(v___x_910_, 2);
        v___x_955_ = l_Lean_Syntax_node2(v___x_898_, v___x_909_, v___x_910_, v___x_954_);
        v___x_956_ = l_Lean_Syntax_node1(v___x_898_, v___x_902_, v___x_955_);
        v___x_957_ = l_Lean_Syntax_node1(v___x_898_, v___x_907_, v___x_956_);
        v___x_958_ = l_Lean_Syntax_node1(v___x_898_, v___x_906_, v___x_957_);
        crate::leanh::lean_inc_ref_n(v___x_905_, 3);
        v___x_959_ = l_Lean_Syntax_node2(v___x_898_, v___x_903_, v___x_905_, v___x_958_);
        v___x_960_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__61), core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__61_once), _init_l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__61);
        v___x_961_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__63;
        v___x_962_ = l_Lean_addMacroScope(v_quotContext_894_, v___x_961_, v_currMacroScope_895_);
        v___x_963_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__65;
        v___x_964_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_964_, 0, v___x_898_);
        crate::leanh::lean_ctor_set(v___x_964_, 1, v___x_960_);
        crate::leanh::lean_ctor_set(v___x_964_, 2, v___x_962_);
        crate::leanh::lean_ctor_set(v___x_964_, 3, v___x_963_);
        v___x_965_ = l_Lean_Syntax_node2(v___x_898_, v___x_911_, v___x_964_, v___x_953_);
        v___x_966_ = l_Lean_Syntax_node2(v___x_898_, v___x_909_, v___x_910_, v___x_965_);
        v___x_967_ = l_Lean_Syntax_node1(v___x_898_, v___x_902_, v___x_966_);
        v___x_968_ = l_Lean_Syntax_node1(v___x_898_, v___x_907_, v___x_967_);
        v___x_969_ = l_Lean_Syntax_node1(v___x_898_, v___x_906_, v___x_968_);
        v___x_970_ = l_Lean_Syntax_node2(v___x_898_, v___x_903_, v___x_905_, v___x_969_);
        v___x_971_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__67), core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__67_once), _init_l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__67);
        v___x_972_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__69;
        v___x_973_ = l_Lean_addMacroScope(v_quotContext_894_, v___x_972_, v_currMacroScope_895_);
        v___x_974_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__71;
        v___x_975_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_975_, 0, v___x_898_);
        crate::leanh::lean_ctor_set(v___x_975_, 1, v___x_971_);
        crate::leanh::lean_ctor_set(v___x_975_, 2, v___x_973_);
        crate::leanh::lean_ctor_set(v___x_975_, 3, v___x_974_);
        v___x_976_ = l_Lean_Syntax_node2(v___x_898_, v___x_911_, v___x_975_, v___x_953_);
        v___x_977_ = l_Lean_Syntax_node2(v___x_898_, v___x_909_, v___x_910_, v___x_976_);
        v___x_978_ = l_Lean_Syntax_node1(v___x_898_, v___x_902_, v___x_977_);
        v___x_979_ = l_Lean_Syntax_node1(v___x_898_, v___x_907_, v___x_978_);
        v___x_980_ = l_Lean_Syntax_node1(v___x_898_, v___x_906_, v___x_979_);
        v___x_981_ = l_Lean_Syntax_node2(v___x_898_, v___x_903_, v___x_905_, v___x_980_);
        v___x_982_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__72;
        v___x_983_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__73;
        v___x_984_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_984_, 0, v___x_898_);
        crate::leanh::lean_ctor_set(v___x_984_, 1, v___x_982_);
        v___x_985_ = l_Lean_Syntax_node1(v___x_898_, v___x_983_, v___x_984_);
        v___x_986_ = l_Lean_Syntax_node1(v___x_898_, v___x_902_, v___x_985_);
        v___x_987_ = l_Lean_Syntax_node1(v___x_898_, v___x_907_, v___x_986_);
        v___x_988_ = l_Lean_Syntax_node1(v___x_898_, v___x_906_, v___x_987_);
        v___x_989_ = l_Lean_Syntax_node2(v___x_898_, v___x_903_, v___x_905_, v___x_988_);
        v___x_990_ = l_Lean_Syntax_node4(
            v___x_898_, v___x_902_, v___x_959_, v___x_970_, v___x_981_, v___x_989_,
        );
        v___x_991_ = l_Lean_Syntax_node2(v___x_898_, v___x_900_, v___x_901_, v___x_990_);
        v___x_992_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_992_, 0, v___x_991_);
        crate::leanh::lean_ctor_set(v___x_992_, 1, v_a_889_);
        return v___x_992_;
    }
}
pub unsafe fn l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___boxed(
    mut v_x_993_: *mut crate::leanh::LeanObject,
    mut v_a_994_: *mut crate::leanh::LeanObject,
    mut v_a_995_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_996_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1(v_x_993_, v_a_994_, v_a_995_);
    crate::leanh::lean_dec_ref(v_a_994_);
    return v_res_996_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Range_Polymorphic_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Range_Polymorphic_PRange(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Instances(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Range_Polymorphic_Basic(
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
pub unsafe fn initialize_Init_Data_Range_Polymorphic_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Range_Polymorphic_PRange(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Instances(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Range_Polymorphic_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Range_Polymorphic_Basic(builtin);
}
