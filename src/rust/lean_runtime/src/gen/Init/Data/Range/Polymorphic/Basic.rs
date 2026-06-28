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
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr4, l_Lean_SourceInfo_fromRef,
    l_Lean_Syntax_isOfKind, l_Lean_Syntax_node1, l_Lean_Syntax_node2, l_Lean_Syntax_node3,
    l_Lean_Syntax_node4, l_Lean_addMacroScope, l_String_toRawSubstring_x27,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_once, lean_obj_tag, lean_unbox,
};
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__0_value: LeanStringObject<33> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [116, 97, 99, 116, 105, 99, 71, 101, 116, 95, 101, 108, 101, 109, 95, 116, 97, 99, 116, 105, 99, 95, 101, 120, 116, 101, 110, 115, 105, 98, 108, 101, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__0_value) as *mut LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__0_value) as *mut LeanObject,7705027380931481693 as *mut LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__1_value) as *mut LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value) as *mut LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value) as *mut LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value) as *mut LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__5_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [102, 105, 114, 115, 116, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__5_value) as *mut LeanObject;
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__6_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__6_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__6_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__6_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__6_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__6_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__5_value) as *mut LeanObject,12551601070224435259 as *mut LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__6_value) as *mut LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__7_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__7: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__7_value) as *mut LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__7_value) as *mut LeanObject,9855511589286918680 as *mut LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__8_value) as *mut LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__9_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [103, 114, 111, 117, 112, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__9: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__9_value) as *mut LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__10_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__9_value) as *mut LeanObject,2214559063752339918 as *mut LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__10_value) as *mut LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__11_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [124, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__11: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__11_value) as *mut LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__12_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__12_value) as *mut LeanObject;
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__13_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__13_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__13_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__13_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__13_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__13_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__13_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__12_value) as *mut LeanObject,8504843326314613972 as *mut LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__13: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__13_value) as *mut LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__14_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__14: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__14_value) as *mut LeanObject;
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__14_value) as *mut LeanObject,17228437386856258271 as *mut LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value) as *mut LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__16_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [97, 112, 112, 108, 121, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__16: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__16_value) as *mut LeanObject;
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__16_value) as *mut LeanObject,5826123769708379594 as *mut LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17_value) as *mut LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__18_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__18: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__18_value) as *mut LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__19_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__19: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__19_value) as *mut LeanObject;
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__20_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__20_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__20_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__20_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__20_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__18_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__20_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__20_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__19_value) as *mut LeanObject,12966880221525079621 as *mut LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__20: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__20_value) as *mut LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__21_value: LeanStringObject<44> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 44, m_capacity: 44, m_length: 43, m_data: [83, 116, 100, 46, 82, 99, 111, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 103, 101, 116, 95, 101, 108, 101, 109, 95, 104, 101, 108, 112, 101, 114, 95, 117, 112, 112, 101, 114, 95, 111, 112, 101, 110, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__21: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__21_value) as *mut LeanObject;
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__22_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__22: *mut LeanObject = core::ptr::null_mut();
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__23_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [83, 116, 100, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__23: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__23_value) as *mut LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__24_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [82, 99, 111, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__24: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__24_value) as *mut LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__25_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [73, 110, 116, 101, 114, 110, 97, 108, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__25: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__25_value) as *mut LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__26_value: LeanStringObject<27> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [103, 101, 116, 95, 101, 108, 101, 109, 95, 104, 101, 108, 112, 101, 114, 95, 117, 112, 112, 101, 114, 95, 111, 112, 101, 110, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__26: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__26_value) as *mut LeanObject;
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__27_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__23_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__27_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__27_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__24_value) as *mut LeanObject,36003929318889298 as *mut LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__27_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__27_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__25_value) as *mut LeanObject,8015440497992668395 as *mut LeanObject] };
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__27_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__27_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__26_value) as *mut LeanObject,8588407234422212448 as *mut LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__27: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__27_value) as *mut LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__28_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__27_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__28: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__28_value) as *mut LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__29_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__28_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__29: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__29_value) as *mut LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__30_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 7, m_data: [116, 101, 114, 109, 226, 128, 185, 95, 226, 128, 186, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__30: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__30_value) as *mut LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__31_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__30_value) as *mut LeanObject,8315864120963730325 as *mut LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__31: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__31_value) as *mut LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__32_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 128, 185, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__32: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__32_value) as *mut LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__33_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 111, 108, 101, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__33: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__33_value) as *mut LeanObject;
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__34_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__34_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__34_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__34_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__34_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__18_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__34_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__34_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__33_value) as *mut LeanObject,3984140175429830279 as *mut LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__34: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__34_value) as *mut LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__35_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [95, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__35: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__35_value) as *mut LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__36_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 128, 186, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__36: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__36_value) as *mut LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__37_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [112, 97, 114, 101, 110, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__37: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__37_value) as *mut LeanObject;
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__38_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__38_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__38_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__38_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__38_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__18_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__38_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__38_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__37_value) as *mut LeanObject,7932075773091973500 as *mut LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__38: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__38_value) as *mut LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__39_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [104, 121, 103, 105, 101, 110, 105, 99, 76, 80, 97, 114, 101, 110, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__39: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__39_value) as *mut LeanObject;
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__40_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__40_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__40_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__40_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__40_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__18_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__40_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__40_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__39_value) as *mut LeanObject,7306243862518720553 as *mut LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__40: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__40_value) as *mut LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__41_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__41: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__41_value) as *mut LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__42_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__42: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__42_value) as *mut LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__43_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__42_value) as *mut LeanObject,9871775667037945883 as *mut LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__43: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__43_value) as *mut LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__44_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__44: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__44_value) as *mut LeanObject;
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__45_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__45: *mut LeanObject = core::ptr::null_mut();
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__46_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__23_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__46: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__46_value) as *mut LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__47_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__46_value) as *mut LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__47: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__47_value) as *mut LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__48_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 82, 97, 110, 103, 101, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__48: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__48_value) as *mut LeanObject;
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__49_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__23_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__49_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__49_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__48_value) as *mut LeanObject,9849097416327629642 as *mut LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__49: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__49_value) as *mut LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__50_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__49_value) as *mut LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__50: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__50_value) as *mut LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__51_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__50_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__51: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__51_value) as *mut LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__52_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__47_value) as *mut LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__51_value) as *mut LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__52: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__52_value) as *mut LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__53_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [98, 121, 84, 97, 99, 116, 105, 99, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__53: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__53_value) as *mut LeanObject;
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__54_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__54_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__54_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__54_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__54_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__18_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__54_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__54_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__53_value) as *mut LeanObject,16173796135615239867 as *mut LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__54: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__54_value) as *mut LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__55_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [98, 121, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__55: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__55_value) as *mut LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__56_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [116, 97, 99, 116, 105, 99, 84, 114, 105, 118, 105, 97, 108, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__56: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__56_value) as *mut LeanObject;
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__57_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__57_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__57_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__57_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__57_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__57_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__57_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__56_value) as *mut LeanObject,2766452847008772443 as *mut LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__57: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__57_value) as *mut LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__58_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [116, 114, 105, 118, 105, 97, 108, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__58: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__58_value) as *mut LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__59_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__59: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__59_value) as *mut LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__60_value: LeanStringObject<44> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 44, m_capacity: 44, m_length: 43, m_data: [83, 116, 100, 46, 82, 111, 111, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 103, 101, 116, 95, 101, 108, 101, 109, 95, 104, 101, 108, 112, 101, 114, 95, 117, 112, 112, 101, 114, 95, 111, 112, 101, 110, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__60: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__60_value) as *mut LeanObject;
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__61_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__61: *mut LeanObject = core::ptr::null_mut();
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__62_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [82, 111, 111, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__62: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__62_value) as *mut LeanObject;
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__63_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__23_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__63_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__63_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__62_value) as *mut LeanObject,17971250720669795982 as *mut LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__63_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__63_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__25_value) as *mut LeanObject,17821413486542541535 as *mut LeanObject] };
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__63_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__63_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__26_value) as *mut LeanObject,13586587588939731556 as *mut LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__63: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__63_value) as *mut LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__64_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__63_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__64: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__64_value) as *mut LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__65_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__64_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__65: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__65_value) as *mut LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__66_value: LeanStringObject<44> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 44, m_capacity: 44, m_length: 43, m_data: [83, 116, 100, 46, 82, 105, 111, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 103, 101, 116, 95, 101, 108, 101, 109, 95, 104, 101, 108, 112, 101, 114, 95, 117, 112, 112, 101, 114, 95, 111, 112, 101, 110, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__66: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__66_value) as *mut LeanObject;
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__67_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__67: *mut LeanObject = core::ptr::null_mut();
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__68_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [82, 105, 111, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__68: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__68_value) as *mut LeanObject;
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__69_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__23_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__69_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__69_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__68_value) as *mut LeanObject,10504416010916204673 as *mut LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__69_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__69_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__25_value) as *mut LeanObject,14499228462873218844 as *mut LeanObject] };
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__69_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__69_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__26_value) as *mut LeanObject,9086931729220931171 as *mut LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__69: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__69_value) as *mut LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__70_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__69_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__70: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__70_value) as *mut LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__71_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__70_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__71: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__71_value) as *mut LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__72_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [100, 111, 110, 101, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__72: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__72_value) as *mut LeanObject;
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__73_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__73_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__73_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__73_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__73_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__73_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__73_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__72_value) as *mut LeanObject,8876691400619696497 as *mut LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__73: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__73_value) as *mut LeanObject;
pub unsafe fn l_Std_Rcc_isEmpty___redArg(
    mut v_inst_499_: *mut LeanObject,
    mut v_r_500_: *mut LeanObject,
) -> u8 {
    let mut v_lower_501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_504_: u8 = 0;
    v_lower_501_ = lean_ctor_get(v_r_500_, 0);
    lean_inc(v_lower_501_);
    v_upper_502_ = lean_ctor_get(v_r_500_, 1);
    lean_inc(v_upper_502_);
    lean_dec_ref(v_r_500_);
    v___x_503_ = lean_apply_2(v_inst_499_, v_lower_501_, v_upper_502_);
    v___x_504_ = (lean_unbox(v___x_503_) as u8);
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
    mut v_inst_507_: *mut LeanObject,
    mut v_r_508_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_509_: u8 = 0;
    let mut v_r_510_: *mut LeanObject = core::ptr::null_mut();
    v_res_509_ = l_Std_Rcc_isEmpty___redArg(v_inst_507_, v_r_508_);
    v_r_510_ = lean_box((v_res_509_) as usize);
    return v_r_510_;
}
pub unsafe fn l_Std_Rcc_isEmpty(
    mut v_00_u03b1_511_: *mut LeanObject,
    mut v_inst_512_: *mut LeanObject,
    mut v_inst_513_: *mut LeanObject,
    mut v_inst_514_: *mut LeanObject,
    mut v_r_515_: *mut LeanObject,
) -> u8 {
    let mut v_lower_516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_519_: u8 = 0;
    v_lower_516_ = lean_ctor_get(v_r_515_, 0);
    lean_inc(v_lower_516_);
    v_upper_517_ = lean_ctor_get(v_r_515_, 1);
    lean_inc(v_upper_517_);
    lean_dec_ref(v_r_515_);
    v___x_518_ = lean_apply_2(v_inst_513_, v_lower_516_, v_upper_517_);
    v___x_519_ = (lean_unbox(v___x_518_) as u8);
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
    mut v_00_u03b1_522_: *mut LeanObject,
    mut v_inst_523_: *mut LeanObject,
    mut v_inst_524_: *mut LeanObject,
    mut v_inst_525_: *mut LeanObject,
    mut v_r_526_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_527_: u8 = 0;
    let mut v_r_528_: *mut LeanObject = core::ptr::null_mut();
    v_res_527_ = l_Std_Rcc_isEmpty(
        v_00_u03b1_522_,
        v_inst_523_,
        v_inst_524_,
        v_inst_525_,
        v_r_526_,
    );
    lean_dec_ref(v_inst_525_);
    v_r_528_ = lean_box((v_res_527_) as usize);
    return v_r_528_;
}
pub unsafe fn l_Std_Rco_isEmpty___redArg(
    mut v_inst_529_: *mut LeanObject,
    mut v_r_530_: *mut LeanObject,
) -> u8 {
    let mut v_lower_531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_534_: u8 = 0;
    v_lower_531_ = lean_ctor_get(v_r_530_, 0);
    lean_inc(v_lower_531_);
    v_upper_532_ = lean_ctor_get(v_r_530_, 1);
    lean_inc(v_upper_532_);
    lean_dec_ref(v_r_530_);
    v___x_533_ = lean_apply_2(v_inst_529_, v_lower_531_, v_upper_532_);
    v___x_534_ = (lean_unbox(v___x_533_) as u8);
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
    mut v_inst_537_: *mut LeanObject,
    mut v_r_538_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_539_: u8 = 0;
    let mut v_r_540_: *mut LeanObject = core::ptr::null_mut();
    v_res_539_ = l_Std_Rco_isEmpty___redArg(v_inst_537_, v_r_538_);
    v_r_540_ = lean_box((v_res_539_) as usize);
    return v_r_540_;
}
pub unsafe fn l_Std_Rco_isEmpty(
    mut v_00_u03b1_541_: *mut LeanObject,
    mut v_inst_542_: *mut LeanObject,
    mut v_inst_543_: *mut LeanObject,
    mut v_inst_544_: *mut LeanObject,
    mut v_r_545_: *mut LeanObject,
) -> u8 {
    let mut v_lower_546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_549_: u8 = 0;
    v_lower_546_ = lean_ctor_get(v_r_545_, 0);
    lean_inc(v_lower_546_);
    v_upper_547_ = lean_ctor_get(v_r_545_, 1);
    lean_inc(v_upper_547_);
    lean_dec_ref(v_r_545_);
    v___x_548_ = lean_apply_2(v_inst_543_, v_lower_546_, v_upper_547_);
    v___x_549_ = (lean_unbox(v___x_548_) as u8);
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
    mut v_00_u03b1_552_: *mut LeanObject,
    mut v_inst_553_: *mut LeanObject,
    mut v_inst_554_: *mut LeanObject,
    mut v_inst_555_: *mut LeanObject,
    mut v_r_556_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_557_: u8 = 0;
    let mut v_r_558_: *mut LeanObject = core::ptr::null_mut();
    v_res_557_ = l_Std_Rco_isEmpty(
        v_00_u03b1_552_,
        v_inst_553_,
        v_inst_554_,
        v_inst_555_,
        v_r_556_,
    );
    lean_dec_ref(v_inst_555_);
    v_r_558_ = lean_box((v_res_557_) as usize);
    return v_r_558_;
}
pub unsafe fn l_Std_Rci_isEmpty(
    mut v_00_u03b1_559_: *mut LeanObject,
    mut v_inst_560_: *mut LeanObject,
    mut v_x_561_: *mut LeanObject,
) -> u8 {
    let mut v___x_562_: u8 = 0;
    v___x_562_ = 0;
    return v___x_562_;
}
pub unsafe fn l_Std_Rci_isEmpty___boxed(
    mut v_00_u03b1_563_: *mut LeanObject,
    mut v_inst_564_: *mut LeanObject,
    mut v_x_565_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_566_: u8 = 0;
    let mut v_r_567_: *mut LeanObject = core::ptr::null_mut();
    v_res_566_ = l_Std_Rci_isEmpty(v_00_u03b1_563_, v_inst_564_, v_x_565_);
    lean_dec(v_x_565_);
    lean_dec_ref(v_inst_564_);
    v_r_567_ = lean_box((v_res_566_) as usize);
    return v_r_567_;
}
pub unsafe fn l_Std_Roc_isEmpty___redArg(
    mut v_inst_568_: *mut LeanObject,
    mut v_r_569_: *mut LeanObject,
) -> u8 {
    let mut v_lower_570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_573_: u8 = 0;
    v_lower_570_ = lean_ctor_get(v_r_569_, 0);
    lean_inc(v_lower_570_);
    v_upper_571_ = lean_ctor_get(v_r_569_, 1);
    lean_inc(v_upper_571_);
    lean_dec_ref(v_r_569_);
    v___x_572_ = lean_apply_2(v_inst_568_, v_lower_570_, v_upper_571_);
    v___x_573_ = (lean_unbox(v___x_572_) as u8);
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
    mut v_inst_576_: *mut LeanObject,
    mut v_r_577_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_578_: u8 = 0;
    let mut v_r_579_: *mut LeanObject = core::ptr::null_mut();
    v_res_578_ = l_Std_Roc_isEmpty___redArg(v_inst_576_, v_r_577_);
    v_r_579_ = lean_box((v_res_578_) as usize);
    return v_r_579_;
}
pub unsafe fn l_Std_Roc_isEmpty(
    mut v_00_u03b1_580_: *mut LeanObject,
    mut v_inst_581_: *mut LeanObject,
    mut v_inst_582_: *mut LeanObject,
    mut v_inst_583_: *mut LeanObject,
    mut v_r_584_: *mut LeanObject,
) -> u8 {
    let mut v_lower_585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_588_: u8 = 0;
    v_lower_585_ = lean_ctor_get(v_r_584_, 0);
    lean_inc(v_lower_585_);
    v_upper_586_ = lean_ctor_get(v_r_584_, 1);
    lean_inc(v_upper_586_);
    lean_dec_ref(v_r_584_);
    v___x_587_ = lean_apply_2(v_inst_582_, v_lower_585_, v_upper_586_);
    v___x_588_ = (lean_unbox(v___x_587_) as u8);
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
    mut v_00_u03b1_591_: *mut LeanObject,
    mut v_inst_592_: *mut LeanObject,
    mut v_inst_593_: *mut LeanObject,
    mut v_inst_594_: *mut LeanObject,
    mut v_r_595_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_596_: u8 = 0;
    let mut v_r_597_: *mut LeanObject = core::ptr::null_mut();
    v_res_596_ = l_Std_Roc_isEmpty(
        v_00_u03b1_591_,
        v_inst_592_,
        v_inst_593_,
        v_inst_594_,
        v_r_595_,
    );
    lean_dec_ref(v_inst_594_);
    v_r_597_ = lean_box((v_res_596_) as usize);
    return v_r_597_;
}
pub unsafe fn l_Std_Roo_isEmpty___redArg___lam__0(
    mut v_inst_598_: *mut LeanObject,
    mut v_upper_599_: *mut LeanObject,
    mut v_a_600_: *mut LeanObject,
) -> u8 {
    let mut v___x_601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_602_: u8 = 0;
    v___x_601_ = lean_apply_2(v_inst_598_, v_a_600_, v_upper_599_);
    v___x_602_ = (lean_unbox(v___x_601_) as u8);
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
    mut v_inst_605_: *mut LeanObject,
    mut v_upper_606_: *mut LeanObject,
    mut v_a_607_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_608_: u8 = 0;
    let mut v_r_609_: *mut LeanObject = core::ptr::null_mut();
    v_res_608_ = l_Std_Roo_isEmpty___redArg___lam__0(v_inst_605_, v_upper_606_, v_a_607_);
    v_r_609_ = lean_box((v_res_608_) as usize);
    return v_r_609_;
}
pub unsafe fn l_Std_Roo_isEmpty___redArg(
    mut v_inst_610_: *mut LeanObject,
    mut v_inst_611_: *mut LeanObject,
    mut v_r_612_: *mut LeanObject,
) -> u8 {
    let mut v_succ_x3f_613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lower_614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_618_: u8 = 0;
    v_succ_x3f_613_ = lean_ctor_get(v_inst_611_, 0);
    lean_inc_ref(v_succ_x3f_613_);
    lean_dec_ref(v_inst_611_);
    v_lower_614_ = lean_ctor_get(v_r_612_, 0);
    lean_inc(v_lower_614_);
    v_upper_615_ = lean_ctor_get(v_r_612_, 1);
    lean_inc(v_upper_615_);
    lean_dec_ref(v_r_612_);
    v___f_616_ = lean_alloc_closure(
        l_Std_Roo_isEmpty___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_616_, 0, v_inst_610_);
    lean_closure_set(v___f_616_, 1, v_upper_615_);
    v___x_617_ = lean_apply_1(v_succ_x3f_613_, v_lower_614_);
    v___x_618_ = l_Option_decidableForallMem___redArg(v___f_616_, v___x_617_);
    return v___x_618_;
}
pub unsafe fn l_Std_Roo_isEmpty___redArg___boxed(
    mut v_inst_619_: *mut LeanObject,
    mut v_inst_620_: *mut LeanObject,
    mut v_r_621_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_622_: u8 = 0;
    let mut v_r_623_: *mut LeanObject = core::ptr::null_mut();
    v_res_622_ = l_Std_Roo_isEmpty___redArg(v_inst_619_, v_inst_620_, v_r_621_);
    v_r_623_ = lean_box((v_res_622_) as usize);
    return v_r_623_;
}
pub unsafe fn l_Std_Roo_isEmpty(
    mut v_00_u03b1_624_: *mut LeanObject,
    mut v_inst_625_: *mut LeanObject,
    mut v_inst_626_: *mut LeanObject,
    mut v_inst_627_: *mut LeanObject,
    mut v_r_628_: *mut LeanObject,
) -> u8 {
    let mut v_succ_x3f_629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lower_630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_634_: u8 = 0;
    v_succ_x3f_629_ = lean_ctor_get(v_inst_627_, 0);
    lean_inc_ref(v_succ_x3f_629_);
    lean_dec_ref(v_inst_627_);
    v_lower_630_ = lean_ctor_get(v_r_628_, 0);
    lean_inc(v_lower_630_);
    v_upper_631_ = lean_ctor_get(v_r_628_, 1);
    lean_inc(v_upper_631_);
    lean_dec_ref(v_r_628_);
    v___f_632_ = lean_alloc_closure(
        l_Std_Roo_isEmpty___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_632_, 0, v_inst_626_);
    lean_closure_set(v___f_632_, 1, v_upper_631_);
    v___x_633_ = lean_apply_1(v_succ_x3f_629_, v_lower_630_);
    v___x_634_ = l_Option_decidableForallMem___redArg(v___f_632_, v___x_633_);
    return v___x_634_;
}
pub unsafe fn l_Std_Roo_isEmpty___boxed(
    mut v_00_u03b1_635_: *mut LeanObject,
    mut v_inst_636_: *mut LeanObject,
    mut v_inst_637_: *mut LeanObject,
    mut v_inst_638_: *mut LeanObject,
    mut v_r_639_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_640_: u8 = 0;
    let mut v_r_641_: *mut LeanObject = core::ptr::null_mut();
    v_res_640_ = l_Std_Roo_isEmpty(
        v_00_u03b1_635_,
        v_inst_636_,
        v_inst_637_,
        v_inst_638_,
        v_r_639_,
    );
    v_r_641_ = lean_box((v_res_640_) as usize);
    return v_r_641_;
}
pub unsafe fn l_Std_Roi_isEmpty___redArg(
    mut v_inst_642_: *mut LeanObject,
    mut v_r_643_: *mut LeanObject,
) -> u8 {
    let mut v_succ_x3f_644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_645_: *mut LeanObject = core::ptr::null_mut();
    v_succ_x3f_644_ = lean_ctor_get(v_inst_642_, 0);
    lean_inc_ref(v_succ_x3f_644_);
    lean_dec_ref(v_inst_642_);
    v___x_645_ = lean_apply_1(v_succ_x3f_644_, v_r_643_);
    if lean_obj_tag(v___x_645_) == 0 {
        let mut v___x_646_: u8 = 0;
        v___x_646_ = 1;
        return v___x_646_;
    } else {
        let mut v___x_647_: u8 = 0;
        lean_dec_ref_known(v___x_645_, 1);
        v___x_647_ = 0;
        return v___x_647_;
    }
}
pub unsafe fn l_Std_Roi_isEmpty___redArg___boxed(
    mut v_inst_648_: *mut LeanObject,
    mut v_r_649_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_650_: u8 = 0;
    let mut v_r_651_: *mut LeanObject = core::ptr::null_mut();
    v_res_650_ = l_Std_Roi_isEmpty___redArg(v_inst_648_, v_r_649_);
    v_r_651_ = lean_box((v_res_650_) as usize);
    return v_r_651_;
}
pub unsafe fn l_Std_Roi_isEmpty(
    mut v_00_u03b1_652_: *mut LeanObject,
    mut v_inst_653_: *mut LeanObject,
    mut v_r_654_: *mut LeanObject,
) -> u8 {
    let mut v_succ_x3f_655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_656_: *mut LeanObject = core::ptr::null_mut();
    v_succ_x3f_655_ = lean_ctor_get(v_inst_653_, 0);
    lean_inc_ref(v_succ_x3f_655_);
    lean_dec_ref(v_inst_653_);
    v___x_656_ = lean_apply_1(v_succ_x3f_655_, v_r_654_);
    if lean_obj_tag(v___x_656_) == 0 {
        let mut v___x_657_: u8 = 0;
        v___x_657_ = 1;
        return v___x_657_;
    } else {
        let mut v___x_658_: u8 = 0;
        lean_dec_ref_known(v___x_656_, 1);
        v___x_658_ = 0;
        return v___x_658_;
    }
}
pub unsafe fn l_Std_Roi_isEmpty___boxed(
    mut v_00_u03b1_659_: *mut LeanObject,
    mut v_inst_660_: *mut LeanObject,
    mut v_r_661_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_662_: u8 = 0;
    let mut v_r_663_: *mut LeanObject = core::ptr::null_mut();
    v_res_662_ = l_Std_Roi_isEmpty(v_00_u03b1_659_, v_inst_660_, v_r_661_);
    v_r_663_ = lean_box((v_res_662_) as usize);
    return v_r_663_;
}
pub unsafe fn l_Std_Ric_isEmpty(
    mut v_00_u03b1_664_: *mut LeanObject,
    mut v_inst_665_: *mut LeanObject,
    mut v_x_666_: *mut LeanObject,
) -> u8 {
    let mut v___x_667_: u8 = 0;
    v___x_667_ = 0;
    return v___x_667_;
}
pub unsafe fn l_Std_Ric_isEmpty___boxed(
    mut v_00_u03b1_668_: *mut LeanObject,
    mut v_inst_669_: *mut LeanObject,
    mut v_x_670_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_671_: u8 = 0;
    let mut v_r_672_: *mut LeanObject = core::ptr::null_mut();
    v_res_671_ = l_Std_Ric_isEmpty(v_00_u03b1_668_, v_inst_669_, v_x_670_);
    lean_dec(v_x_670_);
    lean_dec_ref(v_inst_669_);
    v_r_672_ = lean_box((v_res_671_) as usize);
    return v_r_672_;
}
pub unsafe fn l_Std_Rio_isEmpty___redArg___lam__0(
    mut v_inst_673_: *mut LeanObject,
    mut v_r_674_: *mut LeanObject,
    mut v_a_675_: *mut LeanObject,
) -> u8 {
    let mut v___x_676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_677_: u8 = 0;
    v___x_676_ = lean_apply_2(v_inst_673_, v_a_675_, v_r_674_);
    v___x_677_ = (lean_unbox(v___x_676_) as u8);
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
    mut v_inst_680_: *mut LeanObject,
    mut v_r_681_: *mut LeanObject,
    mut v_a_682_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_683_: u8 = 0;
    let mut v_r_684_: *mut LeanObject = core::ptr::null_mut();
    v_res_683_ = l_Std_Rio_isEmpty___redArg___lam__0(v_inst_680_, v_r_681_, v_a_682_);
    v_r_684_ = lean_box((v_res_683_) as usize);
    return v_r_684_;
}
pub unsafe fn l_Std_Rio_isEmpty___redArg(
    mut v_inst_685_: *mut LeanObject,
    mut v_inst_686_: *mut LeanObject,
    mut v_r_687_: *mut LeanObject,
) -> u8 {
    let mut v___f_688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_689_: u8 = 0;
    v___f_688_ = lean_alloc_closure(
        l_Std_Rio_isEmpty___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_688_, 0, v_inst_685_);
    lean_closure_set(v___f_688_, 1, v_r_687_);
    v___x_689_ = l_Option_decidableForallMem___redArg(v___f_688_, v_inst_686_);
    return v___x_689_;
}
pub unsafe fn l_Std_Rio_isEmpty___redArg___boxed(
    mut v_inst_690_: *mut LeanObject,
    mut v_inst_691_: *mut LeanObject,
    mut v_r_692_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_693_: u8 = 0;
    let mut v_r_694_: *mut LeanObject = core::ptr::null_mut();
    v_res_693_ = l_Std_Rio_isEmpty___redArg(v_inst_690_, v_inst_691_, v_r_692_);
    v_r_694_ = lean_box((v_res_693_) as usize);
    return v_r_694_;
}
pub unsafe fn l_Std_Rio_isEmpty(
    mut v_00_u03b1_695_: *mut LeanObject,
    mut v_inst_696_: *mut LeanObject,
    mut v_inst_697_: *mut LeanObject,
    mut v_inst_698_: *mut LeanObject,
    mut v_inst_699_: *mut LeanObject,
    mut v_r_700_: *mut LeanObject,
) -> u8 {
    let mut v___f_701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_702_: u8 = 0;
    v___f_701_ = lean_alloc_closure(
        l_Std_Rio_isEmpty___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_701_, 0, v_inst_697_);
    lean_closure_set(v___f_701_, 1, v_r_700_);
    v___x_702_ = l_Option_decidableForallMem___redArg(v___f_701_, v_inst_699_);
    return v___x_702_;
}
pub unsafe fn l_Std_Rio_isEmpty___boxed(
    mut v_00_u03b1_703_: *mut LeanObject,
    mut v_inst_704_: *mut LeanObject,
    mut v_inst_705_: *mut LeanObject,
    mut v_inst_706_: *mut LeanObject,
    mut v_inst_707_: *mut LeanObject,
    mut v_r_708_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_709_: u8 = 0;
    let mut v_r_710_: *mut LeanObject = core::ptr::null_mut();
    v_res_709_ = l_Std_Rio_isEmpty(
        v_00_u03b1_703_,
        v_inst_704_,
        v_inst_705_,
        v_inst_706_,
        v_inst_707_,
        v_r_708_,
    );
    lean_dec_ref(v_inst_706_);
    v_r_710_ = lean_box((v_res_709_) as usize);
    return v_r_710_;
}
pub unsafe fn l_Std_Rii_isEmpty___redArg(mut v_inst_711_: *mut LeanObject) -> u8 {
    if lean_obj_tag(v_inst_711_) == 0 {
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
    mut v_inst_714_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_715_: u8 = 0;
    let mut v_r_716_: *mut LeanObject = core::ptr::null_mut();
    v_res_715_ = l_Std_Rii_isEmpty___redArg(v_inst_714_);
    lean_dec(v_inst_714_);
    v_r_716_ = lean_box((v_res_715_) as usize);
    return v_r_716_;
}
pub unsafe fn l_Std_Rii_isEmpty(
    mut v_00_u03b1_717_: *mut LeanObject,
    mut v_inst_718_: *mut LeanObject,
    mut v_x_719_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_inst_718_) == 0 {
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
    mut v_00_u03b1_722_: *mut LeanObject,
    mut v_inst_723_: *mut LeanObject,
    mut v_x_724_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_725_: u8 = 0;
    let mut v_r_726_: *mut LeanObject = core::ptr::null_mut();
    v_res_725_ = l_Std_Rii_isEmpty(v_00_u03b1_722_, v_inst_723_, v_x_724_);
    lean_dec(v_inst_723_);
    v_r_726_ = lean_box((v_res_725_) as usize);
    return v_r_726_;
}
pub unsafe fn _init_l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__22()
-> *mut LeanObject {
    let mut v___x_772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_773_: *mut LeanObject = core::ptr::null_mut();
    v___x_772_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__21;
    v___x_773_ = l_String_toRawSubstring_x27(v___x_772_);
    return v___x_773_;
}
pub unsafe fn _init_l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__45()
-> *mut LeanObject {
    let mut v___x_818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_819_: *mut LeanObject = core::ptr::null_mut();
    v___x_818_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__44;
    v___x_819_ = l_String_toRawSubstring_x27(v___x_818_);
    return v___x_819_;
}
pub unsafe fn _init_l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__61()
-> *mut LeanObject {
    let mut v___x_852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_853_: *mut LeanObject = core::ptr::null_mut();
    v___x_852_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__60;
    v___x_853_ = l_String_toRawSubstring_x27(v___x_852_);
    return v___x_853_;
}
pub unsafe fn _init_l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__67()
-> *mut LeanObject {
    let mut v___x_867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_868_: *mut LeanObject = core::ptr::null_mut();
    v___x_867_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__66;
    v___x_868_ = l_String_toRawSubstring_x27(v___x_867_);
    return v___x_868_;
}
pub unsafe fn l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1(
    mut v_x_887_: *mut LeanObject,
    mut v_a_888_: *mut LeanObject,
    mut v_a_889_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_891_: u8 = 0;
    v___x_890_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__1;
    v___x_891_ = l_Lean_Syntax_isOfKind(v_x_887_, v___x_890_);
    if v___x_891_ == 0 {
        let mut v___x_892_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_893_: *mut LeanObject = core::ptr::null_mut();
        v___x_892_ = lean_box(1);
        v___x_893_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_893_, 0, v___x_892_);
        lean_ctor_set(v___x_893_, 1, v_a_889_);
        return v___x_893_;
    } else {
        let mut v_quotContext_894_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_895_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_896_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_897_: u8 = 0;
        let mut v___x_898_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_899_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_900_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_901_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_902_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_903_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_904_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_905_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_906_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_907_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_908_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_909_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_910_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_911_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_912_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_913_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_914_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_915_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_916_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_917_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_918_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_919_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_920_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_921_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_922_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_923_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_924_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_925_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_926_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_927_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_928_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_929_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_930_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_931_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_932_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_933_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_934_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_935_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_936_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_937_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_938_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_939_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_940_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_941_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_942_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_943_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_944_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_945_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_946_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_947_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_948_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_949_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_950_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_951_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_952_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_953_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_954_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_955_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_956_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_957_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_958_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_959_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_960_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_961_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_962_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_963_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_964_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_965_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_966_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_967_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_968_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_969_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_970_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_971_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_972_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_973_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_974_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_975_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_976_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_977_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_978_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_979_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_980_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_981_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_982_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_983_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_984_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_985_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_986_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_987_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_988_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_989_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_990_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_991_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_992_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_894_ = lean_ctor_get(v_a_888_, 1);
        v_currMacroScope_895_ = lean_ctor_get(v_a_888_, 2);
        v_ref_896_ = lean_ctor_get(v_a_888_, 5);
        v___x_897_ = 0;
        v___x_898_ = l_Lean_SourceInfo_fromRef(v_ref_896_, v___x_897_);
        v___x_899_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__5;
        v___x_900_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__6;
        lean_inc_n(v___x_898_, 50);
        v___x_901_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_901_, 0, v___x_898_);
        lean_ctor_set(v___x_901_, 1, v___x_899_);
        v___x_902_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__8;
        v___x_903_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__10;
        v___x_904_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__11;
        v___x_905_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_905_, 0, v___x_898_);
        lean_ctor_set(v___x_905_, 1, v___x_904_);
        v___x_906_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__13;
        v___x_907_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15;
        v___x_908_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__16;
        v___x_909_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17;
        v___x_910_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_910_, 0, v___x_898_);
        lean_ctor_set(v___x_910_, 1, v___x_908_);
        v___x_911_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__20;
        v___x_912_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__22), core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__22_once), _init_l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__22);
        v___x_913_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__27;
        lean_inc_n(v_currMacroScope_895_, 4);
        lean_inc_n(v_quotContext_894_, 4);
        v___x_914_ = l_Lean_addMacroScope(v_quotContext_894_, v___x_913_, v_currMacroScope_895_);
        v___x_915_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__29;
        v___x_916_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_916_, 0, v___x_898_);
        lean_ctor_set(v___x_916_, 1, v___x_912_);
        lean_ctor_set(v___x_916_, 2, v___x_914_);
        lean_ctor_set(v___x_916_, 3, v___x_915_);
        v___x_917_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__31;
        v___x_918_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__32;
        v___x_919_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_919_, 0, v___x_898_);
        lean_ctor_set(v___x_919_, 1, v___x_918_);
        v___x_920_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__34;
        v___x_921_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__35;
        v___x_922_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_922_, 0, v___x_898_);
        lean_ctor_set(v___x_922_, 1, v___x_921_);
        v___x_923_ = l_Lean_Syntax_node1(v___x_898_, v___x_920_, v___x_922_);
        v___x_924_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__36;
        v___x_925_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_925_, 0, v___x_898_);
        lean_ctor_set(v___x_925_, 1, v___x_924_);
        v___x_926_ =
            l_Lean_Syntax_node3(v___x_898_, v___x_917_, v___x_919_, v___x_923_, v___x_925_);
        v___x_927_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__38;
        v___x_928_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__40;
        v___x_929_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__41;
        v___x_930_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_930_, 0, v___x_898_);
        lean_ctor_set(v___x_930_, 1, v___x_929_);
        v___x_931_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__43;
        v___x_932_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__45), core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__45_once), _init_l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__45);
        v___x_933_ = lean_box(0);
        v___x_934_ = l_Lean_addMacroScope(v_quotContext_894_, v___x_933_, v_currMacroScope_895_);
        v___x_935_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__52;
        v___x_936_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_936_, 0, v___x_898_);
        lean_ctor_set(v___x_936_, 1, v___x_932_);
        lean_ctor_set(v___x_936_, 2, v___x_934_);
        lean_ctor_set(v___x_936_, 3, v___x_935_);
        v___x_937_ = l_Lean_Syntax_node1(v___x_898_, v___x_931_, v___x_936_);
        v___x_938_ = l_Lean_Syntax_node2(v___x_898_, v___x_928_, v___x_930_, v___x_937_);
        v___x_939_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__54;
        v___x_940_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__55;
        v___x_941_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_941_, 0, v___x_898_);
        lean_ctor_set(v___x_941_, 1, v___x_940_);
        v___x_942_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__57;
        v___x_943_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__58;
        v___x_944_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_944_, 0, v___x_898_);
        lean_ctor_set(v___x_944_, 1, v___x_943_);
        v___x_945_ = l_Lean_Syntax_node1(v___x_898_, v___x_942_, v___x_944_);
        v___x_946_ = l_Lean_Syntax_node1(v___x_898_, v___x_902_, v___x_945_);
        v___x_947_ = l_Lean_Syntax_node1(v___x_898_, v___x_907_, v___x_946_);
        v___x_948_ = l_Lean_Syntax_node1(v___x_898_, v___x_906_, v___x_947_);
        v___x_949_ = l_Lean_Syntax_node2(v___x_898_, v___x_939_, v___x_941_, v___x_948_);
        v___x_950_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__59;
        v___x_951_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_951_, 0, v___x_898_);
        lean_ctor_set(v___x_951_, 1, v___x_950_);
        v___x_952_ =
            l_Lean_Syntax_node3(v___x_898_, v___x_927_, v___x_938_, v___x_949_, v___x_951_);
        v___x_953_ = l_Lean_Syntax_node2(v___x_898_, v___x_902_, v___x_926_, v___x_952_);
        lean_inc_n(v___x_953_, 2);
        v___x_954_ = l_Lean_Syntax_node2(v___x_898_, v___x_911_, v___x_916_, v___x_953_);
        lean_inc_ref_n(v___x_910_, 2);
        v___x_955_ = l_Lean_Syntax_node2(v___x_898_, v___x_909_, v___x_910_, v___x_954_);
        v___x_956_ = l_Lean_Syntax_node1(v___x_898_, v___x_902_, v___x_955_);
        v___x_957_ = l_Lean_Syntax_node1(v___x_898_, v___x_907_, v___x_956_);
        v___x_958_ = l_Lean_Syntax_node1(v___x_898_, v___x_906_, v___x_957_);
        lean_inc_ref_n(v___x_905_, 3);
        v___x_959_ = l_Lean_Syntax_node2(v___x_898_, v___x_903_, v___x_905_, v___x_958_);
        v___x_960_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__61), core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__61_once), _init_l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__61);
        v___x_961_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__63;
        v___x_962_ = l_Lean_addMacroScope(v_quotContext_894_, v___x_961_, v_currMacroScope_895_);
        v___x_963_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__65;
        v___x_964_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_964_, 0, v___x_898_);
        lean_ctor_set(v___x_964_, 1, v___x_960_);
        lean_ctor_set(v___x_964_, 2, v___x_962_);
        lean_ctor_set(v___x_964_, 3, v___x_963_);
        v___x_965_ = l_Lean_Syntax_node2(v___x_898_, v___x_911_, v___x_964_, v___x_953_);
        v___x_966_ = l_Lean_Syntax_node2(v___x_898_, v___x_909_, v___x_910_, v___x_965_);
        v___x_967_ = l_Lean_Syntax_node1(v___x_898_, v___x_902_, v___x_966_);
        v___x_968_ = l_Lean_Syntax_node1(v___x_898_, v___x_907_, v___x_967_);
        v___x_969_ = l_Lean_Syntax_node1(v___x_898_, v___x_906_, v___x_968_);
        v___x_970_ = l_Lean_Syntax_node2(v___x_898_, v___x_903_, v___x_905_, v___x_969_);
        v___x_971_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__67), core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__67_once), _init_l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__67);
        v___x_972_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__69;
        v___x_973_ = l_Lean_addMacroScope(v_quotContext_894_, v___x_972_, v_currMacroScope_895_);
        v___x_974_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__71;
        v___x_975_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_975_, 0, v___x_898_);
        lean_ctor_set(v___x_975_, 1, v___x_971_);
        lean_ctor_set(v___x_975_, 2, v___x_973_);
        lean_ctor_set(v___x_975_, 3, v___x_974_);
        v___x_976_ = l_Lean_Syntax_node2(v___x_898_, v___x_911_, v___x_975_, v___x_953_);
        v___x_977_ = l_Lean_Syntax_node2(v___x_898_, v___x_909_, v___x_910_, v___x_976_);
        v___x_978_ = l_Lean_Syntax_node1(v___x_898_, v___x_902_, v___x_977_);
        v___x_979_ = l_Lean_Syntax_node1(v___x_898_, v___x_907_, v___x_978_);
        v___x_980_ = l_Lean_Syntax_node1(v___x_898_, v___x_906_, v___x_979_);
        v___x_981_ = l_Lean_Syntax_node2(v___x_898_, v___x_903_, v___x_905_, v___x_980_);
        v___x_982_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__72;
        v___x_983_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__73;
        v___x_984_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_984_, 0, v___x_898_);
        lean_ctor_set(v___x_984_, 1, v___x_982_);
        v___x_985_ = l_Lean_Syntax_node1(v___x_898_, v___x_983_, v___x_984_);
        v___x_986_ = l_Lean_Syntax_node1(v___x_898_, v___x_902_, v___x_985_);
        v___x_987_ = l_Lean_Syntax_node1(v___x_898_, v___x_907_, v___x_986_);
        v___x_988_ = l_Lean_Syntax_node1(v___x_898_, v___x_906_, v___x_987_);
        v___x_989_ = l_Lean_Syntax_node2(v___x_898_, v___x_903_, v___x_905_, v___x_988_);
        v___x_990_ = l_Lean_Syntax_node4(
            v___x_898_, v___x_902_, v___x_959_, v___x_970_, v___x_981_, v___x_989_,
        );
        v___x_991_ = l_Lean_Syntax_node2(v___x_898_, v___x_900_, v___x_901_, v___x_990_);
        v___x_992_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_992_, 0, v___x_991_);
        lean_ctor_set(v___x_992_, 1, v_a_889_);
        return v___x_992_;
    }
}
pub unsafe fn l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1___boxed(
    mut v_x_993_: *mut LeanObject,
    mut v_a_994_: *mut LeanObject,
    mut v_a_995_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_996_: *mut LeanObject = core::ptr::null_mut();
    v_res_996_ = l_Std___aux__Init__Data__Range__Polymorphic__Basic______macroRules__tacticGet__elem__tactic__extensible__1(v_x_993_, v_a_994_, v_a_995_);
    lean_dec_ref(v_a_994_);
    return v_res_996_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Range_Polymorphic_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Range_Polymorphic_PRange(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Instances(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Range_Polymorphic_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Range_Polymorphic_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Range_Polymorphic_PRange(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Option_Instances(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Range_Polymorphic_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Range_Polymorphic_Basic(builtin);
}
