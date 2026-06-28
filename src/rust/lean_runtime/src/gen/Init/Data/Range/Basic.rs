// Lean compiler output
// Module: Init.Data.Range.Basic
// Imports: Init.Control.Basic Init.Grind.Tactics Init.Grind.Tactics Init.Omega Init.WFTactics
use crate::r#gen::Init::Control::Basic::{
    initialize_Init_Control_Basic, runtime_initialize_Init_Control_Basic,
};
use crate::r#gen::Init::Grind::Tactics::{
    initialize_Init_Grind_Tactics, meta_initialize_Init_Grind_Tactics,
    runtime_initialize_Init_Grind_Tactics,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr3,
    l_Lean_Name_mkStr4, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_node1, l_Lean_Syntax_node2, l_Lean_Syntax_node3, l_Lean_Syntax_node5,
    l_Lean_Syntax_node6, l_Lean_Syntax_node7, l_Lean_addMacroScope, l_Lean_mkAtom,
    l_String_toRawSubstring_x27,
};
use crate::r#gen::Init::WFTactics::{initialize_Init_WFTactics, runtime_initialize_Init_WFTactics};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_lt,
    lean_nat_div, lean_nat_sub,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get,
    lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_n, lean_inc_ref,
    lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_mark_persistent,
    lean_obj_once, lean_obj_tag, lean_unsigned_to_nat,
};
pub static mut l_Std_Legacy_instMembershipNatRange: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__0_value
) as *mut LeanObject;
pub static l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__1_value
) as *mut LeanObject;
pub static l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__2_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__2_value
) as *mut LeanObject;
pub static l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__3_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0]};
static mut l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__3_value
) as *mut LeanObject;
static l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__4_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__3_value) as *mut LeanObject,8504843326314613972 as *mut LeanObject] };
static mut l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__4_value
) as *mut LeanObject;
pub static l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__5_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__5_value
) as *mut LeanObject;
pub static l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__6_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0]};
static mut l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__6_value
) as *mut LeanObject;
static l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__7_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__7_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__7_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__7_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__7_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__7_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__6_value) as *mut LeanObject,17228437386856258271 as *mut LeanObject] };
static mut l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__7_value
) as *mut LeanObject;
pub static l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__8_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__8_value
) as *mut LeanObject;
pub static l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__9_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__8_value) as *mut LeanObject,9855511589286918680 as *mut LeanObject] };
static mut l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__9:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__9_value
) as *mut LeanObject;
pub static l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__10_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [111, 109, 101, 103, 97, 0]};
static mut l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__10_value) as *mut LeanObject;
static l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__11_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__11_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__11_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__11_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__11_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__11_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__11_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__10_value) as *mut LeanObject,14893461734720614794 as *mut LeanObject] };
static mut l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__11_value) as *mut LeanObject;
static mut l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__12_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__12: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__14_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [111, 112, 116, 67, 111, 110, 102, 105, 103, 0]};
static mut l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__14: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__14_value) as *mut LeanObject;
static l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__15_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__15_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__15_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__15_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__15_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__15_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__15_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__14_value) as *mut LeanObject,3488656302031949961 as *mut LeanObject] };
static mut l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__15: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__15_value) as *mut LeanObject;
pub static l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__16_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 1 }, m_objs: [((( 2 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__9_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__5_value) as *mut LeanObject] };
static mut l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__16: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__16_value) as *mut LeanObject;
static mut l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__17_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__17: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__18_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__18: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__19_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__19: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__20_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__20: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__21_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__21: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__22_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__22: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__23_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__23: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__24_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__24: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__25_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__25: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__26_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__26: *mut LeanObject = core::ptr::null_mut();
pub static mut l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__0_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [83, 116, 100, 0],
    };
static mut l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__0_value) as *mut LeanObject;
pub static l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__1_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [76, 101, 103, 97, 99, 121, 0],
    };
static mut l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__1_value) as *mut LeanObject;
pub static l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__2_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [82, 97, 110, 103, 101, 0],
    };
static mut l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__2_value) as *mut LeanObject;
pub static l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__3_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [116, 101, 114, 109, 91, 58, 95, 93, 0],
    };
static mut l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__3_value) as *mut LeanObject;
static l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__4_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__0_value)
                as *mut LeanObject,
            15734321041234825264 as *mut LeanObject,
        ],
    };
static l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__4_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__4_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__1_value)
                as *mut LeanObject,
            11605024481027861704 as *mut LeanObject,
        ],
    };
static l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__4_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__4_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__2_value)
                as *mut LeanObject,
            12285343096391770490 as *mut LeanObject,
        ],
    };
pub static l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__4_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__4_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__3_value)
                as *mut LeanObject,
            1789057247254607656 as *mut LeanObject,
        ],
    };
static mut l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__4_value) as *mut LeanObject;
pub static l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__5_value: LeanStringObject<8> =
    LeanStringObject {
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
static mut l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__5_value) as *mut LeanObject;
pub static l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__6_value: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__5_value)
                as *mut LeanObject,
            12571085391447129896 as *mut LeanObject,
        ],
    };
static mut l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__6_value) as *mut LeanObject;
pub static l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__7_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [91, 0],
    };
static mut l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__7_value) as *mut LeanObject;
pub static l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__8_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__7_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__8_value) as *mut LeanObject;
pub static l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__9_value: LeanStringObject<16> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 16,
        m_capacity: 16,
        m_length: 15,
        m_data: [
            119, 105, 116, 104, 111, 117, 116, 80, 111, 115, 105, 116, 105, 111, 110, 0,
        ],
    };
static mut l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__9_value) as *mut LeanObject;
pub static l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__10_value: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__9_value)
                as *mut LeanObject,
            1164644006045091397 as *mut LeanObject,
        ],
    };
static mut l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__10_value)
        as *mut LeanObject;
pub static l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__11_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [58, 0],
    };
static mut l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__11_value)
        as *mut LeanObject;
pub static l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__12_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__11_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__12_value)
        as *mut LeanObject;
pub static l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__13_value: LeanStringObject<5> =
    LeanStringObject {
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
static mut l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__13_value)
        as *mut LeanObject;
pub static l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__14_value: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__13_value)
                as *mut LeanObject,
            8609355255726335675 as *mut LeanObject,
        ],
    };
static mut l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__14_value)
        as *mut LeanObject;
pub static l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__15_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 7,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__14_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__15_value)
        as *mut LeanObject;
pub static l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__16_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__12_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__15_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__16_value)
        as *mut LeanObject;
pub static l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__17_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__10_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__16_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__17_value)
        as *mut LeanObject;
pub static l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__18_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__17_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__18_value)
        as *mut LeanObject;
pub static l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__19_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [93, 0],
    };
static mut l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__19_value)
        as *mut LeanObject;
pub static l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__20_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__19_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__20_value)
        as *mut LeanObject;
pub static l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__21_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__18_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__20_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__21_value)
        as *mut LeanObject;
pub static l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__22_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__4_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__21_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__22: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__22_value)
        as *mut LeanObject;
pub static mut l_Std_Legacy_Range_term_x5b_x3a___x5d: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__22_value)
        as *mut LeanObject;
pub static l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__0_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [116, 101, 114, 109, 91, 95, 58, 95, 93, 0],
    };
static mut l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__0_value)
        as *mut LeanObject;
static l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__1_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__0_value)
                as *mut LeanObject,
            15734321041234825264 as *mut LeanObject,
        ],
    };
static l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__1_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__1_value)
                as *mut LeanObject,
            11605024481027861704 as *mut LeanObject,
        ],
    };
static l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__1_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__2_value)
                as *mut LeanObject,
            12285343096391770490 as *mut LeanObject,
        ],
    };
pub static l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__0_value)
                as *mut LeanObject,
            7982727111025615621 as *mut LeanObject,
        ],
    };
static mut l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__2_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__15_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__12_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__2_value)
        as *mut LeanObject;
pub static l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__3_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__15_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__3_value)
        as *mut LeanObject;
pub static l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__4_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__10_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__4_value)
        as *mut LeanObject;
pub static l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__5_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__5_value)
        as *mut LeanObject;
pub static l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__6_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__20_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__6_value)
        as *mut LeanObject;
pub static l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__7_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__1_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__7_value)
        as *mut LeanObject;
pub static mut l_Std_Legacy_Range_term_x5b___x3a___x5d: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__7_value)
        as *mut LeanObject;
pub static l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__0_value: LeanStringObject<11> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [116, 101, 114, 109, 91, 58, 95, 58, 95, 93, 0],
    };
static mut l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__0_value)
        as *mut LeanObject;
static l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__1_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__0_value)
                as *mut LeanObject,
            15734321041234825264 as *mut LeanObject,
        ],
    };
static l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__1_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__1_value)
                as *mut LeanObject,
            11605024481027861704 as *mut LeanObject,
        ],
    };
static l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__1_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__2_value)
                as *mut LeanObject,
            12285343096391770490 as *mut LeanObject,
        ],
    };
pub static l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__0_value)
                as *mut LeanObject,
            13729938264223131606 as *mut LeanObject,
        ],
    };
static mut l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__2_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__16_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__12_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__2_value)
        as *mut LeanObject;
pub static l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__3_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__15_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__3_value)
        as *mut LeanObject;
pub static l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__4_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__10_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__4_value)
        as *mut LeanObject;
pub static l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__5_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__5_value)
        as *mut LeanObject;
pub static l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__6_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__20_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__6_value)
        as *mut LeanObject;
pub static l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__7_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__1_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__7_value)
        as *mut LeanObject;
pub static mut l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__7_value)
        as *mut LeanObject;
pub static l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__0_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [116, 101, 114, 109, 91, 95, 58, 95, 58, 95, 93, 0],
    };
static mut l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__0_value)
        as *mut LeanObject;
static l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__1_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__0_value)
                as *mut LeanObject,
            15734321041234825264 as *mut LeanObject,
        ],
    };
static l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__1_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__1_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__1_value)
                as *mut LeanObject,
            11605024481027861704 as *mut LeanObject,
        ],
    };
static l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__1_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__1_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__2_value)
                as *mut LeanObject,
            12285343096391770490 as *mut LeanObject,
        ],
    };
pub static l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__1_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__0_value)
                as *mut LeanObject,
            3905970969787411623 as *mut LeanObject,
        ],
    };
static mut l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__2_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__12_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__2_value)
        as *mut LeanObject;
pub static l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__3_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__15_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__3_value)
        as *mut LeanObject;
pub static l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__4_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__10_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__4_value)
        as *mut LeanObject;
pub static l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__5_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__5_value)
        as *mut LeanObject;
pub static l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__6_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__20_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__6_value)
        as *mut LeanObject;
pub static l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__7_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__1_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__7_value)
        as *mut LeanObject;
pub static mut l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__7_value)
        as *mut LeanObject;
pub static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__0_value) as *mut LeanObject;
pub static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__1_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [115, 116, 114, 117, 99, 116, 73, 110, 115, 116, 0]};
static mut l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__1_value) as *mut LeanObject;
static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__2_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__2_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__2_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__0_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__2_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__1_value) as *mut LeanObject,2026475204632980274 as *mut LeanObject] };
static mut l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__2_value) as *mut LeanObject;
pub static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__3_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [123, 0]};
static mut l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__3_value) as *mut LeanObject;
static mut l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__5_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 116, 114, 117, 99, 116, 73, 110, 115, 116, 70, 105, 101, 108, 100, 115, 0]};
static mut l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__5_value) as *mut LeanObject;
static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__6_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__6_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__6_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__6_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__6_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__0_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__6_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__5_value) as *mut LeanObject,5018042693327868416 as *mut LeanObject] };
static mut l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__6_value) as *mut LeanObject;
pub static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__7_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [115, 116, 114, 117, 99, 116, 73, 110, 115, 116, 70, 105, 101, 108, 100, 0]};
static mut l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__7: *mut LeanObject = core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__7_value) as *mut LeanObject;
static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__8_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__8_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__8_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__8_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__8_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__0_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__8_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__7_value) as *mut LeanObject,6117808163008040242 as *mut LeanObject] };
static mut l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__8_value) as *mut LeanObject;
pub static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__9_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [115, 116, 114, 117, 99, 116, 73, 110, 115, 116, 76, 86, 97, 108, 0]};
static mut l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__9: *mut LeanObject = core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__9_value) as *mut LeanObject;
static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__10_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__10_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__10_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__10_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__10_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__0_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__10_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__10_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__9_value) as *mut LeanObject,14295752356045161913 as *mut LeanObject] };
static mut l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__10_value) as *mut LeanObject;
pub static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__11_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 116, 111, 112, 0]};
static mut l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__11: *mut LeanObject = core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__11_value) as *mut LeanObject;
static mut l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__12_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__12: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__13_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__11_value) as *mut LeanObject,5308569851895372105 as *mut LeanObject] };
static mut l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__13: *mut LeanObject = core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__13_value) as *mut LeanObject;
static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__14_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__0_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__14_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__14_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__1_value) as *mut LeanObject,11605024481027861704 as *mut LeanObject] };
static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__14_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__14_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__2_value) as *mut LeanObject,12285343096391770490 as *mut LeanObject] };
pub static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__14_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__14_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__11_value) as *mut LeanObject,1892624668511565044 as *mut LeanObject] };
static mut l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__14: *mut LeanObject = core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__14_value) as *mut LeanObject;
pub static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__15_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__14_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__15: *mut LeanObject = core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__15_value) as *mut LeanObject;
pub static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__16_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__15_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__16: *mut LeanObject = core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__16_value) as *mut LeanObject;
pub static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__17_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [115, 116, 114, 117, 99, 116, 73, 110, 115, 116, 70, 105, 101, 108, 100, 68, 101, 102, 0]};
static mut l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__17: *mut LeanObject = core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__17_value) as *mut LeanObject;
static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__18_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__18_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__18_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__18_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__18_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__0_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__18_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__18_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__17_value) as *mut LeanObject,7440505896048223825 as *mut LeanObject] };
static mut l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__18: *mut LeanObject = core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__18_value) as *mut LeanObject;
pub static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__19_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [58, 61, 0]};
static mut l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__19: *mut LeanObject = core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__19_value) as *mut LeanObject;
pub static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__20_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [44, 0]};
static mut l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__20: *mut LeanObject = core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__20_value) as *mut LeanObject;
pub static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__21_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [115, 116, 101, 112, 95, 112, 111, 115, 0]};
static mut l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__21: *mut LeanObject = core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__21_value) as *mut LeanObject;
static mut l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__22_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__22: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__23_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__21_value) as *mut LeanObject,5594111154515311093 as *mut LeanObject] };
static mut l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__23: *mut LeanObject = core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__23_value) as *mut LeanObject;
static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__24_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__0_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__24_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__24_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__1_value) as *mut LeanObject,11605024481027861704 as *mut LeanObject] };
static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__24_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__24_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__2_value) as *mut LeanObject,12285343096391770490 as *mut LeanObject] };
pub static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__24_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__24_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__21_value) as *mut LeanObject,6242496087388805024 as *mut LeanObject] };
static mut l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__24: *mut LeanObject = core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__24_value) as *mut LeanObject;
pub static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__25_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__24_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__25: *mut LeanObject = core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__25_value) as *mut LeanObject;
pub static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__26_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__25_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__26: *mut LeanObject = core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__26_value) as *mut LeanObject;
pub static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__27_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [78, 97, 116, 46, 122, 101, 114, 111, 95, 108, 116, 95, 111, 110, 101, 0]};
static mut l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__27: *mut LeanObject = core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__27_value) as *mut LeanObject;
static mut l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__28_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__28: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__29_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [78, 97, 116, 0]};
static mut l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__29: *mut LeanObject = core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__29_value) as *mut LeanObject;
pub static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__30_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [122, 101, 114, 111, 95, 108, 116, 95, 111, 110, 101, 0]};
static mut l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__30: *mut LeanObject = core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__30_value) as *mut LeanObject;
static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__31_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__29_value) as *mut LeanObject,11442535297760353691 as *mut LeanObject] };
pub static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__31_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__31_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__30_value) as *mut LeanObject,18370005618953685177 as *mut LeanObject] };
static mut l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__31: *mut LeanObject = core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__31_value) as *mut LeanObject;
pub static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__32_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__31_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__32: *mut LeanObject = core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__32_value) as *mut LeanObject;
pub static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__33_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__32_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__33: *mut LeanObject = core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__33_value) as *mut LeanObject;
pub static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__34_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [111, 112, 116, 69, 108, 108, 105, 112, 115, 105, 115, 0]};
static mut l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__34: *mut LeanObject = core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__34_value) as *mut LeanObject;
static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__35_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__35_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__35_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__35_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__35_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__0_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__35_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__35_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__34_value) as *mut LeanObject,11580369617518985485 as *mut LeanObject] };
static mut l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__35: *mut LeanObject = core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__35_value) as *mut LeanObject;
static mut l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__36_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__36: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__37_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__2_value) as *mut LeanObject,12243235223794968693 as *mut LeanObject] };
static mut l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__37: *mut LeanObject = core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__37_value) as *mut LeanObject;
static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__38_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__0_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__38_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__38_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__1_value) as *mut LeanObject,11605024481027861704 as *mut LeanObject] };
pub static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__38_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__38_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__2_value) as *mut LeanObject,12285343096391770490 as *mut LeanObject] };
static mut l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__38: *mut LeanObject = core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__38_value) as *mut LeanObject;
pub static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__39_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__38_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__39: *mut LeanObject = core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__39_value) as *mut LeanObject;
pub static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__40_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__38_value) as *mut LeanObject] };
static mut l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__40: *mut LeanObject = core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__40_value) as *mut LeanObject;
pub static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__41_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__40_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__41: *mut LeanObject = core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__41_value) as *mut LeanObject;
pub static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__42_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__39_value) as *mut LeanObject,core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__41_value) as *mut LeanObject] };
static mut l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__42: *mut LeanObject = core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__42_value) as *mut LeanObject;
pub static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__43_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [125, 0]};
static mut l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__43: *mut LeanObject = core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__43_value) as *mut LeanObject;
pub static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [115, 116, 97, 114, 116, 0]};
static mut l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__0_value) as *mut LeanObject;
static mut l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__0_value) as *mut LeanObject,12748178501718933929 as *mut LeanObject] };
static mut l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__2_value) as *mut LeanObject;
static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__0_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__1_value) as *mut LeanObject,11605024481027861704 as *mut LeanObject] };
static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__2_value) as *mut LeanObject,12285343096391770490 as *mut LeanObject] };
pub static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__0_value) as *mut LeanObject,6388013072772761428 as *mut LeanObject] };
static mut l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__3_value) as *mut LeanObject;
pub static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__3_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__4_value) as *mut LeanObject;
pub static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__5_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__4_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__5_value) as *mut LeanObject;
pub static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 116, 101, 112, 0]};
static mut l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__0_value) as *mut LeanObject;
static mut l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__0_value) as *mut LeanObject,522840107559006527 as *mut LeanObject] };
static mut l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__2_value) as *mut LeanObject;
static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__0_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__1_value) as *mut LeanObject,11605024481027861704 as *mut LeanObject] };
static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__2_value) as *mut LeanObject,12285343096391770490 as *mut LeanObject] };
pub static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__0_value) as *mut LeanObject,1235519761781178730 as *mut LeanObject] };
static mut l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__3_value) as *mut LeanObject;
pub static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__3_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__4_value) as *mut LeanObject;
pub static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__5_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__4_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__5_value) as *mut LeanObject;
pub static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__6_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [98, 121, 84, 97, 99, 116, 105, 99, 0]};
static mut l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__6_value) as *mut LeanObject;
static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__7_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__7_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__7_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__7_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__7_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__0_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__7_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__6_value) as *mut LeanObject,16173796135615239867 as *mut LeanObject] };
static mut l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__7: *mut LeanObject = core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__7_value) as *mut LeanObject;
pub static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__8_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [98, 121, 0]};
static mut l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__8_value) as *mut LeanObject;
pub static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__9_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [100, 101, 99, 105, 100, 101, 0]};
static mut l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__9: *mut LeanObject = core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__9_value) as *mut LeanObject;
static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__10_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__10_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__10_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__10_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__10_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__10_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__10_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__9_value) as *mut LeanObject,14249328086033210933 as *mut LeanObject] };
static mut l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__10_value) as *mut LeanObject;
pub static l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__0_value: LeanStringObject<33> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [116, 97, 99, 116, 105, 99, 71, 101, 116, 95, 101, 108, 101, 109, 95, 116, 97, 99, 116, 105, 99, 95, 101, 120, 116, 101, 110, 115, 105, 98, 108, 101, 0]};
static mut l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__0_value) as *mut LeanObject;
pub static l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__0_value) as *mut LeanObject,7705027380931481693 as *mut LeanObject] };
static mut l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__1_value) as *mut LeanObject;
pub static l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 101, 113, 49, 0]};
static mut l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value) as *mut LeanObject;
static l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value) as *mut LeanObject,8471002125274025202 as *mut LeanObject] };
static mut l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value) as *mut LeanObject;
pub static l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [97, 112, 112, 108, 121, 0]};
static mut l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value) as *mut LeanObject;
static l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__5_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__5_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__5_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__5_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__5_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value) as *mut LeanObject,5826123769708379594 as *mut LeanObject] };
static mut l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__5: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__5_value) as *mut LeanObject;
pub static l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__6_value: LeanStringObject<27> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [77, 101, 109, 98, 101, 114, 115, 104, 105, 112, 46, 103, 101, 116, 95, 101, 108, 101, 109, 95, 104, 101, 108, 112, 101, 114, 0]};
static mut l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__6: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__6_value) as *mut LeanObject;
static mut l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__8_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [77, 101, 109, 98, 101, 114, 115, 104, 105, 112, 0]};
static mut l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__8: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__8_value) as *mut LeanObject;
pub static l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__9_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [103, 101, 116, 95, 101, 108, 101, 109, 95, 104, 101, 108, 112, 101, 114, 0]};
static mut l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__9: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__9_value) as *mut LeanObject;
static l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__10_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__8_value) as *mut LeanObject,7877420268164864461 as *mut LeanObject] };
pub static l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__10_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__10_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__9_value) as *mut LeanObject,14720060119771013513 as *mut LeanObject] };
static mut l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__10: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__10_value) as *mut LeanObject;
pub static l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__11_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__10_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__11: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__11_value) as *mut LeanObject;
pub static l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__12_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__11_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__12: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__12_value) as *mut LeanObject;
pub static l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__13_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [59, 0]};
static mut l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__13: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__13_value) as *mut LeanObject;
pub static l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__14_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [97, 115, 115, 117, 109, 112, 116, 105, 111, 110, 0]};
static mut l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__14: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__14_value) as *mut LeanObject;
static l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__14_value) as *mut LeanObject,16687334436616221424 as *mut LeanObject] };
static mut l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value) as *mut LeanObject;
pub static l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__16_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 97, 99, 116, 105, 99, 82, 102, 108, 0]};
static mut l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__16: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__16_value) as *mut LeanObject;
static l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__16_value) as *mut LeanObject,3294379458557754569 as *mut LeanObject] };
static mut l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17_value) as *mut LeanObject;
pub static l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__18_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [114, 102, 108, 0]};
static mut l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__18: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__18_value) as *mut LeanObject;
pub unsafe fn _init_l_Std_Legacy_instMembershipNatRange() -> *mut LeanObject {
    let mut v___x_954_: *mut LeanObject = core::ptr::null_mut();
    v___x_954_ = lean_box(0);
    return v___x_954_;
}
pub unsafe fn l_Std_Legacy_Range_size(mut v_r_955_: *mut LeanObject) -> *mut LeanObject {
    let mut v_start_956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_step_958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_963_: *mut LeanObject = core::ptr::null_mut();
    v_start_956_ = lean_ctor_get(v_r_955_, 0);
    v_stop_957_ = lean_ctor_get(v_r_955_, 1);
    v_step_958_ = lean_ctor_get(v_r_955_, 2);
    v___x_959_ = lean_nat_sub(v_stop_957_, v_start_956_);
    v___x_960_ = lean_nat_add(v___x_959_, v_step_958_);
    lean_dec(v___x_959_);
    v___x_961_ = lean_unsigned_to_nat(1);
    v___x_962_ = lean_nat_sub(v___x_960_, v___x_961_);
    lean_dec(v___x_960_);
    v___x_963_ = lean_nat_div(v___x_962_, v_step_958_);
    lean_dec(v___x_962_);
    return v___x_963_;
}
pub unsafe fn l_Std_Legacy_Range_size___boxed(mut v_r_964_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_965_: *mut LeanObject = core::ptr::null_mut();
    v_res_965_ = l_Std_Legacy_Range_size(v_r_964_);
    lean_dec_ref(v_r_964_);
    return v_res_965_;
}
pub unsafe fn _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__12()
-> *mut LeanObject {
    let mut v___x_992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut LeanObject = core::ptr::null_mut();
    v___x_992_ =
        l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__10;
    v___x_993_ = l_Lean_mkAtom(v___x_992_);
    return v___x_993_;
}
pub unsafe fn _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__13()
-> *mut LeanObject {
    let mut v___x_994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_996_: *mut LeanObject = core::ptr::null_mut();
    v___x_994_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__12), core::ptr::addr_of_mut!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__12_once), _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__12);
    v___x_995_ =
        l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__5;
    v___x_996_ = lean_array_push(v___x_995_, v___x_994_);
    return v___x_996_;
}
pub unsafe fn _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__17()
-> *mut LeanObject {
    let mut v___x_1007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: *mut LeanObject = core::ptr::null_mut();
    v___x_1007_ =
        l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__16;
    v___x_1008_ =
        l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__5;
    v___x_1009_ = lean_array_push(v___x_1008_, v___x_1007_);
    return v___x_1009_;
}
pub unsafe fn _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__18()
-> *mut LeanObject {
    let mut v___x_1010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: *mut LeanObject = core::ptr::null_mut();
    v___x_1010_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__17), core::ptr::addr_of_mut!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__17_once), _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__17);
    v___x_1011_ =
        l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__15;
    v___x_1012_ = lean_box(2);
    v___x_1013_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_1013_, 0, v___x_1012_);
    lean_ctor_set(v___x_1013_, 1, v___x_1011_);
    lean_ctor_set(v___x_1013_, 2, v___x_1010_);
    return v___x_1013_;
}
pub unsafe fn _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__19()
-> *mut LeanObject {
    let mut v___x_1014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: *mut LeanObject = core::ptr::null_mut();
    v___x_1014_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__18), core::ptr::addr_of_mut!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__18_once), _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__18);
    v___x_1015_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__13), core::ptr::addr_of_mut!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__13_once), _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__13);
    v___x_1016_ = lean_array_push(v___x_1015_, v___x_1014_);
    return v___x_1016_;
}
pub unsafe fn _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__20()
-> *mut LeanObject {
    let mut v___x_1017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: *mut LeanObject = core::ptr::null_mut();
    v___x_1017_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__19), core::ptr::addr_of_mut!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__19_once), _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__19);
    v___x_1018_ =
        l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__11;
    v___x_1019_ = lean_box(2);
    v___x_1020_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_1020_, 0, v___x_1019_);
    lean_ctor_set(v___x_1020_, 1, v___x_1018_);
    lean_ctor_set(v___x_1020_, 2, v___x_1017_);
    return v___x_1020_;
}
pub unsafe fn _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__21()
-> *mut LeanObject {
    let mut v___x_1021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: *mut LeanObject = core::ptr::null_mut();
    v___x_1021_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__20), core::ptr::addr_of_mut!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__20_once), _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__20);
    v___x_1022_ =
        l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__5;
    v___x_1023_ = lean_array_push(v___x_1022_, v___x_1021_);
    return v___x_1023_;
}
pub unsafe fn _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__22()
-> *mut LeanObject {
    let mut v___x_1024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: *mut LeanObject = core::ptr::null_mut();
    v___x_1024_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__21), core::ptr::addr_of_mut!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__21_once), _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__21);
    v___x_1025_ =
        l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__9;
    v___x_1026_ = lean_box(2);
    v___x_1027_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_1027_, 0, v___x_1026_);
    lean_ctor_set(v___x_1027_, 1, v___x_1025_);
    lean_ctor_set(v___x_1027_, 2, v___x_1024_);
    return v___x_1027_;
}
pub unsafe fn _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__23()
-> *mut LeanObject {
    let mut v___x_1028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: *mut LeanObject = core::ptr::null_mut();
    v___x_1028_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__22), core::ptr::addr_of_mut!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__22_once), _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__22);
    v___x_1029_ =
        l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__5;
    v___x_1030_ = lean_array_push(v___x_1029_, v___x_1028_);
    return v___x_1030_;
}
pub unsafe fn _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__24()
-> *mut LeanObject {
    let mut v___x_1031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1034_: *mut LeanObject = core::ptr::null_mut();
    v___x_1031_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__23), core::ptr::addr_of_mut!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__23_once), _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__23);
    v___x_1032_ =
        l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__7;
    v___x_1033_ = lean_box(2);
    v___x_1034_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_1034_, 0, v___x_1033_);
    lean_ctor_set(v___x_1034_, 1, v___x_1032_);
    lean_ctor_set(v___x_1034_, 2, v___x_1031_);
    return v___x_1034_;
}
pub unsafe fn _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__25()
-> *mut LeanObject {
    let mut v___x_1035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: *mut LeanObject = core::ptr::null_mut();
    v___x_1035_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__24), core::ptr::addr_of_mut!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__24_once), _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__24);
    v___x_1036_ =
        l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__5;
    v___x_1037_ = lean_array_push(v___x_1036_, v___x_1035_);
    return v___x_1037_;
}
pub unsafe fn _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__26()
-> *mut LeanObject {
    let mut v___x_1038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1041_: *mut LeanObject = core::ptr::null_mut();
    v___x_1038_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__25), core::ptr::addr_of_mut!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__25_once), _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__25);
    v___x_1039_ =
        l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__4;
    v___x_1040_ = lean_box(2);
    v___x_1041_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_1041_, 0, v___x_1040_);
    lean_ctor_set(v___x_1041_, 1, v___x_1039_);
    lean_ctor_set(v___x_1041_, 2, v___x_1038_);
    return v___x_1041_;
}
pub unsafe fn _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1()
-> *mut LeanObject {
    let mut v___x_1042_: *mut LeanObject = core::ptr::null_mut();
    v___x_1042_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__26), core::ptr::addr_of_mut!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__26_once), _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__26);
    return v___x_1042_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___redArg___lam__0___boxed(
    mut v_toApplicative_1043_: *mut LeanObject,
    mut v_i_1044_: *mut LeanObject,
    mut v_step_1045_: *mut LeanObject,
    mut v_inst_1046_: *mut LeanObject,
    mut v_range_1047_: *mut LeanObject,
    mut v_f_1048_: *mut LeanObject,
    mut v_____do__lift_1049_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1050_: *mut LeanObject = core::ptr::null_mut();
    v_res_1050_ =
        l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___redArg___lam__0(
            v_toApplicative_1043_,
            v_i_1044_,
            v_step_1045_,
            v_inst_1046_,
            v_range_1047_,
            v_f_1048_,
            v_____do__lift_1049_,
        );
    lean_dec(v_step_1045_);
    lean_dec(v_i_1044_);
    return v_res_1050_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___redArg(
    mut v_inst_1051_: *mut LeanObject,
    mut v_range_1052_: *mut LeanObject,
    mut v_f_1053_: *mut LeanObject,
    mut v_b_1054_: *mut LeanObject,
    mut v_i_1055_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_stop_1056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_step_1057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1058_: u8 = 0;
    v_stop_1056_ = lean_ctor_get(v_range_1052_, 1);
    v_step_1057_ = lean_ctor_get(v_range_1052_, 2);
    lean_inc(v_step_1057_);
    v___x_1058_ = lean_nat_dec_lt(v_i_1055_, v_stop_1056_);
    if v___x_1058_ == 0 {
        let mut v_toApplicative_1059_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_1060_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1061_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_step_1057_);
        lean_dec(v_i_1055_);
        lean_dec(v_f_1053_);
        lean_dec_ref(v_range_1052_);
        v_toApplicative_1059_ = lean_ctor_get(v_inst_1051_, 0);
        lean_inc_ref(v_toApplicative_1059_);
        lean_dec_ref(v_inst_1051_);
        v_toPure_1060_ = lean_ctor_get(v_toApplicative_1059_, 1);
        lean_inc(v_toPure_1060_);
        lean_dec_ref(v_toApplicative_1059_);
        v___x_1061_ = lean_apply_2(v_toPure_1060_, lean_box(0), v_b_1054_);
        return v___x_1061_;
    } else {
        let mut v_toApplicative_1062_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toBind_1063_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_1064_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1065_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1066_: *mut LeanObject = core::ptr::null_mut();
        v_toApplicative_1062_ = lean_ctor_get(v_inst_1051_, 0);
        lean_inc_ref(v_toApplicative_1062_);
        v_toBind_1063_ = lean_ctor_get(v_inst_1051_, 1);
        lean_inc(v_toBind_1063_);
        lean_inc(v_f_1053_);
        lean_inc(v_i_1055_);
        v___f_1064_ = lean_alloc_closure(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___redArg___lam__0___boxed as *mut core::ffi::c_void, 7, 6);
        lean_closure_set(v___f_1064_, 0, v_toApplicative_1062_);
        lean_closure_set(v___f_1064_, 1, v_i_1055_);
        lean_closure_set(v___f_1064_, 2, v_step_1057_);
        lean_closure_set(v___f_1064_, 3, v_inst_1051_);
        lean_closure_set(v___f_1064_, 4, v_range_1052_);
        lean_closure_set(v___f_1064_, 5, v_f_1053_);
        v___x_1065_ = lean_apply_3(v_f_1053_, v_i_1055_, lean_box(0), v_b_1054_);
        v___x_1066_ = lean_apply_4(
            v_toBind_1063_,
            lean_box(0),
            lean_box(0),
            v___x_1065_,
            v___f_1064_,
        );
        return v___x_1066_;
    }
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___redArg___lam__0(
    mut v_toApplicative_1067_: *mut LeanObject,
    mut v_i_1068_: *mut LeanObject,
    mut v_step_1069_: *mut LeanObject,
    mut v_inst_1070_: *mut LeanObject,
    mut v_range_1071_: *mut LeanObject,
    mut v_f_1072_: *mut LeanObject,
    mut v_____do__lift_1073_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_1073_) == 0 {
        let mut v_a_1074_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_1075_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1076_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_f_1072_);
        lean_dec_ref(v_range_1071_);
        lean_dec_ref(v_inst_1070_);
        v_a_1074_ = lean_ctor_get(v_____do__lift_1073_, 0);
        lean_inc(v_a_1074_);
        lean_dec_ref_known(v_____do__lift_1073_, 1);
        v_toPure_1075_ = lean_ctor_get(v_toApplicative_1067_, 1);
        lean_inc(v_toPure_1075_);
        lean_dec_ref(v_toApplicative_1067_);
        v___x_1076_ = lean_apply_2(v_toPure_1075_, lean_box(0), v_a_1074_);
        return v___x_1076_;
    } else {
        let mut v_a_1077_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1078_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1079_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_toApplicative_1067_);
        v_a_1077_ = lean_ctor_get(v_____do__lift_1073_, 0);
        lean_inc(v_a_1077_);
        lean_dec_ref_known(v_____do__lift_1073_, 1);
        v___x_1078_ = lean_nat_add(v_i_1068_, v_step_1069_);
        v___x_1079_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___redArg(
            v_inst_1070_,
            v_range_1071_,
            v_f_1072_,
            v_a_1077_,
            v___x_1078_,
        );
        return v___x_1079_;
    }
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop(
    mut v_m_1080_: *mut LeanObject,
    mut v_00_u03b2_1081_: *mut LeanObject,
    mut v_inst_1082_: *mut LeanObject,
    mut v_range_1083_: *mut LeanObject,
    mut v_f_1084_: *mut LeanObject,
    mut v_b_1085_: *mut LeanObject,
    mut v_i_1086_: *mut LeanObject,
    mut v_hs_1087_: *mut LeanObject,
    mut v_hl_1088_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1089_: *mut LeanObject = core::ptr::null_mut();
    v___x_1089_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___redArg(
        v_inst_1082_,
        v_range_1083_,
        v_f_1084_,
        v_b_1085_,
        v_i_1086_,
    );
    return v___x_1089_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop_match__1_splitter___redArg(
    mut v_____do__lift_1090_: *mut LeanObject,
    mut v_h__1_1091_: *mut LeanObject,
    mut v_h__2_1092_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_1090_) == 0 {
        let mut v_a_1093_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1094_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1092_);
        v_a_1093_ = lean_ctor_get(v_____do__lift_1090_, 0);
        lean_inc(v_a_1093_);
        lean_dec_ref_known(v_____do__lift_1090_, 1);
        v___x_1094_ = lean_apply_1(v_h__1_1091_, v_a_1093_);
        return v___x_1094_;
    } else {
        let mut v_a_1095_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1096_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1091_);
        v_a_1095_ = lean_ctor_get(v_____do__lift_1090_, 0);
        lean_inc(v_a_1095_);
        lean_dec_ref_known(v_____do__lift_1090_, 1);
        v___x_1096_ = lean_apply_1(v_h__2_1092_, v_a_1095_);
        return v___x_1096_;
    }
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop_match__1_splitter(
    mut v_00_u03b2_1097_: *mut LeanObject,
    mut v_motive_1098_: *mut LeanObject,
    mut v_____do__lift_1099_: *mut LeanObject,
    mut v_h__1_1100_: *mut LeanObject,
    mut v_h__2_1101_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_1099_) == 0 {
        let mut v_a_1102_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1103_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1101_);
        v_a_1102_ = lean_ctor_get(v_____do__lift_1099_, 0);
        lean_inc(v_a_1102_);
        lean_dec_ref_known(v_____do__lift_1099_, 1);
        v___x_1103_ = lean_apply_1(v_h__1_1100_, v_a_1102_);
        return v___x_1103_;
    } else {
        let mut v_a_1104_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1105_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1100_);
        v_a_1104_ = lean_ctor_get(v_____do__lift_1099_, 0);
        lean_inc(v_a_1104_);
        lean_dec_ref_known(v_____do__lift_1099_, 1);
        v___x_1105_ = lean_apply_1(v_h__2_1101_, v_a_1104_);
        return v___x_1105_;
    }
}
pub unsafe fn l_Std_Legacy_Range_forIn_x27___redArg(
    mut v_inst_1106_: *mut LeanObject,
    mut v_range_1107_: *mut LeanObject,
    mut v_init_1108_: *mut LeanObject,
    mut v_f_1109_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_start_1110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1111_: *mut LeanObject = core::ptr::null_mut();
    v_start_1110_ = lean_ctor_get(v_range_1107_, 0);
    lean_inc(v_start_1110_);
    v___x_1111_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___redArg(
        v_inst_1106_,
        v_range_1107_,
        v_f_1109_,
        v_init_1108_,
        v_start_1110_,
    );
    return v___x_1111_;
}
pub unsafe fn l_Std_Legacy_Range_forIn_x27(
    mut v_m_1112_: *mut LeanObject,
    mut v_00_u03b2_1113_: *mut LeanObject,
    mut v_inst_1114_: *mut LeanObject,
    mut v_range_1115_: *mut LeanObject,
    mut v_init_1116_: *mut LeanObject,
    mut v_f_1117_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_start_1118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1119_: *mut LeanObject = core::ptr::null_mut();
    v_start_1118_ = lean_ctor_get(v_range_1115_, 0);
    lean_inc(v_start_1118_);
    v___x_1119_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___redArg(
        v_inst_1114_,
        v_range_1115_,
        v_f_1117_,
        v_init_1116_,
        v_start_1118_,
    );
    return v___x_1119_;
}
pub unsafe fn l_Std_Legacy_Range_instForIn_x27NatInferInstanceMembershipOfMonad___redArg___lam__0(
    mut v_inst_1120_: *mut LeanObject,
    mut v_00_u03b2_1121_: *mut LeanObject,
    mut v___y_1122_: *mut LeanObject,
    mut v___y_1123_: *mut LeanObject,
    mut v___y_1124_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_start_1125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1126_: *mut LeanObject = core::ptr::null_mut();
    v_start_1125_ = lean_ctor_get(v___y_1122_, 0);
    lean_inc(v_start_1125_);
    v___x_1126_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___redArg(
        v_inst_1120_,
        v___y_1122_,
        v___y_1124_,
        v___y_1123_,
        v_start_1125_,
    );
    return v___x_1126_;
}
pub unsafe fn l_Std_Legacy_Range_instForIn_x27NatInferInstanceMembershipOfMonad___redArg(
    mut v_inst_1127_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1128_: *mut LeanObject = core::ptr::null_mut();
    v___f_1128_ = lean_alloc_closure(
        l_Std_Legacy_Range_instForIn_x27NatInferInstanceMembershipOfMonad___redArg___lam__0
            as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_1128_, 0, v_inst_1127_);
    return v___f_1128_;
}
pub unsafe fn l_Std_Legacy_Range_instForIn_x27NatInferInstanceMembershipOfMonad(
    mut v_m_1129_: *mut LeanObject,
    mut v_inst_1130_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1131_: *mut LeanObject = core::ptr::null_mut();
    v___f_1131_ = lean_alloc_closure(
        l_Std_Legacy_Range_instForIn_x27NatInferInstanceMembershipOfMonad___redArg___lam__0
            as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_1131_, 0, v_inst_1130_);
    return v___f_1131_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forM_loop___redArg___lam__0___boxed(
    mut v_i_1132_: *mut LeanObject,
    mut v_step_1133_: *mut LeanObject,
    mut v_inst_1134_: *mut LeanObject,
    mut v_range_1135_: *mut LeanObject,
    mut v_f_1136_: *mut LeanObject,
    mut v_____r_1137_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1138_: *mut LeanObject = core::ptr::null_mut();
    v_res_1138_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forM_loop___redArg___lam__0(
        v_i_1132_,
        v_step_1133_,
        v_inst_1134_,
        v_range_1135_,
        v_f_1136_,
        v_____r_1137_,
    );
    lean_dec(v_step_1133_);
    lean_dec(v_i_1132_);
    return v_res_1138_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forM_loop___redArg(
    mut v_inst_1139_: *mut LeanObject,
    mut v_range_1140_: *mut LeanObject,
    mut v_f_1141_: *mut LeanObject,
    mut v_i_1142_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_stop_1143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_step_1144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: u8 = 0;
    v_stop_1143_ = lean_ctor_get(v_range_1140_, 1);
    v_step_1144_ = lean_ctor_get(v_range_1140_, 2);
    lean_inc(v_step_1144_);
    v___x_1145_ = lean_nat_dec_lt(v_i_1142_, v_stop_1143_);
    if v___x_1145_ == 0 {
        let mut v_toApplicative_1146_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_1147_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1148_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1149_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_step_1144_);
        lean_dec(v_i_1142_);
        lean_dec(v_f_1141_);
        lean_dec_ref(v_range_1140_);
        v_toApplicative_1146_ = lean_ctor_get(v_inst_1139_, 0);
        lean_inc_ref(v_toApplicative_1146_);
        lean_dec_ref(v_inst_1139_);
        v_toPure_1147_ = lean_ctor_get(v_toApplicative_1146_, 1);
        lean_inc(v_toPure_1147_);
        lean_dec_ref(v_toApplicative_1146_);
        v___x_1148_ = lean_box(0);
        v___x_1149_ = lean_apply_2(v_toPure_1147_, lean_box(0), v___x_1148_);
        return v___x_1149_;
    } else {
        let mut v_toBind_1150_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_1151_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1152_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1153_: *mut LeanObject = core::ptr::null_mut();
        v_toBind_1150_ = lean_ctor_get(v_inst_1139_, 1);
        lean_inc(v_toBind_1150_);
        lean_inc(v_f_1141_);
        lean_inc(v_i_1142_);
        v___f_1151_ = lean_alloc_closure(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forM_loop___redArg___lam__0___boxed as *mut core::ffi::c_void, 6, 5);
        lean_closure_set(v___f_1151_, 0, v_i_1142_);
        lean_closure_set(v___f_1151_, 1, v_step_1144_);
        lean_closure_set(v___f_1151_, 2, v_inst_1139_);
        lean_closure_set(v___f_1151_, 3, v_range_1140_);
        lean_closure_set(v___f_1151_, 4, v_f_1141_);
        v___x_1152_ = lean_apply_1(v_f_1141_, v_i_1142_);
        v___x_1153_ = lean_apply_4(
            v_toBind_1150_,
            lean_box(0),
            lean_box(0),
            v___x_1152_,
            v___f_1151_,
        );
        return v___x_1153_;
    }
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forM_loop___redArg___lam__0(
    mut v_i_1154_: *mut LeanObject,
    mut v_step_1155_: *mut LeanObject,
    mut v_inst_1156_: *mut LeanObject,
    mut v_range_1157_: *mut LeanObject,
    mut v_f_1158_: *mut LeanObject,
    mut v_____r_1159_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut LeanObject = core::ptr::null_mut();
    v___x_1160_ = lean_nat_add(v_i_1154_, v_step_1155_);
    v___x_1161_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forM_loop___redArg(
        v_inst_1156_,
        v_range_1157_,
        v_f_1158_,
        v___x_1160_,
    );
    return v___x_1161_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forM_loop(
    mut v_m_1162_: *mut LeanObject,
    mut v_inst_1163_: *mut LeanObject,
    mut v_range_1164_: *mut LeanObject,
    mut v_f_1165_: *mut LeanObject,
    mut v_i_1166_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1167_: *mut LeanObject = core::ptr::null_mut();
    v___x_1167_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forM_loop___redArg(
        v_inst_1163_,
        v_range_1164_,
        v_f_1165_,
        v_i_1166_,
    );
    return v___x_1167_;
}
pub unsafe fn l_Std_Legacy_Range_forM___redArg(
    mut v_inst_1168_: *mut LeanObject,
    mut v_range_1169_: *mut LeanObject,
    mut v_f_1170_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_start_1171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1172_: *mut LeanObject = core::ptr::null_mut();
    v_start_1171_ = lean_ctor_get(v_range_1169_, 0);
    lean_inc(v_start_1171_);
    v___x_1172_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forM_loop___redArg(
        v_inst_1168_,
        v_range_1169_,
        v_f_1170_,
        v_start_1171_,
    );
    return v___x_1172_;
}
pub unsafe fn l_Std_Legacy_Range_forM(
    mut v_m_1173_: *mut LeanObject,
    mut v_inst_1174_: *mut LeanObject,
    mut v_range_1175_: *mut LeanObject,
    mut v_f_1176_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_start_1177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1178_: *mut LeanObject = core::ptr::null_mut();
    v_start_1177_ = lean_ctor_get(v_range_1175_, 0);
    lean_inc(v_start_1177_);
    v___x_1178_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forM_loop___redArg(
        v_inst_1174_,
        v_range_1175_,
        v_f_1176_,
        v_start_1177_,
    );
    return v___x_1178_;
}
pub unsafe fn l_Std_Legacy_Range_instForMNatOfMonad___redArg(
    mut v_inst_1179_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1180_: *mut LeanObject = core::ptr::null_mut();
    v___x_1180_ = lean_alloc_closure(l_Std_Legacy_Range_forM as *mut core::ffi::c_void, 4, 2);
    lean_closure_set(v___x_1180_, 0, lean_box(0));
    lean_closure_set(v___x_1180_, 1, v_inst_1179_);
    return v___x_1180_;
}
pub unsafe fn l_Std_Legacy_Range_instForMNatOfMonad(
    mut v_m_1181_: *mut LeanObject,
    mut v_inst_1182_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1183_: *mut LeanObject = core::ptr::null_mut();
    v___x_1183_ = lean_alloc_closure(l_Std_Legacy_Range_forM as *mut core::ffi::c_void, 4, 2);
    lean_closure_set(v___x_1183_, 0, lean_box(0));
    lean_closure_set(v___x_1183_, 1, v_inst_1182_);
    return v___x_1183_;
}
pub unsafe fn _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__4()
-> *mut LeanObject {
    let mut v___x_1332_: *mut LeanObject = core::ptr::null_mut();
    v___x_1332_ = l_Array_mkArray0(lean_box(0));
    return v___x_1332_;
}
pub unsafe fn _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__12()
-> *mut LeanObject {
    let mut v___x_1352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut LeanObject = core::ptr::null_mut();
    v___x_1352_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__11;
    v___x_1353_ = l_String_toRawSubstring_x27(v___x_1352_);
    return v___x_1353_;
}
pub unsafe fn _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__22()
-> *mut LeanObject {
    let mut v___x_1376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut LeanObject = core::ptr::null_mut();
    v___x_1376_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__21;
    v___x_1377_ = l_String_toRawSubstring_x27(v___x_1376_);
    return v___x_1377_;
}
pub unsafe fn _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__28()
-> *mut LeanObject {
    let mut v___x_1392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut LeanObject = core::ptr::null_mut();
    v___x_1392_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__27;
    v___x_1393_ = l_String_toRawSubstring_x27(v___x_1392_);
    return v___x_1393_;
}
pub unsafe fn _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__36()
-> *mut LeanObject {
    let mut v___x_1411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: *mut LeanObject = core::ptr::null_mut();
    v___x_1411_ = l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__2;
    v___x_1412_ = l_String_toRawSubstring_x27(v___x_1411_);
    return v___x_1412_;
}
pub unsafe fn l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1(
    mut v_x_1431_: *mut LeanObject,
    mut v_a_1432_: *mut LeanObject,
    mut v_a_1433_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: u8 = 0;
    v___x_1434_ = l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__4;
    lean_inc(v_x_1431_);
    v___x_1435_ = l_Lean_Syntax_isOfKind(v_x_1431_, v___x_1434_);
    if v___x_1435_ == 0 {
        let mut v___x_1436_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1437_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_1431_);
        v___x_1436_ = lean_box(1);
        v___x_1437_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_1437_, 0, v___x_1436_);
        lean_ctor_set(v___x_1437_, 1, v_a_1433_);
        return v___x_1437_;
    } else {
        let mut v_quotContext_1438_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_1439_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_1440_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1441_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1442_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1443_: u8 = 0;
        let mut v___x_1444_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1445_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1446_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1447_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1448_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1449_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1450_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1451_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1452_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1453_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1454_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1455_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1456_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1457_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1458_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1459_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1460_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1461_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1462_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1463_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1464_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1465_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1466_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1467_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1468_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1469_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1470_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1471_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1472_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1473_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1474_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1475_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1476_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1477_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1478_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1479_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1480_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1481_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1482_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1483_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1484_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1485_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1486_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1487_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1488_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1489_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1490_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1491_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1492_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1493_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1494_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1495_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1496_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1497_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_1438_ = lean_ctor_get(v_a_1432_, 1);
        v_currMacroScope_1439_ = lean_ctor_get(v_a_1432_, 2);
        v_ref_1440_ = lean_ctor_get(v_a_1432_, 5);
        v___x_1441_ = lean_unsigned_to_nat(2);
        v___x_1442_ = l_Lean_Syntax_getArg(v_x_1431_, v___x_1441_);
        lean_dec(v_x_1431_);
        v___x_1443_ = 0;
        v___x_1444_ = l_Lean_SourceInfo_fromRef(v_ref_1440_, v___x_1443_);
        v___x_1445_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__2;
        v___x_1446_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__3;
        lean_inc_n(v___x_1444_, 22);
        v___x_1447_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1447_, 0, v___x_1444_);
        lean_ctor_set(v___x_1447_, 1, v___x_1446_);
        v___x_1448_ =
            l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__9;
        v___x_1449_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__4), core::ptr::addr_of_mut!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__4_once), _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__4);
        v___x_1450_ = lean_alloc_ctor(1, 3, (0) as u32);
        lean_ctor_set(v___x_1450_, 0, v___x_1444_);
        lean_ctor_set(v___x_1450_, 1, v___x_1448_);
        lean_ctor_set(v___x_1450_, 2, v___x_1449_);
        v___x_1451_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__6;
        v___x_1452_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__8;
        v___x_1453_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__10;
        v___x_1454_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__12), core::ptr::addr_of_mut!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__12_once), _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__12);
        v___x_1455_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__13;
        lean_inc_n(v_currMacroScope_1439_, 4);
        lean_inc_n(v_quotContext_1438_, 4);
        v___x_1456_ =
            l_Lean_addMacroScope(v_quotContext_1438_, v___x_1455_, v_currMacroScope_1439_);
        v___x_1457_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__16;
        v___x_1458_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1458_, 0, v___x_1444_);
        lean_ctor_set(v___x_1458_, 1, v___x_1454_);
        lean_ctor_set(v___x_1458_, 2, v___x_1456_);
        lean_ctor_set(v___x_1458_, 3, v___x_1457_);
        lean_inc_ref_n(v___x_1450_, 9);
        v___x_1459_ = l_Lean_Syntax_node2(v___x_1444_, v___x_1453_, v___x_1458_, v___x_1450_);
        v___x_1460_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__18;
        v___x_1461_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__19;
        v___x_1462_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1462_, 0, v___x_1444_);
        lean_ctor_set(v___x_1462_, 1, v___x_1461_);
        lean_inc_ref(v___x_1462_);
        v___x_1463_ = l_Lean_Syntax_node3(
            v___x_1444_,
            v___x_1460_,
            v___x_1462_,
            v___x_1450_,
            v___x_1442_,
        );
        v___x_1464_ = l_Lean_Syntax_node3(
            v___x_1444_,
            v___x_1448_,
            v___x_1450_,
            v___x_1450_,
            v___x_1463_,
        );
        v___x_1465_ = l_Lean_Syntax_node2(v___x_1444_, v___x_1452_, v___x_1459_, v___x_1464_);
        v___x_1466_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__20;
        v___x_1467_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1467_, 0, v___x_1444_);
        lean_ctor_set(v___x_1467_, 1, v___x_1466_);
        v___x_1468_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__22), core::ptr::addr_of_mut!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__22_once), _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__22);
        v___x_1469_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__23;
        v___x_1470_ =
            l_Lean_addMacroScope(v_quotContext_1438_, v___x_1469_, v_currMacroScope_1439_);
        v___x_1471_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__26;
        v___x_1472_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1472_, 0, v___x_1444_);
        lean_ctor_set(v___x_1472_, 1, v___x_1468_);
        lean_ctor_set(v___x_1472_, 2, v___x_1470_);
        lean_ctor_set(v___x_1472_, 3, v___x_1471_);
        v___x_1473_ = l_Lean_Syntax_node2(v___x_1444_, v___x_1453_, v___x_1472_, v___x_1450_);
        v___x_1474_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__28), core::ptr::addr_of_mut!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__28_once), _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__28);
        v___x_1475_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__31;
        v___x_1476_ =
            l_Lean_addMacroScope(v_quotContext_1438_, v___x_1475_, v_currMacroScope_1439_);
        v___x_1477_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__33;
        v___x_1478_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1478_, 0, v___x_1444_);
        lean_ctor_set(v___x_1478_, 1, v___x_1474_);
        lean_ctor_set(v___x_1478_, 2, v___x_1476_);
        lean_ctor_set(v___x_1478_, 3, v___x_1477_);
        v___x_1479_ = l_Lean_Syntax_node3(
            v___x_1444_,
            v___x_1460_,
            v___x_1462_,
            v___x_1450_,
            v___x_1478_,
        );
        v___x_1480_ = l_Lean_Syntax_node3(
            v___x_1444_,
            v___x_1448_,
            v___x_1450_,
            v___x_1450_,
            v___x_1479_,
        );
        v___x_1481_ = l_Lean_Syntax_node2(v___x_1444_, v___x_1452_, v___x_1473_, v___x_1480_);
        v___x_1482_ = l_Lean_Syntax_node3(
            v___x_1444_,
            v___x_1448_,
            v___x_1465_,
            v___x_1467_,
            v___x_1481_,
        );
        v___x_1483_ = l_Lean_Syntax_node1(v___x_1444_, v___x_1451_, v___x_1482_);
        v___x_1484_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__35;
        v___x_1485_ = l_Lean_Syntax_node1(v___x_1444_, v___x_1484_, v___x_1450_);
        v___x_1486_ = l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__11;
        v___x_1487_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1487_, 0, v___x_1444_);
        lean_ctor_set(v___x_1487_, 1, v___x_1486_);
        v___x_1488_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__36), core::ptr::addr_of_mut!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__36_once), _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__36);
        v___x_1489_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__37;
        v___x_1490_ =
            l_Lean_addMacroScope(v_quotContext_1438_, v___x_1489_, v_currMacroScope_1439_);
        v___x_1491_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__42;
        v___x_1492_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1492_, 0, v___x_1444_);
        lean_ctor_set(v___x_1492_, 1, v___x_1488_);
        lean_ctor_set(v___x_1492_, 2, v___x_1490_);
        lean_ctor_set(v___x_1492_, 3, v___x_1491_);
        v___x_1493_ = l_Lean_Syntax_node2(v___x_1444_, v___x_1448_, v___x_1487_, v___x_1492_);
        v___x_1494_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__43;
        v___x_1495_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1495_, 0, v___x_1444_);
        lean_ctor_set(v___x_1495_, 1, v___x_1494_);
        v___x_1496_ = l_Lean_Syntax_node6(
            v___x_1444_,
            v___x_1445_,
            v___x_1447_,
            v___x_1450_,
            v___x_1483_,
            v___x_1485_,
            v___x_1493_,
            v___x_1495_,
        );
        v___x_1497_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_1497_, 0, v___x_1496_);
        lean_ctor_set(v___x_1497_, 1, v_a_1433_);
        return v___x_1497_;
    }
}
pub unsafe fn l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___boxed(
    mut v_x_1498_: *mut LeanObject,
    mut v_a_1499_: *mut LeanObject,
    mut v_a_1500_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1501_: *mut LeanObject = core::ptr::null_mut();
    v_res_1501_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1(v_x_1498_, v_a_1499_, v_a_1500_);
    lean_dec_ref(v_a_1499_);
    return v_res_1501_;
}
pub unsafe fn _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__1()
-> *mut LeanObject {
    let mut v___x_1503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut LeanObject = core::ptr::null_mut();
    v___x_1503_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__0;
    v___x_1504_ = l_String_toRawSubstring_x27(v___x_1503_);
    return v___x_1504_;
}
pub unsafe fn l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1(
    mut v_x_1518_: *mut LeanObject,
    mut v_a_1519_: *mut LeanObject,
    mut v_a_1520_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: u8 = 0;
    v___x_1521_ = l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__1;
    lean_inc(v_x_1518_);
    v___x_1522_ = l_Lean_Syntax_isOfKind(v_x_1518_, v___x_1521_);
    if v___x_1522_ == 0 {
        let mut v___x_1523_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1524_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_1518_);
        v___x_1523_ = lean_box(1);
        v___x_1524_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_1524_, 0, v___x_1523_);
        lean_ctor_set(v___x_1524_, 1, v_a_1520_);
        return v___x_1524_;
    } else {
        let mut v_quotContext_1525_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_1526_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_1527_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1528_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1529_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1530_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1531_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1532_: u8 = 0;
        let mut v___x_1533_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1534_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1535_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1536_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1537_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1538_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1539_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1540_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1541_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1542_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1543_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1544_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1545_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1546_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1547_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1548_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1549_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1550_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1551_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1552_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1553_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1554_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1555_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1556_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1557_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1558_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1559_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1560_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1561_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1562_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1563_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1564_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1565_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1566_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1567_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1568_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1569_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1570_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1571_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1572_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1573_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1574_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1575_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1576_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1577_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1578_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1579_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1580_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1581_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1582_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1583_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1584_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1585_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1586_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1587_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1588_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1589_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1590_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1591_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1592_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1593_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1594_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1595_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_1525_ = lean_ctor_get(v_a_1519_, 1);
        v_currMacroScope_1526_ = lean_ctor_get(v_a_1519_, 2);
        v_ref_1527_ = lean_ctor_get(v_a_1519_, 5);
        v___x_1528_ = lean_unsigned_to_nat(1);
        v___x_1529_ = l_Lean_Syntax_getArg(v_x_1518_, v___x_1528_);
        v___x_1530_ = lean_unsigned_to_nat(3);
        v___x_1531_ = l_Lean_Syntax_getArg(v_x_1518_, v___x_1530_);
        lean_dec(v_x_1518_);
        v___x_1532_ = 0;
        v___x_1533_ = l_Lean_SourceInfo_fromRef(v_ref_1527_, v___x_1532_);
        v___x_1534_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__2;
        v___x_1535_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__3;
        lean_inc_n(v___x_1533_, 27);
        v___x_1536_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1536_, 0, v___x_1533_);
        lean_ctor_set(v___x_1536_, 1, v___x_1535_);
        v___x_1537_ =
            l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__9;
        v___x_1538_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__4), core::ptr::addr_of_mut!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__4_once), _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__4);
        v___x_1539_ = lean_alloc_ctor(1, 3, (0) as u32);
        lean_ctor_set(v___x_1539_, 0, v___x_1533_);
        lean_ctor_set(v___x_1539_, 1, v___x_1537_);
        lean_ctor_set(v___x_1539_, 2, v___x_1538_);
        v___x_1540_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__6;
        v___x_1541_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__8;
        v___x_1542_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__10;
        v___x_1543_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__1), core::ptr::addr_of_mut!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__1_once), _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__1);
        v___x_1544_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__2;
        lean_inc_n(v_currMacroScope_1526_, 5);
        lean_inc_n(v_quotContext_1525_, 5);
        v___x_1545_ =
            l_Lean_addMacroScope(v_quotContext_1525_, v___x_1544_, v_currMacroScope_1526_);
        v___x_1546_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__5;
        v___x_1547_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1547_, 0, v___x_1533_);
        lean_ctor_set(v___x_1547_, 1, v___x_1543_);
        lean_ctor_set(v___x_1547_, 2, v___x_1545_);
        lean_ctor_set(v___x_1547_, 3, v___x_1546_);
        lean_inc_ref_n(v___x_1539_, 13);
        v___x_1548_ = l_Lean_Syntax_node2(v___x_1533_, v___x_1542_, v___x_1547_, v___x_1539_);
        v___x_1549_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__18;
        v___x_1550_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__19;
        v___x_1551_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1551_, 0, v___x_1533_);
        lean_ctor_set(v___x_1551_, 1, v___x_1550_);
        lean_inc_ref_n(v___x_1551_, 2);
        v___x_1552_ = l_Lean_Syntax_node3(
            v___x_1533_,
            v___x_1549_,
            v___x_1551_,
            v___x_1539_,
            v___x_1529_,
        );
        v___x_1553_ = l_Lean_Syntax_node3(
            v___x_1533_,
            v___x_1537_,
            v___x_1539_,
            v___x_1539_,
            v___x_1552_,
        );
        v___x_1554_ = l_Lean_Syntax_node2(v___x_1533_, v___x_1541_, v___x_1548_, v___x_1553_);
        v___x_1555_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__20;
        v___x_1556_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1556_, 0, v___x_1533_);
        lean_ctor_set(v___x_1556_, 1, v___x_1555_);
        v___x_1557_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__12), core::ptr::addr_of_mut!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__12_once), _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__12);
        v___x_1558_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__13;
        v___x_1559_ =
            l_Lean_addMacroScope(v_quotContext_1525_, v___x_1558_, v_currMacroScope_1526_);
        v___x_1560_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__16;
        v___x_1561_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1561_, 0, v___x_1533_);
        lean_ctor_set(v___x_1561_, 1, v___x_1557_);
        lean_ctor_set(v___x_1561_, 2, v___x_1559_);
        lean_ctor_set(v___x_1561_, 3, v___x_1560_);
        v___x_1562_ = l_Lean_Syntax_node2(v___x_1533_, v___x_1542_, v___x_1561_, v___x_1539_);
        v___x_1563_ = l_Lean_Syntax_node3(
            v___x_1533_,
            v___x_1549_,
            v___x_1551_,
            v___x_1539_,
            v___x_1531_,
        );
        v___x_1564_ = l_Lean_Syntax_node3(
            v___x_1533_,
            v___x_1537_,
            v___x_1539_,
            v___x_1539_,
            v___x_1563_,
        );
        v___x_1565_ = l_Lean_Syntax_node2(v___x_1533_, v___x_1541_, v___x_1562_, v___x_1564_);
        v___x_1566_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__22), core::ptr::addr_of_mut!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__22_once), _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__22);
        v___x_1567_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__23;
        v___x_1568_ =
            l_Lean_addMacroScope(v_quotContext_1525_, v___x_1567_, v_currMacroScope_1526_);
        v___x_1569_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__26;
        v___x_1570_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1570_, 0, v___x_1533_);
        lean_ctor_set(v___x_1570_, 1, v___x_1566_);
        lean_ctor_set(v___x_1570_, 2, v___x_1568_);
        lean_ctor_set(v___x_1570_, 3, v___x_1569_);
        v___x_1571_ = l_Lean_Syntax_node2(v___x_1533_, v___x_1542_, v___x_1570_, v___x_1539_);
        v___x_1572_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__28), core::ptr::addr_of_mut!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__28_once), _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__28);
        v___x_1573_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__31;
        v___x_1574_ =
            l_Lean_addMacroScope(v_quotContext_1525_, v___x_1573_, v_currMacroScope_1526_);
        v___x_1575_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__33;
        v___x_1576_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1576_, 0, v___x_1533_);
        lean_ctor_set(v___x_1576_, 1, v___x_1572_);
        lean_ctor_set(v___x_1576_, 2, v___x_1574_);
        lean_ctor_set(v___x_1576_, 3, v___x_1575_);
        v___x_1577_ = l_Lean_Syntax_node3(
            v___x_1533_,
            v___x_1549_,
            v___x_1551_,
            v___x_1539_,
            v___x_1576_,
        );
        v___x_1578_ = l_Lean_Syntax_node3(
            v___x_1533_,
            v___x_1537_,
            v___x_1539_,
            v___x_1539_,
            v___x_1577_,
        );
        v___x_1579_ = l_Lean_Syntax_node2(v___x_1533_, v___x_1541_, v___x_1571_, v___x_1578_);
        lean_inc_ref(v___x_1556_);
        v___x_1580_ = l_Lean_Syntax_node5(
            v___x_1533_,
            v___x_1537_,
            v___x_1554_,
            v___x_1556_,
            v___x_1565_,
            v___x_1556_,
            v___x_1579_,
        );
        v___x_1581_ = l_Lean_Syntax_node1(v___x_1533_, v___x_1540_, v___x_1580_);
        v___x_1582_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__35;
        v___x_1583_ = l_Lean_Syntax_node1(v___x_1533_, v___x_1582_, v___x_1539_);
        v___x_1584_ = l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__11;
        v___x_1585_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1585_, 0, v___x_1533_);
        lean_ctor_set(v___x_1585_, 1, v___x_1584_);
        v___x_1586_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__36), core::ptr::addr_of_mut!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__36_once), _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__36);
        v___x_1587_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__37;
        v___x_1588_ =
            l_Lean_addMacroScope(v_quotContext_1525_, v___x_1587_, v_currMacroScope_1526_);
        v___x_1589_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__42;
        v___x_1590_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1590_, 0, v___x_1533_);
        lean_ctor_set(v___x_1590_, 1, v___x_1586_);
        lean_ctor_set(v___x_1590_, 2, v___x_1588_);
        lean_ctor_set(v___x_1590_, 3, v___x_1589_);
        v___x_1591_ = l_Lean_Syntax_node2(v___x_1533_, v___x_1537_, v___x_1585_, v___x_1590_);
        v___x_1592_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__43;
        v___x_1593_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1593_, 0, v___x_1533_);
        lean_ctor_set(v___x_1593_, 1, v___x_1592_);
        v___x_1594_ = l_Lean_Syntax_node6(
            v___x_1533_,
            v___x_1534_,
            v___x_1536_,
            v___x_1539_,
            v___x_1581_,
            v___x_1583_,
            v___x_1591_,
            v___x_1593_,
        );
        v___x_1595_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_1595_, 0, v___x_1594_);
        lean_ctor_set(v___x_1595_, 1, v_a_1520_);
        return v___x_1595_;
    }
}
pub unsafe fn l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___boxed(
    mut v_x_1596_: *mut LeanObject,
    mut v_a_1597_: *mut LeanObject,
    mut v_a_1598_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1599_: *mut LeanObject = core::ptr::null_mut();
    v_res_1599_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1(v_x_1596_, v_a_1597_, v_a_1598_);
    lean_dec_ref(v_a_1597_);
    return v_res_1599_;
}
pub unsafe fn _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__1()
-> *mut LeanObject {
    let mut v___x_1601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut LeanObject = core::ptr::null_mut();
    v___x_1601_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__0;
    v___x_1602_ = l_String_toRawSubstring_x27(v___x_1601_);
    return v___x_1602_;
}
pub unsafe fn l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1(
    mut v_x_1629_: *mut LeanObject,
    mut v_a_1630_: *mut LeanObject,
    mut v_a_1631_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: u8 = 0;
    v___x_1632_ = l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__1;
    lean_inc(v_x_1629_);
    v___x_1633_ = l_Lean_Syntax_isOfKind(v_x_1629_, v___x_1632_);
    if v___x_1633_ == 0 {
        let mut v___x_1634_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1635_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_1629_);
        v___x_1634_ = lean_box(1);
        v___x_1635_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_1635_, 0, v___x_1634_);
        lean_ctor_set(v___x_1635_, 1, v_a_1631_);
        return v___x_1635_;
    } else {
        let mut v_quotContext_1636_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_1637_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_1638_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1639_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1640_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1641_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1642_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1643_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1644_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1645_: u8 = 0;
        let mut v___x_1646_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1647_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1648_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1649_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1650_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1651_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1652_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1653_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1654_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1655_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1656_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1657_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1658_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1659_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1660_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1661_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1662_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1663_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1664_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1665_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1666_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1667_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1668_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1669_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1670_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1671_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1672_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1673_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1674_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1675_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1676_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1677_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1678_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1679_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1680_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1681_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1682_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1683_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1684_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1685_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1686_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1687_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1688_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1689_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1690_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1691_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1692_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1693_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1694_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1695_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1696_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1697_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1698_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1699_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1700_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1701_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1702_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1703_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1704_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1705_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1706_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1707_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1708_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1709_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1710_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1711_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1712_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1713_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1714_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1715_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1716_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1717_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1718_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1719_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1720_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1721_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1722_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1723_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1724_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1725_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1726_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1727_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_1636_ = lean_ctor_get(v_a_1630_, 1);
        v_currMacroScope_1637_ = lean_ctor_get(v_a_1630_, 2);
        v_ref_1638_ = lean_ctor_get(v_a_1630_, 5);
        v___x_1639_ = lean_unsigned_to_nat(1);
        v___x_1640_ = l_Lean_Syntax_getArg(v_x_1629_, v___x_1639_);
        v___x_1641_ = lean_unsigned_to_nat(3);
        v___x_1642_ = l_Lean_Syntax_getArg(v_x_1629_, v___x_1641_);
        v___x_1643_ = lean_unsigned_to_nat(5);
        v___x_1644_ = l_Lean_Syntax_getArg(v_x_1629_, v___x_1643_);
        lean_dec(v_x_1629_);
        v___x_1645_ = 0;
        v___x_1646_ = l_Lean_SourceInfo_fromRef(v_ref_1638_, v___x_1645_);
        v___x_1647_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__2;
        v___x_1648_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__3;
        lean_inc_n(v___x_1646_, 39);
        v___x_1649_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1649_, 0, v___x_1646_);
        lean_ctor_set(v___x_1649_, 1, v___x_1648_);
        v___x_1650_ =
            l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__9;
        v___x_1651_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__4), core::ptr::addr_of_mut!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__4_once), _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__4);
        v___x_1652_ = lean_alloc_ctor(1, 3, (0) as u32);
        lean_ctor_set(v___x_1652_, 0, v___x_1646_);
        lean_ctor_set(v___x_1652_, 1, v___x_1650_);
        lean_ctor_set(v___x_1652_, 2, v___x_1651_);
        v___x_1653_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__6;
        v___x_1654_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__8;
        v___x_1655_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__10;
        v___x_1656_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__1), core::ptr::addr_of_mut!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__1_once), _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__1);
        v___x_1657_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__2;
        lean_inc_n(v_currMacroScope_1637_, 5);
        lean_inc_n(v_quotContext_1636_, 5);
        v___x_1658_ =
            l_Lean_addMacroScope(v_quotContext_1636_, v___x_1657_, v_currMacroScope_1637_);
        v___x_1659_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__5;
        v___x_1660_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1660_, 0, v___x_1646_);
        lean_ctor_set(v___x_1660_, 1, v___x_1656_);
        lean_ctor_set(v___x_1660_, 2, v___x_1658_);
        lean_ctor_set(v___x_1660_, 3, v___x_1659_);
        lean_inc_ref_n(v___x_1652_, 18);
        v___x_1661_ = l_Lean_Syntax_node2(v___x_1646_, v___x_1655_, v___x_1660_, v___x_1652_);
        v___x_1662_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__18;
        v___x_1663_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__19;
        v___x_1664_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1664_, 0, v___x_1646_);
        lean_ctor_set(v___x_1664_, 1, v___x_1663_);
        lean_inc_ref_n(v___x_1664_, 3);
        v___x_1665_ = l_Lean_Syntax_node3(
            v___x_1646_,
            v___x_1662_,
            v___x_1664_,
            v___x_1652_,
            v___x_1640_,
        );
        v___x_1666_ = l_Lean_Syntax_node3(
            v___x_1646_,
            v___x_1650_,
            v___x_1652_,
            v___x_1652_,
            v___x_1665_,
        );
        v___x_1667_ = l_Lean_Syntax_node2(v___x_1646_, v___x_1654_, v___x_1661_, v___x_1666_);
        v___x_1668_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__20;
        v___x_1669_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1669_, 0, v___x_1646_);
        lean_ctor_set(v___x_1669_, 1, v___x_1668_);
        v___x_1670_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__12), core::ptr::addr_of_mut!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__12_once), _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__12);
        v___x_1671_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__13;
        v___x_1672_ =
            l_Lean_addMacroScope(v_quotContext_1636_, v___x_1671_, v_currMacroScope_1637_);
        v___x_1673_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__16;
        v___x_1674_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1674_, 0, v___x_1646_);
        lean_ctor_set(v___x_1674_, 1, v___x_1670_);
        lean_ctor_set(v___x_1674_, 2, v___x_1672_);
        lean_ctor_set(v___x_1674_, 3, v___x_1673_);
        v___x_1675_ = l_Lean_Syntax_node2(v___x_1646_, v___x_1655_, v___x_1674_, v___x_1652_);
        v___x_1676_ = l_Lean_Syntax_node3(
            v___x_1646_,
            v___x_1662_,
            v___x_1664_,
            v___x_1652_,
            v___x_1642_,
        );
        v___x_1677_ = l_Lean_Syntax_node3(
            v___x_1646_,
            v___x_1650_,
            v___x_1652_,
            v___x_1652_,
            v___x_1676_,
        );
        v___x_1678_ = l_Lean_Syntax_node2(v___x_1646_, v___x_1654_, v___x_1675_, v___x_1677_);
        v___x_1679_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__1), core::ptr::addr_of_mut!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__1_once), _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__1);
        v___x_1680_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__2;
        v___x_1681_ =
            l_Lean_addMacroScope(v_quotContext_1636_, v___x_1680_, v_currMacroScope_1637_);
        v___x_1682_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__5;
        v___x_1683_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1683_, 0, v___x_1646_);
        lean_ctor_set(v___x_1683_, 1, v___x_1679_);
        lean_ctor_set(v___x_1683_, 2, v___x_1681_);
        lean_ctor_set(v___x_1683_, 3, v___x_1682_);
        v___x_1684_ = l_Lean_Syntax_node2(v___x_1646_, v___x_1655_, v___x_1683_, v___x_1652_);
        v___x_1685_ = l_Lean_Syntax_node3(
            v___x_1646_,
            v___x_1662_,
            v___x_1664_,
            v___x_1652_,
            v___x_1644_,
        );
        v___x_1686_ = l_Lean_Syntax_node3(
            v___x_1646_,
            v___x_1650_,
            v___x_1652_,
            v___x_1652_,
            v___x_1685_,
        );
        v___x_1687_ = l_Lean_Syntax_node2(v___x_1646_, v___x_1654_, v___x_1684_, v___x_1686_);
        v___x_1688_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__22), core::ptr::addr_of_mut!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__22_once), _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__22);
        v___x_1689_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__23;
        v___x_1690_ =
            l_Lean_addMacroScope(v_quotContext_1636_, v___x_1689_, v_currMacroScope_1637_);
        v___x_1691_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__26;
        v___x_1692_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1692_, 0, v___x_1646_);
        lean_ctor_set(v___x_1692_, 1, v___x_1688_);
        lean_ctor_set(v___x_1692_, 2, v___x_1690_);
        lean_ctor_set(v___x_1692_, 3, v___x_1691_);
        v___x_1693_ = l_Lean_Syntax_node2(v___x_1646_, v___x_1655_, v___x_1692_, v___x_1652_);
        v___x_1694_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__7;
        v___x_1695_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__8;
        v___x_1696_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1696_, 0, v___x_1646_);
        lean_ctor_set(v___x_1696_, 1, v___x_1695_);
        v___x_1697_ =
            l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__4;
        v___x_1698_ =
            l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__7;
        v___x_1699_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__9;
        v___x_1700_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__10;
        v___x_1701_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1701_, 0, v___x_1646_);
        lean_ctor_set(v___x_1701_, 1, v___x_1699_);
        v___x_1702_ =
            l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__15;
        v___x_1703_ = l_Lean_Syntax_node1(v___x_1646_, v___x_1702_, v___x_1652_);
        v___x_1704_ = l_Lean_Syntax_node2(v___x_1646_, v___x_1700_, v___x_1701_, v___x_1703_);
        v___x_1705_ = l_Lean_Syntax_node1(v___x_1646_, v___x_1650_, v___x_1704_);
        v___x_1706_ = l_Lean_Syntax_node1(v___x_1646_, v___x_1698_, v___x_1705_);
        v___x_1707_ = l_Lean_Syntax_node1(v___x_1646_, v___x_1697_, v___x_1706_);
        v___x_1708_ = l_Lean_Syntax_node2(v___x_1646_, v___x_1694_, v___x_1696_, v___x_1707_);
        v___x_1709_ = l_Lean_Syntax_node3(
            v___x_1646_,
            v___x_1662_,
            v___x_1664_,
            v___x_1652_,
            v___x_1708_,
        );
        v___x_1710_ = l_Lean_Syntax_node3(
            v___x_1646_,
            v___x_1650_,
            v___x_1652_,
            v___x_1652_,
            v___x_1709_,
        );
        v___x_1711_ = l_Lean_Syntax_node2(v___x_1646_, v___x_1654_, v___x_1693_, v___x_1710_);
        lean_inc_ref_n(v___x_1669_, 2);
        v___x_1712_ = l_Lean_Syntax_node7(
            v___x_1646_,
            v___x_1650_,
            v___x_1667_,
            v___x_1669_,
            v___x_1678_,
            v___x_1669_,
            v___x_1687_,
            v___x_1669_,
            v___x_1711_,
        );
        v___x_1713_ = l_Lean_Syntax_node1(v___x_1646_, v___x_1653_, v___x_1712_);
        v___x_1714_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__35;
        v___x_1715_ = l_Lean_Syntax_node1(v___x_1646_, v___x_1714_, v___x_1652_);
        v___x_1716_ = l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__11;
        v___x_1717_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1717_, 0, v___x_1646_);
        lean_ctor_set(v___x_1717_, 1, v___x_1716_);
        v___x_1718_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__36), core::ptr::addr_of_mut!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__36_once), _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__36);
        v___x_1719_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__37;
        v___x_1720_ =
            l_Lean_addMacroScope(v_quotContext_1636_, v___x_1719_, v_currMacroScope_1637_);
        v___x_1721_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__42;
        v___x_1722_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1722_, 0, v___x_1646_);
        lean_ctor_set(v___x_1722_, 1, v___x_1718_);
        lean_ctor_set(v___x_1722_, 2, v___x_1720_);
        lean_ctor_set(v___x_1722_, 3, v___x_1721_);
        v___x_1723_ = l_Lean_Syntax_node2(v___x_1646_, v___x_1650_, v___x_1717_, v___x_1722_);
        v___x_1724_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__43;
        v___x_1725_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1725_, 0, v___x_1646_);
        lean_ctor_set(v___x_1725_, 1, v___x_1724_);
        v___x_1726_ = l_Lean_Syntax_node6(
            v___x_1646_,
            v___x_1647_,
            v___x_1649_,
            v___x_1652_,
            v___x_1713_,
            v___x_1715_,
            v___x_1723_,
            v___x_1725_,
        );
        v___x_1727_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_1727_, 0, v___x_1726_);
        lean_ctor_set(v___x_1727_, 1, v_a_1631_);
        return v___x_1727_;
    }
}
pub unsafe fn l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___boxed(
    mut v_x_1728_: *mut LeanObject,
    mut v_a_1729_: *mut LeanObject,
    mut v_a_1730_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1731_: *mut LeanObject = core::ptr::null_mut();
    v_res_1731_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1(v_x_1728_, v_a_1729_, v_a_1730_);
    lean_dec_ref(v_a_1729_);
    return v_res_1731_;
}
pub unsafe fn l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x3a___x5d__1(
    mut v_x_1732_: *mut LeanObject,
    mut v_a_1733_: *mut LeanObject,
    mut v_a_1734_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: u8 = 0;
    v___x_1735_ = l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__1;
    lean_inc(v_x_1732_);
    v___x_1736_ = l_Lean_Syntax_isOfKind(v_x_1732_, v___x_1735_);
    if v___x_1736_ == 0 {
        let mut v___x_1737_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1738_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_1732_);
        v___x_1737_ = lean_box(1);
        v___x_1738_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_1738_, 0, v___x_1737_);
        lean_ctor_set(v___x_1738_, 1, v_a_1734_);
        return v___x_1738_;
    } else {
        let mut v_quotContext_1739_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_1740_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_1741_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1742_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1743_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1744_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1745_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1746_: u8 = 0;
        let mut v___x_1747_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1748_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1749_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1750_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1751_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1752_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1753_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1754_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1755_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1756_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1757_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1758_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1759_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1760_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1761_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1762_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1763_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1764_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1765_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1766_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1767_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1768_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1769_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1770_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1771_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1772_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1773_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1774_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1775_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1776_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1777_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1778_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1779_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1780_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1781_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1782_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1783_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1784_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1785_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1786_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1787_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1788_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1789_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1790_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1791_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1792_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1793_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1794_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1795_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1796_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1797_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1798_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1799_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1800_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1801_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1802_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1803_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1804_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1805_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1806_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1807_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1808_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1809_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1810_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1811_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1812_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1813_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1814_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1815_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1816_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1817_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1818_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1819_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_1739_ = lean_ctor_get(v_a_1733_, 1);
        v_currMacroScope_1740_ = lean_ctor_get(v_a_1733_, 2);
        v_ref_1741_ = lean_ctor_get(v_a_1733_, 5);
        v___x_1742_ = lean_unsigned_to_nat(2);
        v___x_1743_ = l_Lean_Syntax_getArg(v_x_1732_, v___x_1742_);
        v___x_1744_ = lean_unsigned_to_nat(4);
        v___x_1745_ = l_Lean_Syntax_getArg(v_x_1732_, v___x_1744_);
        lean_dec(v_x_1732_);
        v___x_1746_ = 0;
        v___x_1747_ = l_Lean_SourceInfo_fromRef(v_ref_1741_, v___x_1746_);
        v___x_1748_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__2;
        v___x_1749_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__3;
        lean_inc_n(v___x_1747_, 34);
        v___x_1750_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1750_, 0, v___x_1747_);
        lean_ctor_set(v___x_1750_, 1, v___x_1749_);
        v___x_1751_ =
            l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__9;
        v___x_1752_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__4), core::ptr::addr_of_mut!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__4_once), _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__4);
        v___x_1753_ = lean_alloc_ctor(1, 3, (0) as u32);
        lean_ctor_set(v___x_1753_, 0, v___x_1747_);
        lean_ctor_set(v___x_1753_, 1, v___x_1751_);
        lean_ctor_set(v___x_1753_, 2, v___x_1752_);
        v___x_1754_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__6;
        v___x_1755_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__8;
        v___x_1756_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__10;
        v___x_1757_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__12), core::ptr::addr_of_mut!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__12_once), _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__12);
        v___x_1758_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__13;
        lean_inc_n(v_currMacroScope_1740_, 4);
        lean_inc_n(v_quotContext_1739_, 4);
        v___x_1759_ =
            l_Lean_addMacroScope(v_quotContext_1739_, v___x_1758_, v_currMacroScope_1740_);
        v___x_1760_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__16;
        v___x_1761_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1761_, 0, v___x_1747_);
        lean_ctor_set(v___x_1761_, 1, v___x_1757_);
        lean_ctor_set(v___x_1761_, 2, v___x_1759_);
        lean_ctor_set(v___x_1761_, 3, v___x_1760_);
        lean_inc_ref_n(v___x_1753_, 14);
        v___x_1762_ = l_Lean_Syntax_node2(v___x_1747_, v___x_1756_, v___x_1761_, v___x_1753_);
        v___x_1763_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__18;
        v___x_1764_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__19;
        v___x_1765_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1765_, 0, v___x_1747_);
        lean_ctor_set(v___x_1765_, 1, v___x_1764_);
        lean_inc_ref_n(v___x_1765_, 2);
        v___x_1766_ = l_Lean_Syntax_node3(
            v___x_1747_,
            v___x_1763_,
            v___x_1765_,
            v___x_1753_,
            v___x_1743_,
        );
        v___x_1767_ = l_Lean_Syntax_node3(
            v___x_1747_,
            v___x_1751_,
            v___x_1753_,
            v___x_1753_,
            v___x_1766_,
        );
        v___x_1768_ = l_Lean_Syntax_node2(v___x_1747_, v___x_1755_, v___x_1762_, v___x_1767_);
        v___x_1769_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__20;
        v___x_1770_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1770_, 0, v___x_1747_);
        lean_ctor_set(v___x_1770_, 1, v___x_1769_);
        v___x_1771_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__1), core::ptr::addr_of_mut!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__1_once), _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__1);
        v___x_1772_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__2;
        v___x_1773_ =
            l_Lean_addMacroScope(v_quotContext_1739_, v___x_1772_, v_currMacroScope_1740_);
        v___x_1774_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__5;
        v___x_1775_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1775_, 0, v___x_1747_);
        lean_ctor_set(v___x_1775_, 1, v___x_1771_);
        lean_ctor_set(v___x_1775_, 2, v___x_1773_);
        lean_ctor_set(v___x_1775_, 3, v___x_1774_);
        v___x_1776_ = l_Lean_Syntax_node2(v___x_1747_, v___x_1756_, v___x_1775_, v___x_1753_);
        v___x_1777_ = l_Lean_Syntax_node3(
            v___x_1747_,
            v___x_1763_,
            v___x_1765_,
            v___x_1753_,
            v___x_1745_,
        );
        v___x_1778_ = l_Lean_Syntax_node3(
            v___x_1747_,
            v___x_1751_,
            v___x_1753_,
            v___x_1753_,
            v___x_1777_,
        );
        v___x_1779_ = l_Lean_Syntax_node2(v___x_1747_, v___x_1755_, v___x_1776_, v___x_1778_);
        v___x_1780_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__22), core::ptr::addr_of_mut!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__22_once), _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__22);
        v___x_1781_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__23;
        v___x_1782_ =
            l_Lean_addMacroScope(v_quotContext_1739_, v___x_1781_, v_currMacroScope_1740_);
        v___x_1783_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__26;
        v___x_1784_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1784_, 0, v___x_1747_);
        lean_ctor_set(v___x_1784_, 1, v___x_1780_);
        lean_ctor_set(v___x_1784_, 2, v___x_1782_);
        lean_ctor_set(v___x_1784_, 3, v___x_1783_);
        v___x_1785_ = l_Lean_Syntax_node2(v___x_1747_, v___x_1756_, v___x_1784_, v___x_1753_);
        v___x_1786_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__7;
        v___x_1787_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__8;
        v___x_1788_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1788_, 0, v___x_1747_);
        lean_ctor_set(v___x_1788_, 1, v___x_1787_);
        v___x_1789_ =
            l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__4;
        v___x_1790_ =
            l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__7;
        v___x_1791_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__9;
        v___x_1792_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__10;
        v___x_1793_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1793_, 0, v___x_1747_);
        lean_ctor_set(v___x_1793_, 1, v___x_1791_);
        v___x_1794_ =
            l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__15;
        v___x_1795_ = l_Lean_Syntax_node1(v___x_1747_, v___x_1794_, v___x_1753_);
        v___x_1796_ = l_Lean_Syntax_node2(v___x_1747_, v___x_1792_, v___x_1793_, v___x_1795_);
        v___x_1797_ = l_Lean_Syntax_node1(v___x_1747_, v___x_1751_, v___x_1796_);
        v___x_1798_ = l_Lean_Syntax_node1(v___x_1747_, v___x_1790_, v___x_1797_);
        v___x_1799_ = l_Lean_Syntax_node1(v___x_1747_, v___x_1789_, v___x_1798_);
        v___x_1800_ = l_Lean_Syntax_node2(v___x_1747_, v___x_1786_, v___x_1788_, v___x_1799_);
        v___x_1801_ = l_Lean_Syntax_node3(
            v___x_1747_,
            v___x_1763_,
            v___x_1765_,
            v___x_1753_,
            v___x_1800_,
        );
        v___x_1802_ = l_Lean_Syntax_node3(
            v___x_1747_,
            v___x_1751_,
            v___x_1753_,
            v___x_1753_,
            v___x_1801_,
        );
        v___x_1803_ = l_Lean_Syntax_node2(v___x_1747_, v___x_1755_, v___x_1785_, v___x_1802_);
        lean_inc_ref(v___x_1770_);
        v___x_1804_ = l_Lean_Syntax_node5(
            v___x_1747_,
            v___x_1751_,
            v___x_1768_,
            v___x_1770_,
            v___x_1779_,
            v___x_1770_,
            v___x_1803_,
        );
        v___x_1805_ = l_Lean_Syntax_node1(v___x_1747_, v___x_1754_, v___x_1804_);
        v___x_1806_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__35;
        v___x_1807_ = l_Lean_Syntax_node1(v___x_1747_, v___x_1806_, v___x_1753_);
        v___x_1808_ = l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__11;
        v___x_1809_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1809_, 0, v___x_1747_);
        lean_ctor_set(v___x_1809_, 1, v___x_1808_);
        v___x_1810_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__36), core::ptr::addr_of_mut!(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__36_once), _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__36);
        v___x_1811_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__37;
        v___x_1812_ =
            l_Lean_addMacroScope(v_quotContext_1739_, v___x_1811_, v_currMacroScope_1740_);
        v___x_1813_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__42;
        v___x_1814_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1814_, 0, v___x_1747_);
        lean_ctor_set(v___x_1814_, 1, v___x_1810_);
        lean_ctor_set(v___x_1814_, 2, v___x_1812_);
        lean_ctor_set(v___x_1814_, 3, v___x_1813_);
        v___x_1815_ = l_Lean_Syntax_node2(v___x_1747_, v___x_1751_, v___x_1809_, v___x_1814_);
        v___x_1816_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__43;
        v___x_1817_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1817_, 0, v___x_1747_);
        lean_ctor_set(v___x_1817_, 1, v___x_1816_);
        v___x_1818_ = l_Lean_Syntax_node6(
            v___x_1747_,
            v___x_1748_,
            v___x_1750_,
            v___x_1753_,
            v___x_1805_,
            v___x_1807_,
            v___x_1815_,
            v___x_1817_,
        );
        v___x_1819_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_1819_, 0, v___x_1818_);
        lean_ctor_set(v___x_1819_, 1, v_a_1734_);
        return v___x_1819_;
    }
}
pub unsafe fn l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x3a___x5d__1___boxed(
    mut v_x_1820_: *mut LeanObject,
    mut v_a_1821_: *mut LeanObject,
    mut v_a_1822_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1823_: *mut LeanObject = core::ptr::null_mut();
    v_res_1823_ = l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x3a___x5d__1(v_x_1820_, v_a_1821_, v_a_1822_);
    lean_dec_ref(v_a_1821_);
    return v_res_1823_;
}
pub unsafe fn _init_l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__7()
-> *mut LeanObject {
    let mut v___x_1840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut LeanObject = core::ptr::null_mut();
    v___x_1840_ = l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__6;
    v___x_1841_ = l_String_toRawSubstring_x27(v___x_1840_);
    return v___x_1841_;
}
pub unsafe fn l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1(
    mut v_x_1867_: *mut LeanObject,
    mut v_a_1868_: *mut LeanObject,
    mut v_a_1869_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: u8 = 0;
    v___x_1870_ = l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__1;
    v___x_1871_ = l_Lean_Syntax_isOfKind(v_x_1867_, v___x_1870_);
    if v___x_1871_ == 0 {
        let mut v___x_1872_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1873_: *mut LeanObject = core::ptr::null_mut();
        v___x_1872_ = lean_box(1);
        v___x_1873_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_1873_, 0, v___x_1872_);
        lean_ctor_set(v___x_1873_, 1, v_a_1869_);
        return v___x_1873_;
    } else {
        let mut v_quotContext_1874_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_1875_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_1876_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1877_: u8 = 0;
        let mut v___x_1878_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1879_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1880_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1881_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1882_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1883_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1884_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1885_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1886_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1887_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1888_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1889_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1890_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1891_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1892_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1893_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1894_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1895_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1896_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1897_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1898_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1899_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1900_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1901_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1902_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_1874_ = lean_ctor_get(v_a_1868_, 1);
        v_currMacroScope_1875_ = lean_ctor_get(v_a_1868_, 2);
        v_ref_1876_ = lean_ctor_get(v_a_1868_, 5);
        v___x_1877_ = 0;
        v___x_1878_ = l_Lean_SourceInfo_fromRef(v_ref_1876_, v___x_1877_);
        v___x_1879_ = l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3;
        v___x_1880_ =
            l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__9;
        v___x_1881_ = l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4;
        v___x_1882_ = l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__5;
        lean_inc_n(v___x_1878_, 9);
        v___x_1883_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1883_, 0, v___x_1878_);
        lean_ctor_set(v___x_1883_, 1, v___x_1881_);
        v___x_1884_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__7), core::ptr::addr_of_mut!(l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__7_once), _init_l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__7);
        v___x_1885_ = l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__10;
        lean_inc(v_currMacroScope_1875_);
        lean_inc(v_quotContext_1874_);
        v___x_1886_ =
            l_Lean_addMacroScope(v_quotContext_1874_, v___x_1885_, v_currMacroScope_1875_);
        v___x_1887_ = l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__12;
        v___x_1888_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1888_, 0, v___x_1878_);
        lean_ctor_set(v___x_1888_, 1, v___x_1884_);
        lean_ctor_set(v___x_1888_, 2, v___x_1886_);
        lean_ctor_set(v___x_1888_, 3, v___x_1887_);
        v___x_1889_ = l_Lean_Syntax_node2(v___x_1878_, v___x_1882_, v___x_1883_, v___x_1888_);
        v___x_1890_ = l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__13;
        v___x_1891_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1891_, 0, v___x_1878_);
        lean_ctor_set(v___x_1891_, 1, v___x_1890_);
        v___x_1892_ = l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__14;
        v___x_1893_ = l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15;
        v___x_1894_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1894_, 0, v___x_1878_);
        lean_ctor_set(v___x_1894_, 1, v___x_1892_);
        v___x_1895_ = l_Lean_Syntax_node1(v___x_1878_, v___x_1893_, v___x_1894_);
        v___x_1896_ = l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17;
        v___x_1897_ = l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__18;
        v___x_1898_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1898_, 0, v___x_1878_);
        lean_ctor_set(v___x_1898_, 1, v___x_1897_);
        v___x_1899_ = l_Lean_Syntax_node1(v___x_1878_, v___x_1896_, v___x_1898_);
        lean_inc_ref(v___x_1891_);
        v___x_1900_ = l_Lean_Syntax_node5(
            v___x_1878_,
            v___x_1880_,
            v___x_1889_,
            v___x_1891_,
            v___x_1895_,
            v___x_1891_,
            v___x_1899_,
        );
        v___x_1901_ = l_Lean_Syntax_node1(v___x_1878_, v___x_1879_, v___x_1900_);
        v___x_1902_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_1902_, 0, v___x_1901_);
        lean_ctor_set(v___x_1902_, 1, v_a_1869_);
        return v___x_1902_;
    }
}
pub unsafe fn l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___boxed(
    mut v_x_1903_: *mut LeanObject,
    mut v_a_1904_: *mut LeanObject,
    mut v_a_1905_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1906_: *mut LeanObject = core::ptr::null_mut();
    v_res_1906_ =
        l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1(
            v_x_1903_, v_a_1904_, v_a_1905_,
        );
    lean_dec_ref(v_a_1904_);
    return v_res_1906_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Range_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Control_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Tactics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_WFTactics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Std_Legacy_instMembershipNatRange = _init_l_Std_Legacy_instMembershipNatRange();
    lean_mark_persistent(l_Std_Legacy_instMembershipNatRange);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Range_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Init_Grind_Tactics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1 =
        _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1();
    lean_mark_persistent(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Range_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Control_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Grind_Tactics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_WFTactics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Range_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Range_Basic(builtin);
}
