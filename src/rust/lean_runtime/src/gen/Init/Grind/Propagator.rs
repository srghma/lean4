// Lean compiler output
// Module: Init.Grind.Propagator
// Imports: Init.Meta Init.Tactics Init.Meta.Defs
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Meta::Defs::{
    initialize_Init_Meta_Defs, l_Lean_Syntax_isNone, lean_mk_syntax_ident,
    runtime_initialize_Init_Meta_Defs,
};
use crate::r#gen::Init::Meta::{initialize_Init_Meta, meta_initialize_Init_Meta};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Array_mkArray1___redArg, l_Lean_Name_mkStr1, l_Lean_Name_mkStr3,
    l_Lean_Name_mkStr4, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_matchesNull, l_Lean_Syntax_node1, l_Lean_Syntax_node2, l_Lean_Syntax_node3,
    l_Lean_Syntax_node4, l_Lean_Syntax_node5, l_Lean_Syntax_node7,
};
use crate::r#gen::Init::Tactics::{
    initialize_Init_Tactics, l_Lean_Parser_Tactic_simpPost, l_Lean_Parser_Tactic_simpPre,
    runtime_initialize_Init_Tactics,
};
use crate::lean_imports_rs::Init::Prelude::lean_mk_empty_array_with_capacity;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_set,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_n, lean_inc_ref_n,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_mark_persistent, lean_obj_once,
    lean_obj_tag, lean_unsigned_to_nat,
};
pub static l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__0_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__1_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__2_value: LeanStringObject<34> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [99, 111, 109, 109, 97, 110, 100, 95, 71, 114, 105, 110, 100, 95, 112, 114, 111, 112, 97, 103, 97, 116, 111, 114, 95, 95, 95, 40, 95, 41, 58, 61, 95, 0]};
static mut l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__2_value
) as *mut LeanObject;
static l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__2_value) as *mut LeanObject,8162061125005664235 as *mut LeanObject] };
static mut l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__3_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__4_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [97, 110, 100, 116, 104, 101, 110, 0]};
static mut l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__4_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__4_value) as *mut LeanObject,12571085391447129896 as *mut LeanObject] };
static mut l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__5_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__6_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [111, 112, 116, 105, 111, 110, 97, 108, 0]};
static mut l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__6_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__6_value) as *mut LeanObject,18170484695678750185 as *mut LeanObject] };
static mut l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__7_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__8_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [100, 111, 99, 67, 111, 109, 109, 101, 110, 116, 0]};
static mut l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__8_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__9_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__8_value) as *mut LeanObject,3961966953292576997 as *mut LeanObject] };
static mut l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__9:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__9_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__10_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__9_value) as *mut LeanObject] };
static mut l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__10:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__10_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__11_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__7_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__10_value) as *mut LeanObject] };
static mut l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__11:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__11_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__12_value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [103, 114, 105, 110, 100, 95, 112, 114, 111, 112, 97, 103, 97, 116, 111, 114, 32, 0]};
static mut l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__12:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__12_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__13_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__12_value) as *mut LeanObject] };
static mut l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__13:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__13_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__14_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__5_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__11_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__13_value) as *mut LeanObject] };
static mut l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__14:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__14_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__15_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [111, 114, 101, 108, 115, 101, 0]};
static mut l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__15:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__15_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__16_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__15_value) as *mut LeanObject,393173242845875278 as *mut LeanObject] };
static mut l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__16:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__16_value
) as *mut LeanObject;
static mut l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__17_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__17:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__18_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__18:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__19_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__19:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__19_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__20_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__19_value) as *mut LeanObject,5117844058249666356 as *mut LeanObject] };
static mut l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__20:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__20_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__21_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__20_value) as *mut LeanObject] };
static mut l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__21:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__21_value
) as *mut LeanObject;
static mut l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__22_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__22:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__23_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [32, 40, 0]};
static mut l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__23:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__23_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__24_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__23_value) as *mut LeanObject] };
static mut l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__24:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__24_value
) as *mut LeanObject;
static mut l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__25_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__25:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__26_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__26:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__27_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__27:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__27_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__28_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__27_value) as *mut LeanObject] };
static mut l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__28:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__28_value
) as *mut LeanObject;
static mut l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__29_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__29:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__30_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [32, 58, 61, 32, 0]};
static mut l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__30:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__30_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__31_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__30_value) as *mut LeanObject] };
static mut l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__31:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__31_value
) as *mut LeanObject;
static mut l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__32_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__32:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__33_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 101, 114, 109, 0]};
static mut l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__33:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__33_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__34_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__33_value) as *mut LeanObject,8609355255726335675 as *mut LeanObject] };
static mut l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__34:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__34_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__35_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 7 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__34_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__35:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__35_value
) as *mut LeanObject;
static mut l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__36_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__36:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__37_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__37:
    *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d__: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_command__Builtin__grind__propagator_________x3a_x3d___00__closed__0_value: LeanStringObject<40> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 40, m_capacity: 40, m_length: 39, m_data: [99, 111, 109, 109, 97, 110, 100, 95, 66, 117, 105, 108, 116, 105, 110, 95, 103, 114, 105, 110, 100, 95, 112, 114, 111, 112, 97, 103, 97, 116, 111, 114, 95, 95, 95, 95, 58, 61, 95, 0]};
static mut l_Lean_Parser_command__Builtin__grind__propagator_________x3a_x3d___00__closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Builtin__grind__propagator_________x3a_x3d___00__closed__0_value
) as *mut LeanObject;
static l_Lean_Parser_command__Builtin__grind__propagator_________x3a_x3d___00__closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser_command__Builtin__grind__propagator_________x3a_x3d___00__closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command__Builtin__grind__propagator_________x3a_x3d___00__closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l_Lean_Parser_command__Builtin__grind__propagator_________x3a_x3d___00__closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command__Builtin__grind__propagator_________x3a_x3d___00__closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Builtin__grind__propagator_________x3a_x3d___00__closed__0_value) as *mut LeanObject,14298962423613870329 as *mut LeanObject] };
static mut l_Lean_Parser_command__Builtin__grind__propagator_________x3a_x3d___00__closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Builtin__grind__propagator_________x3a_x3d___00__closed__1_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Builtin__grind__propagator_________x3a_x3d___00__closed__2_value: LeanStringObject<26> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [98, 117, 105, 108, 116, 105, 110, 95, 103, 114, 105, 110, 100, 95, 112, 114, 111, 112, 97, 103, 97, 116, 111, 114, 32, 0]};
static mut l_Lean_Parser_command__Builtin__grind__propagator_________x3a_x3d___00__closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Builtin__grind__propagator_________x3a_x3d___00__closed__2_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Builtin__grind__propagator_________x3a_x3d___00__closed__3_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command__Builtin__grind__propagator_________x3a_x3d___00__closed__2_value) as *mut LeanObject] };
static mut l_Lean_Parser_command__Builtin__grind__propagator_________x3a_x3d___00__closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Builtin__grind__propagator_________x3a_x3d___00__closed__3_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Builtin__grind__propagator_________x3a_x3d___00__closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__5_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__11_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Builtin__grind__propagator_________x3a_x3d___00__closed__3_value) as *mut LeanObject] };
static mut l_Lean_Parser_command__Builtin__grind__propagator_________x3a_x3d___00__closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Builtin__grind__propagator_________x3a_x3d___00__closed__4_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Builtin__grind__propagator_________x3a_x3d___00__closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__5_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Builtin__grind__propagator_________x3a_x3d___00__closed__4_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__21_value) as *mut LeanObject] };
static mut l_Lean_Parser_command__Builtin__grind__propagator_________x3a_x3d___00__closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Builtin__grind__propagator_________x3a_x3d___00__closed__5_value
) as *mut LeanObject;
static mut l_Lean_Parser_command__Builtin__grind__propagator_________x3a_x3d___00__closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command__Builtin__grind__propagator_________x3a_x3d___00__closed__6:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command__Builtin__grind__propagator_________x3a_x3d___00__closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command__Builtin__grind__propagator_________x3a_x3d___00__closed__7:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command__Builtin__grind__propagator_________x3a_x3d___00__closed__8_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command__Builtin__grind__propagator_________x3a_x3d___00__closed__8:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command__Builtin__grind__propagator_________x3a_x3d___00__closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command__Builtin__grind__propagator_________x3a_x3d___00__closed__9:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command__Builtin__grind__propagator_________x3a_x3d___00__closed__10_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command__Builtin__grind__propagator_________x3a_x3d___00__closed__10:
    *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_command__Builtin__grind__propagator_________x3a_x3d__:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_grindPropagatorBuiltinAttr___closed__0_value: LeanStringObject<27> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 27,
        m_capacity: 27,
        m_length: 26,
        m_data: [
            103, 114, 105, 110, 100, 80, 114, 111, 112, 97, 103, 97, 116, 111, 114, 66, 117, 105,
            108, 116, 105, 110, 65, 116, 116, 114, 0,
        ],
    };
static mut l_Lean_Parser_grindPropagatorBuiltinAttr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_grindPropagatorBuiltinAttr___closed__0_value)
        as *mut LeanObject;
static l_Lean_Parser_grindPropagatorBuiltinAttr___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser_grindPropagatorBuiltinAttr___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_grindPropagatorBuiltinAttr___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l_Lean_Parser_grindPropagatorBuiltinAttr___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_grindPropagatorBuiltinAttr___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_grindPropagatorBuiltinAttr___closed__0_value)
                as *mut LeanObject,
            2465372125855737269 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_grindPropagatorBuiltinAttr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_grindPropagatorBuiltinAttr___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_grindPropagatorBuiltinAttr___closed__2_value: LeanStringObject<25> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 25,
        m_capacity: 25,
        m_length: 24,
        m_data: [
            98, 117, 105, 108, 116, 105, 110, 95, 103, 114, 105, 110, 100, 95, 112, 114, 111, 112,
            97, 103, 97, 116, 111, 114, 0,
        ],
    };
static mut l_Lean_Parser_grindPropagatorBuiltinAttr___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_grindPropagatorBuiltinAttr___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_grindPropagatorBuiltinAttr___closed__3_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_grindPropagatorBuiltinAttr___closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_grindPropagatorBuiltinAttr___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_grindPropagatorBuiltinAttr___closed__3_value)
        as *mut LeanObject;
static mut l_Lean_Parser_grindPropagatorBuiltinAttr___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_grindPropagatorBuiltinAttr___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_grindPropagatorBuiltinAttr___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_grindPropagatorBuiltinAttr___closed__5: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_grindPropagatorBuiltinAttr___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_grindPropagatorBuiltinAttr___closed__6: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_grindPropagatorBuiltinAttr: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__0_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 0]};
static mut l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__1_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [100, 101, 102, 0]};
static mut l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__2_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [100, 101, 99, 108, 73, 100, 0]};
static mut l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__3_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [111, 112, 116, 68, 101, 99, 108, 83, 105, 103, 0]};
static mut l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__4_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__5_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [116, 121, 112, 101, 83, 112, 101, 99, 0]};
static mut l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__5_value) as *mut LeanObject;
static l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__6_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__6_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__6_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__6_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__6_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__4_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__6_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__5_value) as *mut LeanObject,4498178684837002829 as *mut LeanObject] };
static mut l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__7_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [58, 0]};
static mut l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__7: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__7_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__8_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [100, 101, 99, 108, 86, 97, 108, 83, 105, 109, 112, 108, 101, 0]};
static mut l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__8_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__9_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [58, 61, 0]};
static mut l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__9: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__9_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__10_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [84, 101, 114, 109, 105, 110, 97, 116, 105, 111, 110, 0]};
static mut l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__10_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__11_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 117, 102, 102, 105, 120, 0]};
static mut l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__11: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__11_value) as *mut LeanObject;
static l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__12_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__12_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__12_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__12_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__12_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__10_value) as *mut LeanObject,7625897890118033792 as *mut LeanObject] };
pub static l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__12_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__12_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__11_value) as *mut LeanObject,8715860392475343861 as *mut LeanObject] };
static mut l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__12_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__13_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [97, 116, 116, 114, 105, 98, 117, 116, 101, 0]};
static mut l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__13: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__13_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__14_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [91, 0]};
static mut l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__14: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__14_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__15_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [97, 116, 116, 114, 73, 110, 115, 116, 97, 110, 99, 101, 0]};
static mut l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__15: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__15_value) as *mut LeanObject;
static l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__16_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__16_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__16_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__16_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__16_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__4_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__16_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__16_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__15_value) as *mut LeanObject,7499624980761693169 as *mut LeanObject] };
static mut l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__16: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__16_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__17_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [97, 116, 116, 114, 75, 105, 110, 100, 0]};
static mut l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__17: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__17_value) as *mut LeanObject;
static l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__18_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__18_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__18_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__18_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__18_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__4_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__18_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__18_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__17_value) as *mut LeanObject,7983999284776576032 as *mut LeanObject] };
static mut l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__18: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__18_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__19_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__19: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__19_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__20_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__20: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__20_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__21_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [71, 114, 105, 110, 100, 0]};
static mut l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__21: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__21_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__22_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [80, 114, 111, 112, 97, 103, 97, 116, 111, 114, 0]};
static mut l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__22: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__22_value) as *mut LeanObject;
static l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__23_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__23_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__23_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__20_value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
static l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__23_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__23_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__21_value) as *mut LeanObject,15218882539576375456 as *mut LeanObject] };
pub static l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__23_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__23_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__22_value) as *mut LeanObject,3973629845752699748 as *mut LeanObject] };
static mut l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__23: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__23_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__24_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__24: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__24_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__25_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__24_value) as *mut LeanObject,9855511589286918680 as *mut LeanObject] };
static mut l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__25: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__25_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__26_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [67, 111, 109, 109, 97, 110, 100, 0]};
static mut l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__26: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__26_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__27_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 0]};
static mut l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__27: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__27_value) as *mut LeanObject;
static l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__28_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__28_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__28_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__28_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__28_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__26_value) as *mut LeanObject,17342580262104060118 as *mut LeanObject] };
pub static l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__28_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__28_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__27_value) as *mut LeanObject,8497769072906204829 as *mut LeanObject] };
static mut l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__28: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__28_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__29_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [100, 101, 99, 108, 77, 111, 100, 105, 102, 105, 101, 114, 115, 0]};
static mut l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__29: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__29_value) as *mut LeanObject;
static l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__30_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__30_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__30_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__30_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__30_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__26_value) as *mut LeanObject,17342580262104060118 as *mut LeanObject] };
pub static l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__30_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__30_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__29_value) as *mut LeanObject,14557702332550915328 as *mut LeanObject] };
static mut l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__30: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__30_value) as *mut LeanObject;
static mut l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__31_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__31: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__32_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__32: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__32_value) as *mut LeanObject;
static l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__33_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__33_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__33_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__33_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__33_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__26_value) as *mut LeanObject,17342580262104060118 as *mut LeanObject] };
pub static l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__33_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__33_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__8_value) as *mut LeanObject,9063780239635860524 as *mut LeanObject] };
static mut l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__33: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__33_value) as *mut LeanObject;
pub unsafe fn _init_l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__17()
-> *mut LeanObject {
    let mut v___x_368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_371_: *mut LeanObject = core::ptr::null_mut();
    v___x_368_ = l_Lean_Parser_Tactic_simpPost;
    v___x_369_ = l_Lean_Parser_Tactic_simpPre;
    v___x_370_ = l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__16;
    v___x_371_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_371_, 0, v___x_370_);
    lean_ctor_set(v___x_371_, 1, v___x_369_);
    lean_ctor_set(v___x_371_, 2, v___x_368_);
    return v___x_371_;
}
pub unsafe fn _init_l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__18()
-> *mut LeanObject {
    let mut v___x_372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_375_: *mut LeanObject = core::ptr::null_mut();
    v___x_372_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__17
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__17_once
        ),
        _init_l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__17,
    );
    v___x_373_ = l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__14;
    v___x_374_ = l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__5;
    v___x_375_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_375_, 0, v___x_374_);
    lean_ctor_set(v___x_375_, 1, v___x_373_);
    lean_ctor_set(v___x_375_, 2, v___x_372_);
    return v___x_375_;
}
pub unsafe fn _init_l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__22()
-> *mut LeanObject {
    let mut v___x_381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_384_: *mut LeanObject = core::ptr::null_mut();
    v___x_381_ = l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__21;
    v___x_382_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__18
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__18_once
        ),
        _init_l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__18,
    );
    v___x_383_ = l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__5;
    v___x_384_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_384_, 0, v___x_383_);
    lean_ctor_set(v___x_384_, 1, v___x_382_);
    lean_ctor_set(v___x_384_, 2, v___x_381_);
    return v___x_384_;
}
pub unsafe fn _init_l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__25()
-> *mut LeanObject {
    let mut v___x_388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_391_: *mut LeanObject = core::ptr::null_mut();
    v___x_388_ = l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__24;
    v___x_389_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__22
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__22_once
        ),
        _init_l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__22,
    );
    v___x_390_ = l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__5;
    v___x_391_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_391_, 0, v___x_390_);
    lean_ctor_set(v___x_391_, 1, v___x_389_);
    lean_ctor_set(v___x_391_, 2, v___x_388_);
    return v___x_391_;
}
pub unsafe fn _init_l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__26()
-> *mut LeanObject {
    let mut v___x_392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_395_: *mut LeanObject = core::ptr::null_mut();
    v___x_392_ = l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__21;
    v___x_393_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__25
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__25_once
        ),
        _init_l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__25,
    );
    v___x_394_ = l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__5;
    v___x_395_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_395_, 0, v___x_394_);
    lean_ctor_set(v___x_395_, 1, v___x_393_);
    lean_ctor_set(v___x_395_, 2, v___x_392_);
    return v___x_395_;
}
pub unsafe fn _init_l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__29()
-> *mut LeanObject {
    let mut v___x_399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_402_: *mut LeanObject = core::ptr::null_mut();
    v___x_399_ = l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__28;
    v___x_400_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__26
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__26_once
        ),
        _init_l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__26,
    );
    v___x_401_ = l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__5;
    v___x_402_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_402_, 0, v___x_401_);
    lean_ctor_set(v___x_402_, 1, v___x_400_);
    lean_ctor_set(v___x_402_, 2, v___x_399_);
    return v___x_402_;
}
pub unsafe fn _init_l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__32()
-> *mut LeanObject {
    let mut v___x_406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_409_: *mut LeanObject = core::ptr::null_mut();
    v___x_406_ = l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__31;
    v___x_407_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__29
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__29_once
        ),
        _init_l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__29,
    );
    v___x_408_ = l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__5;
    v___x_409_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_409_, 0, v___x_408_);
    lean_ctor_set(v___x_409_, 1, v___x_407_);
    lean_ctor_set(v___x_409_, 2, v___x_406_);
    return v___x_409_;
}
pub unsafe fn _init_l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__36()
-> *mut LeanObject {
    let mut v___x_416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_419_: *mut LeanObject = core::ptr::null_mut();
    v___x_416_ = l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__35;
    v___x_417_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__32
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__32_once
        ),
        _init_l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__32,
    );
    v___x_418_ = l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__5;
    v___x_419_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_419_, 0, v___x_418_);
    lean_ctor_set(v___x_419_, 1, v___x_417_);
    lean_ctor_set(v___x_419_, 2, v___x_416_);
    return v___x_419_;
}
pub unsafe fn _init_l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__37()
-> *mut LeanObject {
    let mut v___x_420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_423_: *mut LeanObject = core::ptr::null_mut();
    v___x_420_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__36
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__36_once
        ),
        _init_l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__36,
    );
    v___x_421_ = lean_unsigned_to_nat(1022);
    v___x_422_ = l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__3;
    v___x_423_ = lean_alloc_ctor(3, 3, (0) as u32);
    lean_ctor_set(v___x_423_, 0, v___x_422_);
    lean_ctor_set(v___x_423_, 1, v___x_421_);
    lean_ctor_set(v___x_423_, 2, v___x_420_);
    return v___x_423_;
}
pub unsafe fn _init_l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d__()
-> *mut LeanObject {
    let mut v___x_424_: *mut LeanObject = core::ptr::null_mut();
    v___x_424_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__37
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__37_once
        ),
        _init_l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__37,
    );
    return v___x_424_;
}
pub unsafe fn _init_l_Lean_Parser_command__Builtin__grind__propagator_________x3a_x3d___00__closed__6()
-> *mut LeanObject {
    let mut v___x_441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_444_: *mut LeanObject = core::ptr::null_mut();
    v___x_441_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__17
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__17_once
        ),
        _init_l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__17,
    );
    v___x_442_ = l_Lean_Parser_command__Builtin__grind__propagator_________x3a_x3d___00__closed__5;
    v___x_443_ = l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__5;
    v___x_444_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_444_, 0, v___x_443_);
    lean_ctor_set(v___x_444_, 1, v___x_442_);
    lean_ctor_set(v___x_444_, 2, v___x_441_);
    return v___x_444_;
}
pub unsafe fn _init_l_Lean_Parser_command__Builtin__grind__propagator_________x3a_x3d___00__closed__7()
-> *mut LeanObject {
    let mut v___x_445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_448_: *mut LeanObject = core::ptr::null_mut();
    v___x_445_ = l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__21;
    v___x_446_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command__Builtin__grind__propagator_________x3a_x3d___00__closed__6
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command__Builtin__grind__propagator_________x3a_x3d___00__closed__6_once
        ),
        _init_l_Lean_Parser_command__Builtin__grind__propagator_________x3a_x3d___00__closed__6,
    );
    v___x_447_ = l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__5;
    v___x_448_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_448_, 0, v___x_447_);
    lean_ctor_set(v___x_448_, 1, v___x_446_);
    lean_ctor_set(v___x_448_, 2, v___x_445_);
    return v___x_448_;
}
pub unsafe fn _init_l_Lean_Parser_command__Builtin__grind__propagator_________x3a_x3d___00__closed__8()
-> *mut LeanObject {
    let mut v___x_449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_452_: *mut LeanObject = core::ptr::null_mut();
    v___x_449_ = l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__31;
    v___x_450_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command__Builtin__grind__propagator_________x3a_x3d___00__closed__7
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command__Builtin__grind__propagator_________x3a_x3d___00__closed__7_once
        ),
        _init_l_Lean_Parser_command__Builtin__grind__propagator_________x3a_x3d___00__closed__7,
    );
    v___x_451_ = l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__5;
    v___x_452_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_452_, 0, v___x_451_);
    lean_ctor_set(v___x_452_, 1, v___x_450_);
    lean_ctor_set(v___x_452_, 2, v___x_449_);
    return v___x_452_;
}
pub unsafe fn _init_l_Lean_Parser_command__Builtin__grind__propagator_________x3a_x3d___00__closed__9()
-> *mut LeanObject {
    let mut v___x_453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_456_: *mut LeanObject = core::ptr::null_mut();
    v___x_453_ = l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__35;
    v___x_454_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command__Builtin__grind__propagator_________x3a_x3d___00__closed__8
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command__Builtin__grind__propagator_________x3a_x3d___00__closed__8_once
        ),
        _init_l_Lean_Parser_command__Builtin__grind__propagator_________x3a_x3d___00__closed__8,
    );
    v___x_455_ = l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__5;
    v___x_456_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_456_, 0, v___x_455_);
    lean_ctor_set(v___x_456_, 1, v___x_454_);
    lean_ctor_set(v___x_456_, 2, v___x_453_);
    return v___x_456_;
}
pub unsafe fn _init_l_Lean_Parser_command__Builtin__grind__propagator_________x3a_x3d___00__closed__10()
-> *mut LeanObject {
    let mut v___x_457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_460_: *mut LeanObject = core::ptr::null_mut();
    v___x_457_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command__Builtin__grind__propagator_________x3a_x3d___00__closed__9
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command__Builtin__grind__propagator_________x3a_x3d___00__closed__9_once
        ),
        _init_l_Lean_Parser_command__Builtin__grind__propagator_________x3a_x3d___00__closed__9,
    );
    v___x_458_ = lean_unsigned_to_nat(1022);
    v___x_459_ = l_Lean_Parser_command__Builtin__grind__propagator_________x3a_x3d___00__closed__1;
    v___x_460_ = lean_alloc_ctor(3, 3, (0) as u32);
    lean_ctor_set(v___x_460_, 0, v___x_459_);
    lean_ctor_set(v___x_460_, 1, v___x_458_);
    lean_ctor_set(v___x_460_, 2, v___x_457_);
    return v___x_460_;
}
pub unsafe fn _init_l_Lean_Parser_command__Builtin__grind__propagator_________x3a_x3d__()
-> *mut LeanObject {
    let mut v___x_461_: *mut LeanObject = core::ptr::null_mut();
    v___x_461_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command__Builtin__grind__propagator_________x3a_x3d___00__closed__10
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command__Builtin__grind__propagator_________x3a_x3d___00__closed__10_once
        ),
        _init_l_Lean_Parser_command__Builtin__grind__propagator_________x3a_x3d___00__closed__10,
    );
    return v___x_461_;
}
pub unsafe fn _init_l_Lean_Parser_grindPropagatorBuiltinAttr___closed__4() -> *mut LeanObject {
    let mut v___x_471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_474_: *mut LeanObject = core::ptr::null_mut();
    v___x_471_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__17
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__17_once
        ),
        _init_l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__17,
    );
    v___x_472_ = l_Lean_Parser_grindPropagatorBuiltinAttr___closed__3;
    v___x_473_ = l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__5;
    v___x_474_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_474_, 0, v___x_473_);
    lean_ctor_set(v___x_474_, 1, v___x_472_);
    lean_ctor_set(v___x_474_, 2, v___x_471_);
    return v___x_474_;
}
pub unsafe fn _init_l_Lean_Parser_grindPropagatorBuiltinAttr___closed__5() -> *mut LeanObject {
    let mut v___x_475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_478_: *mut LeanObject = core::ptr::null_mut();
    v___x_475_ = l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__21;
    v___x_476_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_grindPropagatorBuiltinAttr___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_grindPropagatorBuiltinAttr___closed__4_once),
        _init_l_Lean_Parser_grindPropagatorBuiltinAttr___closed__4,
    );
    v___x_477_ = l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__5;
    v___x_478_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_478_, 0, v___x_477_);
    lean_ctor_set(v___x_478_, 1, v___x_476_);
    lean_ctor_set(v___x_478_, 2, v___x_475_);
    return v___x_478_;
}
pub unsafe fn _init_l_Lean_Parser_grindPropagatorBuiltinAttr___closed__6() -> *mut LeanObject {
    let mut v___x_479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_482_: *mut LeanObject = core::ptr::null_mut();
    v___x_479_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_grindPropagatorBuiltinAttr___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_grindPropagatorBuiltinAttr___closed__5_once),
        _init_l_Lean_Parser_grindPropagatorBuiltinAttr___closed__5,
    );
    v___x_480_ = lean_unsigned_to_nat(1022);
    v___x_481_ = l_Lean_Parser_grindPropagatorBuiltinAttr___closed__1;
    v___x_482_ = lean_alloc_ctor(3, 3, (0) as u32);
    lean_ctor_set(v___x_482_, 0, v___x_481_);
    lean_ctor_set(v___x_482_, 1, v___x_480_);
    lean_ctor_set(v___x_482_, 2, v___x_479_);
    return v___x_482_;
}
pub unsafe fn _init_l_Lean_Parser_grindPropagatorBuiltinAttr() -> *mut LeanObject {
    let mut v___x_483_: *mut LeanObject = core::ptr::null_mut();
    v___x_483_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_grindPropagatorBuiltinAttr___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_grindPropagatorBuiltinAttr___closed__6_once),
        _init_l_Lean_Parser_grindPropagatorBuiltinAttr___closed__6,
    );
    return v___x_483_;
}
pub unsafe fn _init_l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__31()
-> *mut LeanObject {
    let mut v___x_544_: *mut LeanObject = core::ptr::null_mut();
    v___x_544_ = l_Array_mkArray0(lean_box(0));
    return v___x_544_;
}
pub unsafe fn l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1(
    mut v_x_552_: *mut LeanObject,
    mut v_a_553_: *mut LeanObject,
    mut v_a_554_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_627_: u8 = 0;
    let mut v___x_628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_632_: u8 = 0;
    let mut v___x_633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_propagatorType_640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_641_: u8 = 0;
    let mut v___x_642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_652_: u8 = 0;
    let mut v___x_653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_657_: u8 = 0;
    let mut v___x_658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_659_: u8 = 0;
    let mut v___x_660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_664_: u8 = 0;
    let mut v___x_665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_668_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_555_ = l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__0;
                v___x_556_ = l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__1;
                v___x_651_ = l_Lean_Parser_command__Builtin__grind__propagator_________x3a_x3d___00__closed__1;
                lean_inc(v_x_552_);
                v___x_652_ = l_Lean_Syntax_isOfKind(v_x_552_, v___x_651_);
                if v___x_652_ == 0 {
                    lean_dec(v_x_552_);
                    v___x_653_ = lean_box(1);
                    v___x_654_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_654_, 0, v___x_653_);
                    lean_ctor_set(v___x_654_, 1, v_a_554_);
                    return v___x_654_;
                } else {
                    v___x_655_ = lean_unsigned_to_nat(0);
                    v___x_656_ = l_Lean_Syntax_getArg(v_x_552_, v___x_655_);
                    v___x_657_ = l_Lean_Syntax_isNone(v___x_656_);
                    if v___x_657_ == 0 {
                        v___x_658_ = lean_unsigned_to_nat(1);
                        lean_inc(v___x_656_);
                        v___x_659_ = l_Lean_Syntax_matchesNull(v___x_656_, v___x_658_);
                        if v___x_659_ == 0 {
                            lean_dec(v___x_656_);
                            lean_dec(v_x_552_);
                            v___x_660_ = lean_box(1);
                            v___x_661_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v___x_661_, 0, v___x_660_);
                            lean_ctor_set(v___x_661_, 1, v_a_554_);
                            return v___x_661_;
                        } else {
                            v_doc_x3f_662_ = l_Lean_Syntax_getArg(v___x_656_, v___x_655_);
                            lean_dec(v___x_656_);
                            v___x_663_ = l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__33;
                            lean_inc(v_doc_x3f_662_);
                            v___x_664_ = l_Lean_Syntax_isOfKind(v_doc_x3f_662_, v___x_663_);
                            if v___x_664_ == 0 {
                                lean_dec(v_doc_x3f_662_);
                                lean_dec(v_x_552_);
                                v___x_665_ = lean_box(1);
                                v___x_666_ = lean_alloc_ctor(1, 2, (0) as u32);
                                lean_ctor_set(v___x_666_, 0, v___x_665_);
                                lean_ctor_set(v___x_666_, 1, v_a_554_);
                                return v___x_666_;
                            } else {
                                v___x_667_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_667_, 0, v_doc_x3f_662_);
                                v_doc_x3f_621_ = v___x_667_;
                                v___y_622_ = v_a_553_;
                                v___y_623_ = v_a_554_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___x_656_);
                        v___x_668_ = lean_box(0);
                        v_doc_x3f_621_ = v___x_668_;
                        v___y_622_ = v_a_553_;
                        v___y_623_ = v_a_554_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc_ref_n(v___y_560_, 2);
                v___x_571_ = l_Array_append___redArg(v___y_560_, v___y_570_);
                lean_dec_ref(v___y_570_);
                lean_inc_n(v___y_566_, 6);
                lean_inc_n(v___y_567_, 24);
                v___x_572_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_572_, 0, v___y_567_);
                lean_ctor_set(v___x_572_, 1, v___y_566_);
                lean_ctor_set(v___x_572_, 2, v___x_571_);
                v___x_573_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_573_, 0, v___y_567_);
                lean_ctor_set(v___x_573_, 1, v___y_566_);
                lean_ctor_set(v___x_573_, 2, v___y_560_);
                lean_inc_ref_n(v___x_573_, 12);
                lean_inc(v___y_559_);
                v___x_574_ = l_Lean_Syntax_node7(
                    v___y_567_, v___y_559_, v___x_572_, v___x_573_, v___x_573_, v___x_573_,
                    v___x_573_, v___x_573_, v___x_573_,
                );
                v___x_575_ = l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__0;
                lean_inc_ref_n(v___y_565_, 5);
                v___x_576_ = l_Lean_Name_mkStr4(v___x_555_, v___x_556_, v___y_565_, v___x_575_);
                v___x_577_ = l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__1;
                v___x_578_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_578_, 0, v___y_567_);
                lean_ctor_set(v___x_578_, 1, v___x_577_);
                v___x_579_ = l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__2;
                v___x_580_ = l_Lean_Name_mkStr4(v___x_555_, v___x_556_, v___y_565_, v___x_579_);
                lean_inc(v___y_562_);
                v___x_581_ = l_Lean_Syntax_node2(v___y_567_, v___x_580_, v___y_562_, v___x_573_);
                v___x_582_ = l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__3;
                v___x_583_ = l_Lean_Name_mkStr4(v___x_555_, v___x_556_, v___y_565_, v___x_582_);
                v___x_584_ = l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__6;
                v___x_585_ = l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__7;
                v___x_586_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_586_, 0, v___y_567_);
                lean_ctor_set(v___x_586_, 1, v___x_585_);
                lean_inc(v___y_569_);
                v___x_587_ = lean_mk_syntax_ident(v___y_569_);
                v___x_588_ = l_Lean_Syntax_node2(v___y_567_, v___x_584_, v___x_586_, v___x_587_);
                v___x_589_ = l_Lean_Syntax_node1(v___y_567_, v___y_566_, v___x_588_);
                v___x_590_ = l_Lean_Syntax_node2(v___y_567_, v___x_583_, v___x_573_, v___x_589_);
                v___x_591_ = l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__8;
                v___x_592_ = l_Lean_Name_mkStr4(v___x_555_, v___x_556_, v___y_565_, v___x_591_);
                v___x_593_ = l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__9;
                v___x_594_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_594_, 0, v___y_567_);
                lean_ctor_set(v___x_594_, 1, v___x_593_);
                v___x_595_ = l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__12;
                v___x_596_ = l_Lean_Syntax_node2(v___y_567_, v___x_595_, v___x_573_, v___x_573_);
                v___x_597_ = l_Lean_Syntax_node4(
                    v___y_567_, v___x_592_, v___x_594_, v___y_564_, v___x_596_, v___x_573_,
                );
                v___x_598_ = l_Lean_Syntax_node5(
                    v___y_567_, v___x_576_, v___x_578_, v___x_581_, v___x_590_, v___x_597_,
                    v___x_573_,
                );
                lean_inc(v___y_558_);
                v___x_599_ = l_Lean_Syntax_node2(v___y_567_, v___y_558_, v___x_574_, v___x_598_);
                v___x_600_ = l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__13;
                v___x_601_ = l_Lean_Name_mkStr4(v___x_555_, v___x_556_, v___y_565_, v___x_600_);
                v___x_602_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_602_, 0, v___y_567_);
                lean_ctor_set(v___x_602_, 1, v___x_600_);
                v___x_603_ = l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__14;
                v___x_604_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_604_, 0, v___y_567_);
                lean_ctor_set(v___x_604_, 1, v___x_603_);
                v___x_605_ = l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__16;
                v___x_606_ = l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__18;
                v___x_607_ = l_Lean_Syntax_node1(v___y_567_, v___x_606_, v___x_573_);
                v___x_608_ = l_Lean_Parser_grindPropagatorBuiltinAttr___closed__1;
                v___x_609_ = l_Lean_Parser_grindPropagatorBuiltinAttr___closed__2;
                v___x_610_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_610_, 0, v___y_567_);
                lean_ctor_set(v___x_610_, 1, v___x_609_);
                v___x_611_ =
                    l_Lean_Syntax_node3(v___y_567_, v___x_608_, v___x_610_, v___y_561_, v___y_563_);
                v___x_612_ = l_Lean_Syntax_node2(v___y_567_, v___x_605_, v___x_607_, v___x_611_);
                v___x_613_ = l_Lean_Syntax_node1(v___y_567_, v___y_566_, v___x_612_);
                v___x_614_ = l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__19;
                v___x_615_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_615_, 0, v___y_567_);
                lean_ctor_set(v___x_615_, 1, v___x_614_);
                v___x_616_ = l_Lean_Syntax_node1(v___y_567_, v___y_566_, v___y_562_);
                v___x_617_ = l_Lean_Syntax_node5(
                    v___y_567_, v___x_601_, v___x_602_, v___x_604_, v___x_613_, v___x_615_,
                    v___x_616_,
                );
                v___x_618_ = l_Lean_Syntax_node2(v___y_567_, v___y_566_, v___x_599_, v___x_617_);
                v___x_619_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_619_, 0, v___x_618_);
                lean_ctor_set(v___x_619_, 1, v___y_568_);
                return v___x_619_;
            }
            2 => {
                v___x_624_ = lean_unsigned_to_nat(2);
                v___x_625_ = l_Lean_Syntax_getArg(v_x_552_, v___x_624_);
                v___x_626_ = l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d___00__closed__20;
                lean_inc(v___x_625_);
                v___x_627_ = l_Lean_Syntax_isOfKind(v___x_625_, v___x_626_);
                if v___x_627_ == 0 {
                    lean_dec(v___x_625_);
                    lean_dec(v_doc_x3f_621_);
                    lean_dec(v_x_552_);
                    v___x_628_ = lean_box(1);
                    v___x_629_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_629_, 0, v___x_628_);
                    lean_ctor_set(v___x_629_, 1, v___y_623_);
                    return v___x_629_;
                } else {
                    v___x_630_ = lean_unsigned_to_nat(4);
                    v___x_631_ = l_Lean_Syntax_getArg(v_x_552_, v___x_630_);
                    lean_inc(v___x_631_);
                    v___x_632_ = l_Lean_Syntax_isOfKind(v___x_631_, v___x_626_);
                    if v___x_632_ == 0 {
                        lean_dec(v___x_631_);
                        lean_dec(v___x_625_);
                        lean_dec(v_doc_x3f_621_);
                        lean_dec(v_x_552_);
                        v___x_633_ = lean_box(1);
                        v___x_634_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_634_, 0, v___x_633_);
                        lean_ctor_set(v___x_634_, 1, v___y_623_);
                        return v___x_634_;
                    } else {
                        v_ref_635_ = lean_ctor_get(v___y_622_, 5);
                        v___x_636_ = lean_unsigned_to_nat(3);
                        v___x_637_ = l_Lean_Syntax_getArg(v_x_552_, v___x_636_);
                        v___x_638_ = lean_unsigned_to_nat(6);
                        v___x_639_ = l_Lean_Syntax_getArg(v_x_552_, v___x_638_);
                        lean_dec(v_x_552_);
                        v_propagatorType_640_ = l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__23;
                        v___x_641_ = 0;
                        v___x_642_ = l_Lean_SourceInfo_fromRef(v_ref_635_, v___x_641_);
                        v___x_643_ = l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__25;
                        v___x_644_ = l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__26;
                        v___x_645_ = l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__28;
                        v___x_646_ = l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__30;
                        v___x_647_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__31), core::ptr::addr_of_mut!(l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__31_once), _init_l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__31);
                        if lean_obj_tag(v_doc_x3f_621_) == 1 {
                            v_val_648_ = lean_ctor_get(v_doc_x3f_621_, 0);
                            lean_inc(v_val_648_);
                            lean_dec_ref_known(v_doc_x3f_621_, 1);
                            v___x_649_ = l_Array_mkArray1___redArg(v_val_648_);
                            v___y_558_ = v___x_645_;
                            v___y_559_ = v___x_646_;
                            v___y_560_ = v___x_647_;
                            v___y_561_ = v___x_637_;
                            v___y_562_ = v___x_625_;
                            v___y_563_ = v___x_631_;
                            v___y_564_ = v___x_639_;
                            v___y_565_ = v___x_644_;
                            v___y_566_ = v___x_643_;
                            v___y_567_ = v___x_642_;
                            v___y_568_ = v___y_623_;
                            v___y_569_ = v_propagatorType_640_;
                            v___y_570_ = v___x_649_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_doc_x3f_621_);
                            v___x_650_ = l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___closed__32;
                            v___y_558_ = v___x_645_;
                            v___y_559_ = v___x_646_;
                            v___y_560_ = v___x_647_;
                            v___y_561_ = v___x_637_;
                            v___y_562_ = v___x_625_;
                            v___y_563_ = v___x_631_;
                            v___y_564_ = v___x_639_;
                            v___y_565_ = v___x_644_;
                            v___y_566_ = v___x_643_;
                            v___y_567_ = v___x_642_;
                            v___y_568_ = v___y_623_;
                            v___y_569_ = v_propagatorType_640_;
                            v___y_570_ = v___x_650_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___boxed(
    mut v_x_669_: *mut LeanObject,
    mut v_a_670_: *mut LeanObject,
    mut v_a_671_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_672_: *mut LeanObject = core::ptr::null_mut();
    v_res_672_ = l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1(v_x_669_, v_a_670_, v_a_671_);
    lean_dec_ref(v_a_670_);
    return v_res_672_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Grind_Propagator(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Tactics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Meta_Defs(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Grind_Propagator(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Init_Meta(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d__ =
        _init_l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d__();
    lean_mark_persistent(l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d__);
    l_Lean_Parser_command__Builtin__grind__propagator_________x3a_x3d__ =
        _init_l_Lean_Parser_command__Builtin__grind__propagator_________x3a_x3d__();
    lean_mark_persistent(l_Lean_Parser_command__Builtin__grind__propagator_________x3a_x3d__);
    l_Lean_Parser_grindPropagatorBuiltinAttr = _init_l_Lean_Parser_grindPropagatorBuiltinAttr();
    lean_mark_persistent(l_Lean_Parser_grindPropagatorBuiltinAttr);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Grind_Propagator(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Meta(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Tactics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Meta_Defs(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Propagator(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Grind_Propagator(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Grind_Propagator(builtin);
}
