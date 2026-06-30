// Lean compiler output
// Module: Init.Simproc
// Imports: Init.Data.ToString.Name Init.Tactics Init.Meta.Defs
use crate::ffi::{
    lean_array_push, lean_array_size, lean_array_uget_borrowed, lean_mk_empty_array_with_capacity,
    lean_name_eq, lean_usize_add, lean_usize_dec_lt,
};
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::ToString::Name::{
    initialize_Init_Data_ToString_Name, l_Lean_Name_toString,
    runtime_initialize_Init_Data_ToString_Name,
};
use crate::r#gen::Init::Meta::Defs::{
    initialize_Init_Meta_Defs, l_Lean_Syntax_TSepArray_getElems___redArg, l_Lean_Syntax_isNone,
    l_Lean_TSyntax_getId, l_Lean_mkOptionalNode, lean_mk_syntax_ident, lean_name_append_after,
    runtime_initialize_Init_Meta_Defs,
};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Array_mkArray1___redArg, l_Lean_Name_append, l_Lean_Name_mkStr4,
    l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_matchesIdent, l_Lean_Syntax_matchesNull, l_Lean_Syntax_node1,
    l_Lean_Syntax_node2, l_Lean_Syntax_node3, l_Lean_Syntax_node4, l_Lean_Syntax_node5,
    l_Lean_Syntax_node7, l_Lean_Syntax_node8, l_Lean_mkAtom,
};
use crate::r#gen::Init::Tactics::{
    initialize_Init_Tactics, l_Lean_Parser_Tactic_simpPost, l_Lean_Parser_Tactic_simpPre,
    runtime_initialize_Init_Tactics,
};
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__2_value: leanh::LeanStringObject<29> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 29, m_capacity: 29, m_length: 28, m_data: [99, 111, 109, 109, 97, 110, 100, 95, 95, 83, 105, 109, 112, 114, 111, 99, 95, 95, 91, 95, 93, 95, 40, 95, 41, 58, 61, 95, 0]};
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__2_value
) as *mut leanh::LeanObject;
static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__3_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__2_value) as *mut leanh::LeanObject,667243668184828663 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__3_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__4_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [97, 110, 100, 116, 104, 101, 110, 0]};
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__4_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__4_value) as *mut leanh::LeanObject,12571085391447129896 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__6_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [111, 112, 116, 105, 111, 110, 97, 108, 0]};
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__6_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__7_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__6_value) as *mut leanh::LeanObject,18170484695678750185 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__7:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__7_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__8_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [100, 111, 99, 67, 111, 109, 109, 101, 110, 116, 0]};
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__8:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__8_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__9_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__8_value) as *mut leanh::LeanObject,3961966953292576997 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__9:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__9_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__10_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__9_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__10:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__10_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__7_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__10_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__12_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [97, 116, 116, 114, 75, 105, 110, 100, 0]};
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__12:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__12_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__13_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__12_value) as *mut leanh::LeanObject,16084902538479694224 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__13:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__13_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__14_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__13_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__14:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__14_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__15_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__14_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__15:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__15_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__16_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [115, 105, 109, 112, 114, 111, 99, 32, 0]};
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__16:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__16_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__17_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__16_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__17:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__17_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__18_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__15_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__17_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__18:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__18_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__19_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [111, 114, 101, 108, 115, 101, 0]};
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__19:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__19_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__20_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__19_value) as *mut leanh::LeanObject,393173242845875278 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__20:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__20_value
) as *mut leanh::LeanObject;
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__21_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__21:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__23_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__23:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__24_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [91, 0]};
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__24:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__24_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__25_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__24_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__25:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__25_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__26_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__26:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__26_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__27_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__26_value) as *mut leanh::LeanObject,5117844058249666356 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__27:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__27_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__28_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__27_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__28:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__28_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__29_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [44, 0]};
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__29:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__29_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__30_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [44, 32, 0]};
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__30:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__30_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__31_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__30_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__31:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__31_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__32_value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 8) as u16, other: 3, tag: 10 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__28_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__29_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__31_value) as *mut leanh::LeanObject,0 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__32:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__32_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__33_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__25_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__32_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__33:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__33_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__34_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__34:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__34_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__35_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__34_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__35:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__35_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__36_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__33_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__35_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__36:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__36_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__37_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__7_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__36_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__37:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__37_value
) as *mut leanh::LeanObject;
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__38_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__38:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__39_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__39:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__40_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [32, 40, 0]};
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__40:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__40_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__41_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__40_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__41:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__41_value
) as *mut leanh::LeanObject;
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__42_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__42:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__43_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 101, 114, 109, 0]};
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__43:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__43_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__44_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__43_value) as *mut leanh::LeanObject,8609355255726335675 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__44:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__44_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__45_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 7 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__44_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__45:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__45_value
) as *mut leanh::LeanObject;
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__46_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__46:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__47_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__47:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__47_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__48_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__47_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__48:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__48_value
) as *mut leanh::LeanObject;
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__49_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__49:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__50_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [32, 58, 61, 32, 0]};
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__50:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__50_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__51_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__50_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__51:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__51_value
) as *mut leanh::LeanObject;
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__52_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__52:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__53_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__53:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__54_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__54:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d__:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value: leanh::LeanStringObject<30> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 30, m_capacity: 30, m_length: 29, m_data: [99, 111, 109, 109, 97, 110, 100, 95, 95, 68, 115, 105, 109, 112, 114, 111, 99, 95, 95, 91, 95, 93, 95, 40, 95, 41, 58, 61, 95, 0]};
static mut l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value
) as *mut leanh::LeanObject;
static l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
pub static l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value) as *mut leanh::LeanObject,7150602757519970396 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__2_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [100, 115, 105, 109, 112, 114, 111, 99, 32, 0]};
static mut l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__2_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__3_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__2_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__3_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__15_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__3_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__4_value
) as *mut leanh::LeanObject;
static mut l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__6_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__6:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__8_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__8:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__9:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__10_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__10:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__12_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__12:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__13_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__13:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d__:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__0_value:
    leanh::LeanStringObject<28> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 28,
    m_capacity: 28,
    m_length: 27,
    m_data: [
        99, 111, 109, 109, 97, 110, 100, 95, 83, 105, 109, 112, 114, 111, 99, 95, 100, 101, 99,
        108, 95, 40, 95, 41, 58, 61, 95, 0,
    ],
};
static mut l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__0_value
) as *mut leanh::LeanObject;
static l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
pub static l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__1_value:
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
        core::ptr::addr_of!(
            l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__1_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__0_value
        ) as *mut leanh::LeanObject,
        18031830130498964246 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__2_value:
    leanh::LeanStringObject<14> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        115, 105, 109, 112, 114, 111, 99, 95, 100, 101, 99, 108, 32, 0,
    ],
};
static mut l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__2_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__3_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__2_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__3_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__3_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__4_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__5_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__4_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__28_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__5_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__6_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__5_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__41_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__6_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__7_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__6_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__45_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__7:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__7_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__8_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__7_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__48_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__8:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__8_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__9_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__8_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__51_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__9:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__9_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__10_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__9_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__45_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__10:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__10_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__11_value:
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
        core::ptr::addr_of!(
            l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__1_value
        ) as *mut leanh::LeanObject,
        (((1022 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__10_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__11:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__11_value
) as *mut leanh::LeanObject;
pub static mut l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d__:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__11_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__0_value:
    leanh::LeanStringObject<29> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        99, 111, 109, 109, 97, 110, 100, 95, 68, 115, 105, 109, 112, 114, 111, 99, 95, 100, 101,
        99, 108, 95, 40, 95, 41, 58, 61, 95, 0,
    ],
};
static mut l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__0_value
) as *mut leanh::LeanObject;
static l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
pub static l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__1_value:
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
        core::ptr::addr_of!(
            l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__1_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__0_value
        ) as *mut leanh::LeanObject,
        5776010155899880851 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__2_value:
    leanh::LeanStringObject<15> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        100, 115, 105, 109, 112, 114, 111, 99, 95, 100, 101, 99, 108, 32, 0,
    ],
};
static mut l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__2_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__3_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__2_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__3_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__3_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__4_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__5_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__4_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__28_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__5_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__6_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__5_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__41_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__6_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__7_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__6_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__45_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__7:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__7_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__8_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__7_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__48_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__8:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__8_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__9_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__8_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__51_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__9:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__9_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__10_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__9_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__45_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__10:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__10_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__11_value:
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
        core::ptr::addr_of!(
            l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__1_value
        ) as *mut leanh::LeanObject,
        (((1022 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__10_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__11:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__11_value
) as *mut leanh::LeanObject;
pub static mut l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d__:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__11_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value: leanh::LeanStringObject<37> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [99, 111, 109, 109, 97, 110, 100, 95, 95, 66, 117, 105, 108, 116, 105, 110, 95, 115, 105, 109, 112, 114, 111, 99, 95, 95, 91, 95, 93, 95, 40, 95, 41, 58, 61, 95, 0]};
static mut l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value) as *mut leanh::LeanObject;
static l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
pub static l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value) as *mut leanh::LeanObject,12128620401598718473 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__2_value: leanh::LeanStringObject<17> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [98, 117, 105, 108, 116, 105, 110, 95, 115, 105, 109, 112, 114, 111, 99, 32, 0]};
static mut l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__2_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__3_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__2_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__3_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__15_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__3_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__4_value) as *mut leanh::LeanObject;
static mut l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__6_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__6: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__8_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__8: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__10_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__10: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__12_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__12: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__13_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__13: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d__:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value: leanh::LeanStringObject<38> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 38, m_capacity: 38, m_length: 37, m_data: [99, 111, 109, 109, 97, 110, 100, 95, 95, 66, 117, 105, 108, 116, 105, 110, 95, 100, 115, 105, 109, 112, 114, 111, 99, 95, 95, 91, 95, 93, 95, 40, 95, 41, 58, 61, 95, 0]};
static mut l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value) as *mut leanh::LeanObject;
static l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
pub static l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value) as *mut leanh::LeanObject,2656510369972815120 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__2_value: leanh::LeanStringObject<18> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [98, 117, 105, 108, 116, 105, 110, 95, 100, 115, 105, 109, 112, 114, 111, 99, 32, 0]};
static mut l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__2_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__3_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__2_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__3_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__15_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__3_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__4_value) as *mut leanh::LeanObject;
static mut l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__6_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__6: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__8_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__8: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__10_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__10: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__12_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__12: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__13_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__13: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d__:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__0_value: leanh::LeanStringObject<36> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 36, m_capacity: 36, m_length: 35, m_data: [99, 111, 109, 109, 97, 110, 100, 95, 66, 117, 105, 108, 116, 105, 110, 95, 115, 105, 109, 112, 114, 111, 99, 95, 100, 101, 99, 108, 95, 40, 95, 41, 58, 61, 95, 0]};
static mut l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__0_value
) as *mut leanh::LeanObject;
static l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
pub static l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__0_value) as *mut leanh::LeanObject,14561357251485234313 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__2_value: leanh::LeanStringObject<22> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [98, 117, 105, 108, 116, 105, 110, 95, 115, 105, 109, 112, 114, 111, 99, 95, 100, 101, 99, 108, 32, 0]};
static mut l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__2_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__3_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__2_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__3_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__3_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__4_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__5_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__4_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__28_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__5_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__6_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__5_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__41_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__6_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__7_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__6_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__45_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__7:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__7_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__8_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__7_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__48_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__8:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__8_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__9_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__8_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__51_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__9:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__9_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__10_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__9_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__45_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__10:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__10_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__11_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__1_value) as *mut leanh::LeanObject,((( 1022 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__10_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__11:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__11_value
) as *mut leanh::LeanObject;
pub static mut l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d__:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__11_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__0_value: leanh::LeanStringObject<37> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [99, 111, 109, 109, 97, 110, 100, 95, 66, 117, 105, 108, 116, 105, 110, 95, 100, 115, 105, 109, 112, 114, 111, 99, 95, 100, 101, 99, 108, 95, 40, 95, 41, 58, 61, 95, 0]};
static mut l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__0_value
) as *mut leanh::LeanObject;
static l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
pub static l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__0_value) as *mut leanh::LeanObject,8930413136233488908 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__2_value: leanh::LeanStringObject<23> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [98, 117, 105, 108, 116, 105, 110, 95, 100, 115, 105, 109, 112, 114, 111, 99, 95, 100, 101, 99, 108, 32, 0]};
static mut l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__2_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__3_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__2_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__3_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__3_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__4_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__5_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__4_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__28_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__5_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__6_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__5_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__41_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__6_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__7_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__6_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__45_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__7:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__7_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__8_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__7_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__48_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__8:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__8_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__9_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__8_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__51_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__9:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__9_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__10_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__9_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__45_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__10:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__10_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__11_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__1_value) as *mut leanh::LeanObject,((( 1022 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__10_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__11:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__11_value
) as *mut leanh::LeanObject;
pub static mut l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d__:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__11_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_simprocPattern___closed__0_value: leanh::LeanStringObject<15> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 15,
        m_capacity: 15,
        m_length: 14,
        m_data: [
            115, 105, 109, 112, 114, 111, 99, 80, 97, 116, 116, 101, 114, 110, 0,
        ],
    };
static mut l_Lean_Parser_simprocPattern___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_simprocPattern___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Parser_simprocPattern___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Parser_simprocPattern___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_simprocPattern___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
pub static l_Lean_Parser_simprocPattern___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_simprocPattern___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_simprocPattern___closed__0_value)
                as *mut leanh::LeanObject,
            18201466311632407230 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_simprocPattern___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_simprocPattern___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_simprocPattern___closed__2_value: leanh::LeanStringObject<18> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 18,
        m_capacity: 18,
        m_length: 17,
        m_data: [
            115, 105, 109, 112, 114, 111, 99, 95, 112, 97, 116, 116, 101, 114, 110, 37, 32, 0,
        ],
    };
static mut l_Lean_Parser_simprocPattern___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_simprocPattern___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_simprocPattern___closed__3_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_simprocPattern___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_simprocPattern___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_simprocPattern___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_simprocPattern___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_simprocPattern___closed__3_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__45_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_simprocPattern___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_simprocPattern___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_simprocPattern___closed__5_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [32, 61, 62, 32, 0],
    };
static mut l_Lean_Parser_simprocPattern___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_simprocPattern___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_simprocPattern___closed__6_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_simprocPattern___closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_simprocPattern___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_simprocPattern___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_simprocPattern___closed__7_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_simprocPattern___closed__4_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_simprocPattern___closed__6_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_simprocPattern___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_simprocPattern___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_simprocPattern___closed__8_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_simprocPattern___closed__7_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__28_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_simprocPattern___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_simprocPattern___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_simprocPattern___closed__9_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_simprocPattern___closed__1_value)
                as *mut leanh::LeanObject,
            (((1022 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_simprocPattern___closed__8_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_simprocPattern___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_simprocPattern___closed__9_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Parser_simprocPattern: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_simprocPattern___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_simprocPatternBuiltin___closed__0_value: leanh::LeanStringObject<
    22,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        115, 105, 109, 112, 114, 111, 99, 80, 97, 116, 116, 101, 114, 110, 66, 117, 105, 108, 116,
        105, 110, 0,
    ],
};
static mut l_Lean_Parser_simprocPatternBuiltin___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_simprocPatternBuiltin___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Parser_simprocPatternBuiltin___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Parser_simprocPatternBuiltin___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_simprocPatternBuiltin___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
pub static l_Lean_Parser_simprocPatternBuiltin___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_simprocPatternBuiltin___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_simprocPatternBuiltin___closed__0_value)
                as *mut leanh::LeanObject,
            10608001774515379730 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_simprocPatternBuiltin___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_simprocPatternBuiltin___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_simprocPatternBuiltin___closed__2_value: leanh::LeanStringObject<
    26,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 26,
    m_capacity: 26,
    m_length: 25,
    m_data: [
        98, 117, 105, 108, 116, 105, 110, 95, 115, 105, 109, 112, 114, 111, 99, 95, 112, 97, 116,
        116, 101, 114, 110, 37, 32, 0,
    ],
};
static mut l_Lean_Parser_simprocPatternBuiltin___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_simprocPatternBuiltin___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_simprocPatternBuiltin___closed__3_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_simprocPatternBuiltin___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_simprocPatternBuiltin___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_simprocPatternBuiltin___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_simprocPatternBuiltin___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_simprocPatternBuiltin___closed__3_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__45_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_simprocPatternBuiltin___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_simprocPatternBuiltin___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_simprocPatternBuiltin___closed__5_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_simprocPatternBuiltin___closed__4_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_simprocPattern___closed__6_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_simprocPatternBuiltin___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_simprocPatternBuiltin___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_simprocPatternBuiltin___closed__6_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_simprocPatternBuiltin___closed__5_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__28_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_simprocPatternBuiltin___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_simprocPatternBuiltin___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_simprocPatternBuiltin___closed__7_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_simprocPatternBuiltin___closed__1_value)
                as *mut leanh::LeanObject,
            (((1022 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_simprocPatternBuiltin___closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_simprocPatternBuiltin___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_simprocPatternBuiltin___closed__7_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Parser_simprocPatternBuiltin: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_simprocPatternBuiltin___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Attr_simprocAttr___closed__0_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [65, 116, 116, 114, 0],
    };
static mut l_Lean_Parser_Attr_simprocAttr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_simprocAttr___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Attr_simprocAttr___closed__1_value: leanh::LeanStringObject<12> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [115, 105, 109, 112, 114, 111, 99, 65, 116, 116, 114, 0],
    };
static mut l_Lean_Parser_Attr_simprocAttr___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_simprocAttr___closed__1_value)
        as *mut leanh::LeanObject;
static l_Lean_Parser_Attr_simprocAttr___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Parser_Attr_simprocAttr___closed__2_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Attr_simprocAttr___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Parser_Attr_simprocAttr___closed__2_value_aux_2: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_simprocAttr___closed__2_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_simprocAttr___closed__0_value)
                as *mut leanh::LeanObject,
            4584992172905639687 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Attr_simprocAttr___closed__2_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_simprocAttr___closed__2_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_simprocAttr___closed__1_value)
                as *mut leanh::LeanObject,
            11850131029335478859 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_simprocAttr___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_simprocAttr___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Attr_simprocAttr___closed__3_value: leanh::LeanStringObject<8> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [115, 105, 109, 112, 114, 111, 99, 0],
    };
static mut l_Lean_Parser_Attr_simprocAttr___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_simprocAttr___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Attr_simprocAttr___closed__4_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_simprocAttr___closed__3_value)
                as *mut leanh::LeanObject,
            0 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_simprocAttr___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_simprocAttr___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Parser_Attr_simprocAttr___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_simprocAttr___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_simprocAttr___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_simprocAttr___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Attr_simprocAttr: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Attr_sevalprocAttr___closed__0_value: leanh::LeanStringObject<14> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 13,
        m_data: [
            115, 101, 118, 97, 108, 112, 114, 111, 99, 65, 116, 116, 114, 0,
        ],
    };
static mut l_Lean_Parser_Attr_sevalprocAttr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_sevalprocAttr___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Parser_Attr_sevalprocAttr___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Parser_Attr_sevalprocAttr___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Attr_sevalprocAttr___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Parser_Attr_sevalprocAttr___closed__1_value_aux_2: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_sevalprocAttr___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_simprocAttr___closed__0_value)
                as *mut leanh::LeanObject,
            4584992172905639687 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Attr_sevalprocAttr___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_sevalprocAttr___closed__1_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_sevalprocAttr___closed__0_value)
                as *mut leanh::LeanObject,
            14768295711661951876 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_sevalprocAttr___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_sevalprocAttr___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Attr_sevalprocAttr___closed__2_value: leanh::LeanStringObject<10> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [115, 101, 118, 97, 108, 112, 114, 111, 99, 0],
    };
static mut l_Lean_Parser_Attr_sevalprocAttr___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_sevalprocAttr___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Attr_sevalprocAttr___closed__3_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_sevalprocAttr___closed__2_value)
                as *mut leanh::LeanObject,
            0 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_sevalprocAttr___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_sevalprocAttr___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Parser_Attr_sevalprocAttr___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_sevalprocAttr___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_sevalprocAttr___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_sevalprocAttr___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Attr_sevalprocAttr: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Attr_simprocBuiltinAttr___closed__0_value: leanh::LeanStringObject<
    19,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 19,
    m_capacity: 19,
    m_length: 18,
    m_data: [
        115, 105, 109, 112, 114, 111, 99, 66, 117, 105, 108, 116, 105, 110, 65, 116, 116, 114, 0,
    ],
};
static mut l_Lean_Parser_Attr_simprocBuiltinAttr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_simprocBuiltinAttr___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Parser_Attr_simprocBuiltinAttr___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Parser_Attr_simprocBuiltinAttr___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Attr_simprocBuiltinAttr___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Parser_Attr_simprocBuiltinAttr___closed__1_value_aux_2: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_simprocBuiltinAttr___closed__1_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_simprocAttr___closed__0_value)
            as *mut leanh::LeanObject,
        4584992172905639687 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Parser_Attr_simprocBuiltinAttr___closed__1_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_simprocBuiltinAttr___closed__1_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_simprocBuiltinAttr___closed__0_value)
            as *mut leanh::LeanObject,
        18242174535284492835 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_simprocBuiltinAttr___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_simprocBuiltinAttr___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Attr_simprocBuiltinAttr___closed__2_value: leanh::LeanStringObject<
    16,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 16,
    m_capacity: 16,
    m_length: 15,
    m_data: [
        98, 117, 105, 108, 116, 105, 110, 95, 115, 105, 109, 112, 114, 111, 99, 0,
    ],
};
static mut l_Lean_Parser_Attr_simprocBuiltinAttr___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_simprocBuiltinAttr___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Attr_simprocBuiltinAttr___closed__3_value: leanh::LeanCtorObject<
    2,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_simprocBuiltinAttr___closed__2_value)
            as *mut leanh::LeanObject,
        0 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_simprocBuiltinAttr___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_simprocBuiltinAttr___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Parser_Attr_simprocBuiltinAttr___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_simprocBuiltinAttr___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_simprocBuiltinAttr___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_simprocBuiltinAttr___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Attr_simprocBuiltinAttr: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__0_value:
    leanh::LeanStringObject<21> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        115, 101, 118, 97, 108, 112, 114, 111, 99, 66, 117, 105, 108, 116, 105, 110, 65, 116, 116,
        114, 0,
    ],
};
static mut l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__1_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__1_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_simprocAttr___closed__0_value)
            as *mut leanh::LeanObject,
        4584992172905639687 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__1_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__1_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__0_value)
            as *mut leanh::LeanObject,
        14943976816696743720 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__2_value:
    leanh::LeanStringObject<18> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 18,
    m_capacity: 18,
    m_length: 17,
    m_data: [
        98, 117, 105, 108, 116, 105, 110, 95, 115, 101, 118, 97, 108, 112, 114, 111, 99, 0,
    ],
};
static mut l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__3_value: leanh::LeanCtorObject<
    2,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__2_value)
            as *mut leanh::LeanObject,
        0 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Attr_sevalprocBuiltinAttr: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [109, 101, 116, 97, 0]};
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__1_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 0]};
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__2_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [100, 101, 102, 0]};
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__3_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [100, 101, 99, 108, 73, 100, 0]};
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__4_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [111, 112, 116, 68, 101, 99, 108, 83, 105, 103, 0]};
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__5_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__5_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__6_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [116, 121, 112, 101, 83, 112, 101, 99, 0]};
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__6_value) as *mut leanh::LeanObject;
static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__7_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__7_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__7_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__7_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__7_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__5_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__7_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__7_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__6_value) as *mut leanh::LeanObject,4498178684837002829 as *mut leanh::LeanObject] };
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__7_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__8_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [58, 0]};
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__8_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__9_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [100, 101, 99, 108, 86, 97, 108, 83, 105, 109, 112, 108, 101, 0]};
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__9_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__10_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [58, 61, 0]};
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__10_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__11_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [84, 101, 114, 109, 105, 110, 97, 116, 105, 111, 110, 0]};
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__11_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__12_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 117, 102, 102, 105, 120, 0]};
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__12_value) as *mut leanh::LeanObject;
static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__13_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__13_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__13_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__13_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__13_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__11_value) as *mut leanh::LeanObject,7625897890118033792 as *mut leanh::LeanObject] };
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__13_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__13_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__12_value) as *mut leanh::LeanObject,8715860392475343861 as *mut leanh::LeanObject] };
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__13_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__14_value: leanh::LeanStringObject<17> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 105, 109, 112, 114, 111, 99, 95, 112, 97, 116, 116, 101, 114, 110, 37, 0]};
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__14_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__15_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [61, 62, 0]};
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__15: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__15_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__16_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__16_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__17_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [83, 105, 109, 112, 0]};
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__17: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__17_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__18_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [83, 105, 109, 112, 114, 111, 99, 0]};
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__18_value) as *mut leanh::LeanObject;
static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__19_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__19_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__19_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__16_value) as *mut leanh::LeanObject,15449383196166861506 as *mut leanh::LeanObject] };
static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__19_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__19_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__17_value) as *mut leanh::LeanObject,492087047182689846 as *mut leanh::LeanObject] };
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__19_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__19_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__18_value) as *mut leanh::LeanObject,18418687298610896914 as *mut leanh::LeanObject] };
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__19: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__19_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__20_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__20: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__20_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__21_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__20_value) as *mut leanh::LeanObject,9855511589286918680 as *mut leanh::LeanObject] };
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__21: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__21_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__22_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [67, 111, 109, 109, 97, 110, 100, 0]};
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__22: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__22_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__23_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 0]};
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__23: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__23_value) as *mut leanh::LeanObject;
static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__24_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__24_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__24_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__24_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__24_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__22_value) as *mut leanh::LeanObject,17342580262104060118 as *mut leanh::LeanObject] };
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__24_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__24_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__23_value) as *mut leanh::LeanObject,8497769072906204829 as *mut leanh::LeanObject] };
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__24: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__24_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__25_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [100, 101, 99, 108, 77, 111, 100, 105, 102, 105, 101, 114, 115, 0]};
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__25: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__25_value) as *mut leanh::LeanObject;
static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__26_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__26_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__26_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__26_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__26_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__22_value) as *mut leanh::LeanObject,17342580262104060118 as *mut leanh::LeanObject] };
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__26_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__26_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__25_value) as *mut leanh::LeanObject,14557702332550915328 as *mut leanh::LeanObject] };
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__26: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__26_value) as *mut leanh::LeanObject;
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__28_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__28: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__28_value) as *mut leanh::LeanObject;
static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__29_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__29_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__29_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__29_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__29_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__22_value) as *mut leanh::LeanObject,17342580262104060118 as *mut leanh::LeanObject] };
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__29_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__29_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__8_value) as *mut leanh::LeanObject,9063780239635860524 as *mut leanh::LeanObject] };
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__29: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__29_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Dsimproc__decl___x28___x29_x3a_x3d____1___closed__0_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [68, 83, 105, 109, 112, 114, 111, 99, 0]};
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Dsimproc__decl___x28___x29_x3a_x3d____1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Dsimproc__decl___x28___x29_x3a_x3d____1___closed__0_value) as *mut leanh::LeanObject;
static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Dsimproc__decl___x28___x29_x3a_x3d____1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Dsimproc__decl___x28___x29_x3a_x3d____1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Dsimproc__decl___x28___x29_x3a_x3d____1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__16_value) as *mut leanh::LeanObject,15449383196166861506 as *mut leanh::LeanObject] };
static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Dsimproc__decl___x28___x29_x3a_x3d____1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Dsimproc__decl___x28___x29_x3a_x3d____1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__17_value) as *mut leanh::LeanObject,492087047182689846 as *mut leanh::LeanObject] };
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Dsimproc__decl___x28___x29_x3a_x3d____1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Dsimproc__decl___x28___x29_x3a_x3d____1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Dsimproc__decl___x28___x29_x3a_x3d____1___closed__0_value) as *mut leanh::LeanObject,11597777601497588599 as *mut leanh::LeanObject] };
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Dsimproc__decl___x28___x29_x3a_x3d____1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Dsimproc__decl___x28___x29_x3a_x3d____1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Builtin__simproc__decl___x28___x29_x3a_x3d____1___closed__0_value: leanh::LeanStringObject<25> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [98, 117, 105, 108, 116, 105, 110, 95, 115, 105, 109, 112, 114, 111, 99, 95, 112, 97, 116, 116, 101, 114, 110, 37, 0]};
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Builtin__simproc__decl___x28___x29_x3a_x3d____1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Builtin__simproc__decl___x28___x29_x3a_x3d____1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__0_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [97, 116, 116, 114, 105, 98, 117, 116, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__0_value) as *mut leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__22_value) as *mut leanh::LeanObject,17342580262104060118 as *mut leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__0_value) as *mut leanh::LeanObject,11509420844586769999 as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__2_value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [97, 116, 116, 114, 73, 110, 115, 116, 97, 110, 99, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__2_value) as *mut leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__3_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__3_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__5_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__3_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__2_value) as *mut leanh::LeanObject,7499624980761693169 as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__4_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 105, 109, 112, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__5_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__4_value) as *mut leanh::LeanObject,13994041031692860867 as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__6_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [115, 101, 118, 97, 108, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__7_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__6_value) as *mut leanh::LeanObject,10924716299523037131 as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__7_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__8_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [95, 112, 114, 111, 99, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__8_value) as *mut leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__9_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value) as *mut leanh::LeanObject,6907480769838958894 as *mut leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__9_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__9_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Attr_simprocAttr___closed__0_value) as *mut leanh::LeanObject,16282038225239345418 as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__9_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__10_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Attr_sevalprocAttr___closed__0_value) as *mut leanh::LeanObject,12361625276289109352 as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__10_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__11_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Attr_simprocAttr___closed__1_value) as *mut leanh::LeanObject,18056956514849972255 as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__11_value) as *mut leanh::LeanObject;
pub static l___private_Init_Simproc_0__Lean_Parser_mkAttributeCmds___closed__0_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l___private_Init_Simproc_0__Lean_Parser_mkAttributeCmds___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Init_Simproc_0__Lean_Parser_mkAttributeCmds___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0_value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [115, 105, 109, 112, 114, 111, 99, 95, 100, 101, 99, 108, 0]};
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__1_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__1_value) as *mut leanh::LeanObject;
static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__2_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__2_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__2_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__5_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__2_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__12_value) as *mut leanh::LeanObject,7983999284776576032 as *mut leanh::LeanObject] };
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [100, 115, 105, 109, 112, 114, 111, 99, 95, 100, 101, 99, 108, 0]};
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0_value: leanh::LeanStringObject<21> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [98, 117, 105, 108, 116, 105, 110, 95, 115, 105, 109, 112, 114, 111, 99, 95, 100, 101, 99, 108, 0]};
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0_value: leanh::LeanStringObject<22> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [98, 117, 105, 108, 116, 105, 110, 95, 100, 115, 105, 109, 112, 114, 111, 99, 95, 100, 101, 99, 108, 0]};
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0_value) as *mut leanh::LeanObject;
pub unsafe fn _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__21()
-> *mut leanh::LeanObject {
    let mut v___x_2232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2232_ = l_Lean_Parser_Tactic_simpPost;
    v___x_2233_ = l_Lean_Parser_Tactic_simpPre;
    v___x_2234_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__20;
    v___x_2235_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2235_, 0, v___x_2234_);
    leanh::lean_ctor_set(v___x_2235_, 1, v___x_2233_);
    leanh::lean_ctor_set(v___x_2235_, 2, v___x_2232_);
    return v___x_2235_;
}
pub unsafe fn _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22()
-> *mut leanh::LeanObject {
    let mut v___x_2236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2236_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__21), core::ptr::addr_of_mut!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__21_once), _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__21);
    v___x_2237_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__7;
    v___x_2238_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2238_, 0, v___x_2237_);
    leanh::lean_ctor_set(v___x_2238_, 1, v___x_2236_);
    return v___x_2238_;
}
pub unsafe fn _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__23()
-> *mut leanh::LeanObject {
    let mut v___x_2239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2239_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22), core::ptr::addr_of_mut!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22_once), _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22);
    v___x_2240_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__18;
    v___x_2241_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
    v___x_2242_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2242_, 0, v___x_2241_);
    leanh::lean_ctor_set(v___x_2242_, 1, v___x_2240_);
    leanh::lean_ctor_set(v___x_2242_, 2, v___x_2239_);
    return v___x_2242_;
}
pub unsafe fn _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__38()
-> *mut leanh::LeanObject {
    let mut v___x_2274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2274_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__37;
    v___x_2275_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__23), core::ptr::addr_of_mut!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__23_once), _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__23);
    v___x_2276_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
    v___x_2277_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2277_, 0, v___x_2276_);
    leanh::lean_ctor_set(v___x_2277_, 1, v___x_2275_);
    leanh::lean_ctor_set(v___x_2277_, 2, v___x_2274_);
    return v___x_2277_;
}
pub unsafe fn _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__39()
-> *mut leanh::LeanObject {
    let mut v___x_2278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2278_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__28;
    v___x_2279_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__38), core::ptr::addr_of_mut!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__38_once), _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__38);
    v___x_2280_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
    v___x_2281_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2281_, 0, v___x_2280_);
    leanh::lean_ctor_set(v___x_2281_, 1, v___x_2279_);
    leanh::lean_ctor_set(v___x_2281_, 2, v___x_2278_);
    return v___x_2281_;
}
pub unsafe fn _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__42()
-> *mut leanh::LeanObject {
    let mut v___x_2285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2285_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__41;
    v___x_2286_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__39), core::ptr::addr_of_mut!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__39_once), _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__39);
    v___x_2287_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
    v___x_2288_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2288_, 0, v___x_2287_);
    leanh::lean_ctor_set(v___x_2288_, 1, v___x_2286_);
    leanh::lean_ctor_set(v___x_2288_, 2, v___x_2285_);
    return v___x_2288_;
}
pub unsafe fn _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__46()
-> *mut leanh::LeanObject {
    let mut v___x_2295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2295_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__45;
    v___x_2296_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__42), core::ptr::addr_of_mut!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__42_once), _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__42);
    v___x_2297_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
    v___x_2298_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2298_, 0, v___x_2297_);
    leanh::lean_ctor_set(v___x_2298_, 1, v___x_2296_);
    leanh::lean_ctor_set(v___x_2298_, 2, v___x_2295_);
    return v___x_2298_;
}
pub unsafe fn _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__49()
-> *mut leanh::LeanObject {
    let mut v___x_2302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2302_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__48;
    v___x_2303_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__46), core::ptr::addr_of_mut!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__46_once), _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__46);
    v___x_2304_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
    v___x_2305_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2305_, 0, v___x_2304_);
    leanh::lean_ctor_set(v___x_2305_, 1, v___x_2303_);
    leanh::lean_ctor_set(v___x_2305_, 2, v___x_2302_);
    return v___x_2305_;
}
pub unsafe fn _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__52()
-> *mut leanh::LeanObject {
    let mut v___x_2309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2309_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__51;
    v___x_2310_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__49), core::ptr::addr_of_mut!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__49_once), _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__49);
    v___x_2311_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
    v___x_2312_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2312_, 0, v___x_2311_);
    leanh::lean_ctor_set(v___x_2312_, 1, v___x_2310_);
    leanh::lean_ctor_set(v___x_2312_, 2, v___x_2309_);
    return v___x_2312_;
}
pub unsafe fn _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__53()
-> *mut leanh::LeanObject {
    let mut v___x_2313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2313_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__45;
    v___x_2314_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__52), core::ptr::addr_of_mut!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__52_once), _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__52);
    v___x_2315_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
    v___x_2316_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2316_, 0, v___x_2315_);
    leanh::lean_ctor_set(v___x_2316_, 1, v___x_2314_);
    leanh::lean_ctor_set(v___x_2316_, 2, v___x_2313_);
    return v___x_2316_;
}
pub unsafe fn _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__54()
-> *mut leanh::LeanObject {
    let mut v___x_2317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2317_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__53), core::ptr::addr_of_mut!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__53_once), _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__53);
    v___x_2318_ = leanh::lean_unsigned_to_nat(1022);
    v___x_2319_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__3;
    v___x_2320_ = leanh::lean_alloc_ctor(3, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2320_, 0, v___x_2319_);
    leanh::lean_ctor_set(v___x_2320_, 1, v___x_2318_);
    leanh::lean_ctor_set(v___x_2320_, 2, v___x_2317_);
    return v___x_2320_;
}
pub unsafe fn _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d__()
-> *mut leanh::LeanObject {
    let mut v___x_2321_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2321_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__54), core::ptr::addr_of_mut!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__54_once), _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__54);
    return v___x_2321_;
}
pub unsafe fn _init_l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_2334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2334_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22), core::ptr::addr_of_mut!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22_once), _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22);
    v___x_2335_ =
        l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__4;
    v___x_2336_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
    v___x_2337_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2337_, 0, v___x_2336_);
    leanh::lean_ctor_set(v___x_2337_, 1, v___x_2335_);
    leanh::lean_ctor_set(v___x_2337_, 2, v___x_2334_);
    return v___x_2337_;
}
pub unsafe fn _init_l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_2338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2338_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__37;
    v___x_2339_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5), core::ptr::addr_of_mut!(l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_once), _init_l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5);
    v___x_2340_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
    v___x_2341_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2341_, 0, v___x_2340_);
    leanh::lean_ctor_set(v___x_2341_, 1, v___x_2339_);
    leanh::lean_ctor_set(v___x_2341_, 2, v___x_2338_);
    return v___x_2341_;
}
pub unsafe fn _init_l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_2342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2342_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__28;
    v___x_2343_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__6), core::ptr::addr_of_mut!(l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__6_once), _init_l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__6);
    v___x_2344_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
    v___x_2345_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2345_, 0, v___x_2344_);
    leanh::lean_ctor_set(v___x_2345_, 1, v___x_2343_);
    leanh::lean_ctor_set(v___x_2345_, 2, v___x_2342_);
    return v___x_2345_;
}
pub unsafe fn _init_l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_2346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2349_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2346_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__41;
    v___x_2347_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__7), core::ptr::addr_of_mut!(l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__7_once), _init_l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__7);
    v___x_2348_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
    v___x_2349_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2349_, 0, v___x_2348_);
    leanh::lean_ctor_set(v___x_2349_, 1, v___x_2347_);
    leanh::lean_ctor_set(v___x_2349_, 2, v___x_2346_);
    return v___x_2349_;
}
pub unsafe fn _init_l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_2350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2350_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__45;
    v___x_2351_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__8), core::ptr::addr_of_mut!(l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__8_once), _init_l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__8);
    v___x_2352_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
    v___x_2353_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2353_, 0, v___x_2352_);
    leanh::lean_ctor_set(v___x_2353_, 1, v___x_2351_);
    leanh::lean_ctor_set(v___x_2353_, 2, v___x_2350_);
    return v___x_2353_;
}
pub unsafe fn _init_l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_2354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2354_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__48;
    v___x_2355_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__9), core::ptr::addr_of_mut!(l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__9_once), _init_l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__9);
    v___x_2356_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
    v___x_2357_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2357_, 0, v___x_2356_);
    leanh::lean_ctor_set(v___x_2357_, 1, v___x_2355_);
    leanh::lean_ctor_set(v___x_2357_, 2, v___x_2354_);
    return v___x_2357_;
}
pub unsafe fn _init_l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_2358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2358_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__51;
    v___x_2359_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__10), core::ptr::addr_of_mut!(l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__10_once), _init_l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__10);
    v___x_2360_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
    v___x_2361_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2361_, 0, v___x_2360_);
    leanh::lean_ctor_set(v___x_2361_, 1, v___x_2359_);
    leanh::lean_ctor_set(v___x_2361_, 2, v___x_2358_);
    return v___x_2361_;
}
pub unsafe fn _init_l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_2362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2362_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__45;
    v___x_2363_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11), core::ptr::addr_of_mut!(l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11_once), _init_l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11);
    v___x_2364_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
    v___x_2365_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2365_, 0, v___x_2364_);
    leanh::lean_ctor_set(v___x_2365_, 1, v___x_2363_);
    leanh::lean_ctor_set(v___x_2365_, 2, v___x_2362_);
    return v___x_2365_;
}
pub unsafe fn _init_l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_2366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2366_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__12), core::ptr::addr_of_mut!(l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__12_once), _init_l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__12);
    v___x_2367_ = leanh::lean_unsigned_to_nat(1022);
    v___x_2368_ =
        l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1;
    v___x_2369_ = leanh::lean_alloc_ctor(3, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2369_, 0, v___x_2368_);
    leanh::lean_ctor_set(v___x_2369_, 1, v___x_2367_);
    leanh::lean_ctor_set(v___x_2369_, 2, v___x_2366_);
    return v___x_2369_;
}
pub unsafe fn _init_l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d__()
-> *mut leanh::LeanObject {
    let mut v___x_2370_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2370_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__13), core::ptr::addr_of_mut!(l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__13_once), _init_l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__13);
    return v___x_2370_;
}
pub unsafe fn _init_l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_2465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2465_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22), core::ptr::addr_of_mut!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22_once), _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22);
    v___x_2466_ =
        l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__4;
    v___x_2467_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
    v___x_2468_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2468_, 0, v___x_2467_);
    leanh::lean_ctor_set(v___x_2468_, 1, v___x_2466_);
    leanh::lean_ctor_set(v___x_2468_, 2, v___x_2465_);
    return v___x_2468_;
}
pub unsafe fn _init_l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_2469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2469_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__37;
    v___x_2470_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5), core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_once), _init_l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5);
    v___x_2471_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
    v___x_2472_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2472_, 0, v___x_2471_);
    leanh::lean_ctor_set(v___x_2472_, 1, v___x_2470_);
    leanh::lean_ctor_set(v___x_2472_, 2, v___x_2469_);
    return v___x_2472_;
}
pub unsafe fn _init_l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_2473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2473_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__28;
    v___x_2474_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__6), core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__6_once), _init_l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__6);
    v___x_2475_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
    v___x_2476_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2476_, 0, v___x_2475_);
    leanh::lean_ctor_set(v___x_2476_, 1, v___x_2474_);
    leanh::lean_ctor_set(v___x_2476_, 2, v___x_2473_);
    return v___x_2476_;
}
pub unsafe fn _init_l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_2477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2477_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__41;
    v___x_2478_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__7), core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__7_once), _init_l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__7);
    v___x_2479_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
    v___x_2480_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2480_, 0, v___x_2479_);
    leanh::lean_ctor_set(v___x_2480_, 1, v___x_2478_);
    leanh::lean_ctor_set(v___x_2480_, 2, v___x_2477_);
    return v___x_2480_;
}
pub unsafe fn _init_l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_2481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2481_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__45;
    v___x_2482_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__8), core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__8_once), _init_l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__8);
    v___x_2483_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
    v___x_2484_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2484_, 0, v___x_2483_);
    leanh::lean_ctor_set(v___x_2484_, 1, v___x_2482_);
    leanh::lean_ctor_set(v___x_2484_, 2, v___x_2481_);
    return v___x_2484_;
}
pub unsafe fn _init_l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_2485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2485_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__48;
    v___x_2486_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__9), core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__9_once), _init_l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__9);
    v___x_2487_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
    v___x_2488_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2488_, 0, v___x_2487_);
    leanh::lean_ctor_set(v___x_2488_, 1, v___x_2486_);
    leanh::lean_ctor_set(v___x_2488_, 2, v___x_2485_);
    return v___x_2488_;
}
pub unsafe fn _init_l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_2489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2489_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__51;
    v___x_2490_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__10), core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__10_once), _init_l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__10);
    v___x_2491_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
    v___x_2492_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2492_, 0, v___x_2491_);
    leanh::lean_ctor_set(v___x_2492_, 1, v___x_2490_);
    leanh::lean_ctor_set(v___x_2492_, 2, v___x_2489_);
    return v___x_2492_;
}
pub unsafe fn _init_l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_2493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2493_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__45;
    v___x_2494_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11), core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11_once), _init_l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11);
    v___x_2495_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
    v___x_2496_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2496_, 0, v___x_2495_);
    leanh::lean_ctor_set(v___x_2496_, 1, v___x_2494_);
    leanh::lean_ctor_set(v___x_2496_, 2, v___x_2493_);
    return v___x_2496_;
}
pub unsafe fn _init_l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_2497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2500_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2497_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__12), core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__12_once), _init_l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__12);
    v___x_2498_ = leanh::lean_unsigned_to_nat(1022);
    v___x_2499_ =
        l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1;
    v___x_2500_ = leanh::lean_alloc_ctor(3, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2500_, 0, v___x_2499_);
    leanh::lean_ctor_set(v___x_2500_, 1, v___x_2498_);
    leanh::lean_ctor_set(v___x_2500_, 2, v___x_2497_);
    return v___x_2500_;
}
pub unsafe fn _init_l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d__()
-> *mut leanh::LeanObject {
    let mut v___x_2501_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2501_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__13), core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__13_once), _init_l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__13);
    return v___x_2501_;
}
pub unsafe fn _init_l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_2514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2514_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22), core::ptr::addr_of_mut!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22_once), _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22);
    v___x_2515_ = l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__4;
    v___x_2516_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
    v___x_2517_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2517_, 0, v___x_2516_);
    leanh::lean_ctor_set(v___x_2517_, 1, v___x_2515_);
    leanh::lean_ctor_set(v___x_2517_, 2, v___x_2514_);
    return v___x_2517_;
}
pub unsafe fn _init_l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_2518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2518_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__37;
    v___x_2519_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5), core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_once), _init_l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5);
    v___x_2520_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
    v___x_2521_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2521_, 0, v___x_2520_);
    leanh::lean_ctor_set(v___x_2521_, 1, v___x_2519_);
    leanh::lean_ctor_set(v___x_2521_, 2, v___x_2518_);
    return v___x_2521_;
}
pub unsafe fn _init_l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_2522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2522_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__28;
    v___x_2523_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__6), core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__6_once), _init_l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__6);
    v___x_2524_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
    v___x_2525_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2525_, 0, v___x_2524_);
    leanh::lean_ctor_set(v___x_2525_, 1, v___x_2523_);
    leanh::lean_ctor_set(v___x_2525_, 2, v___x_2522_);
    return v___x_2525_;
}
pub unsafe fn _init_l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_2526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2526_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__41;
    v___x_2527_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__7), core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__7_once), _init_l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__7);
    v___x_2528_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
    v___x_2529_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2529_, 0, v___x_2528_);
    leanh::lean_ctor_set(v___x_2529_, 1, v___x_2527_);
    leanh::lean_ctor_set(v___x_2529_, 2, v___x_2526_);
    return v___x_2529_;
}
pub unsafe fn _init_l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_2530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2530_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__45;
    v___x_2531_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__8), core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__8_once), _init_l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__8);
    v___x_2532_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
    v___x_2533_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2533_, 0, v___x_2532_);
    leanh::lean_ctor_set(v___x_2533_, 1, v___x_2531_);
    leanh::lean_ctor_set(v___x_2533_, 2, v___x_2530_);
    return v___x_2533_;
}
pub unsafe fn _init_l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_2534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2534_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__48;
    v___x_2535_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__9), core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__9_once), _init_l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__9);
    v___x_2536_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
    v___x_2537_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2537_, 0, v___x_2536_);
    leanh::lean_ctor_set(v___x_2537_, 1, v___x_2535_);
    leanh::lean_ctor_set(v___x_2537_, 2, v___x_2534_);
    return v___x_2537_;
}
pub unsafe fn _init_l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_2538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2538_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__51;
    v___x_2539_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__10), core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__10_once), _init_l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__10);
    v___x_2540_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
    v___x_2541_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2541_, 0, v___x_2540_);
    leanh::lean_ctor_set(v___x_2541_, 1, v___x_2539_);
    leanh::lean_ctor_set(v___x_2541_, 2, v___x_2538_);
    return v___x_2541_;
}
pub unsafe fn _init_l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_2542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2542_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__45;
    v___x_2543_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11), core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11_once), _init_l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11);
    v___x_2544_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
    v___x_2545_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2545_, 0, v___x_2544_);
    leanh::lean_ctor_set(v___x_2545_, 1, v___x_2543_);
    leanh::lean_ctor_set(v___x_2545_, 2, v___x_2542_);
    return v___x_2545_;
}
pub unsafe fn _init_l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_2546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2546_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__12), core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__12_once), _init_l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__12);
    v___x_2547_ = leanh::lean_unsigned_to_nat(1022);
    v___x_2548_ = l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1;
    v___x_2549_ = leanh::lean_alloc_ctor(3, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2549_, 0, v___x_2548_);
    leanh::lean_ctor_set(v___x_2549_, 1, v___x_2547_);
    leanh::lean_ctor_set(v___x_2549_, 2, v___x_2546_);
    return v___x_2549_;
}
pub unsafe fn _init_l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d__()
-> *mut leanh::LeanObject {
    let mut v___x_2550_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2550_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__13), core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__13_once), _init_l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__13);
    return v___x_2550_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_simprocAttr___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_2697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2697_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22), core::ptr::addr_of_mut!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22_once), _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22);
    v___x_2698_ = l_Lean_Parser_Attr_simprocAttr___closed__4;
    v___x_2699_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
    v___x_2700_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2700_, 0, v___x_2699_);
    leanh::lean_ctor_set(v___x_2700_, 1, v___x_2698_);
    leanh::lean_ctor_set(v___x_2700_, 2, v___x_2697_);
    return v___x_2700_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_simprocAttr___closed__6() -> *mut leanh::LeanObject {
    let mut v___x_2701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2701_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_simprocAttr___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_simprocAttr___closed__5_once),
        _init_l_Lean_Parser_Attr_simprocAttr___closed__5,
    );
    v___x_2702_ = leanh::lean_unsigned_to_nat(1022);
    v___x_2703_ = l_Lean_Parser_Attr_simprocAttr___closed__2;
    v___x_2704_ = leanh::lean_alloc_ctor(3, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2704_, 0, v___x_2703_);
    leanh::lean_ctor_set(v___x_2704_, 1, v___x_2702_);
    leanh::lean_ctor_set(v___x_2704_, 2, v___x_2701_);
    return v___x_2704_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_simprocAttr() -> *mut leanh::LeanObject {
    let mut v___x_2705_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2705_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_simprocAttr___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_simprocAttr___closed__6_once),
        _init_l_Lean_Parser_Attr_simprocAttr___closed__6,
    );
    return v___x_2705_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_sevalprocAttr___closed__4() -> *mut leanh::LeanObject
{
    let mut v___x_2716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2716_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22), core::ptr::addr_of_mut!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22_once), _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22);
    v___x_2717_ = l_Lean_Parser_Attr_sevalprocAttr___closed__3;
    v___x_2718_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
    v___x_2719_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2719_, 0, v___x_2718_);
    leanh::lean_ctor_set(v___x_2719_, 1, v___x_2717_);
    leanh::lean_ctor_set(v___x_2719_, 2, v___x_2716_);
    return v___x_2719_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_sevalprocAttr___closed__5() -> *mut leanh::LeanObject
{
    let mut v___x_2720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2723_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2720_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_sevalprocAttr___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_sevalprocAttr___closed__4_once),
        _init_l_Lean_Parser_Attr_sevalprocAttr___closed__4,
    );
    v___x_2721_ = leanh::lean_unsigned_to_nat(1022);
    v___x_2722_ = l_Lean_Parser_Attr_sevalprocAttr___closed__1;
    v___x_2723_ = leanh::lean_alloc_ctor(3, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2723_, 0, v___x_2722_);
    leanh::lean_ctor_set(v___x_2723_, 1, v___x_2721_);
    leanh::lean_ctor_set(v___x_2723_, 2, v___x_2720_);
    return v___x_2723_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_sevalprocAttr() -> *mut leanh::LeanObject {
    let mut v___x_2724_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2724_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_sevalprocAttr___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_sevalprocAttr___closed__5_once),
        _init_l_Lean_Parser_Attr_sevalprocAttr___closed__5,
    );
    return v___x_2724_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_simprocBuiltinAttr___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_2735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2738_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2735_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22), core::ptr::addr_of_mut!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22_once), _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22);
    v___x_2736_ = l_Lean_Parser_Attr_simprocBuiltinAttr___closed__3;
    v___x_2737_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
    v___x_2738_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2738_, 0, v___x_2737_);
    leanh::lean_ctor_set(v___x_2738_, 1, v___x_2736_);
    leanh::lean_ctor_set(v___x_2738_, 2, v___x_2735_);
    return v___x_2738_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_simprocBuiltinAttr___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_2739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2739_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_simprocBuiltinAttr___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_simprocBuiltinAttr___closed__4_once),
        _init_l_Lean_Parser_Attr_simprocBuiltinAttr___closed__4,
    );
    v___x_2740_ = leanh::lean_unsigned_to_nat(1022);
    v___x_2741_ = l_Lean_Parser_Attr_simprocBuiltinAttr___closed__1;
    v___x_2742_ = leanh::lean_alloc_ctor(3, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2742_, 0, v___x_2741_);
    leanh::lean_ctor_set(v___x_2742_, 1, v___x_2740_);
    leanh::lean_ctor_set(v___x_2742_, 2, v___x_2739_);
    return v___x_2742_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_simprocBuiltinAttr() -> *mut leanh::LeanObject {
    let mut v___x_2743_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2743_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_simprocBuiltinAttr___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_simprocBuiltinAttr___closed__5_once),
        _init_l_Lean_Parser_Attr_simprocBuiltinAttr___closed__5,
    );
    return v___x_2743_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_2754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2754_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22), core::ptr::addr_of_mut!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22_once), _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22);
    v___x_2755_ = l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__3;
    v___x_2756_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
    v___x_2757_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2757_, 0, v___x_2756_);
    leanh::lean_ctor_set(v___x_2757_, 1, v___x_2755_);
    leanh::lean_ctor_set(v___x_2757_, 2, v___x_2754_);
    return v___x_2757_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_2758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2758_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__4_once),
        _init_l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__4,
    );
    v___x_2759_ = leanh::lean_unsigned_to_nat(1022);
    v___x_2760_ = l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__1;
    v___x_2761_ = leanh::lean_alloc_ctor(3, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2761_, 0, v___x_2760_);
    leanh::lean_ctor_set(v___x_2761_, 1, v___x_2759_);
    leanh::lean_ctor_set(v___x_2761_, 2, v___x_2758_);
    return v___x_2761_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_sevalprocBuiltinAttr() -> *mut leanh::LeanObject {
    let mut v___x_2762_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2762_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__5_once),
        _init_l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__5,
    );
    return v___x_2762_;
}
pub unsafe fn _init_l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27()
-> *mut leanh::LeanObject {
    let mut v___x_2811_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2811_ = l_Array_mkArray0(leanh::lean_box(0));
    return v___x_2811_;
}
pub unsafe fn l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1(
    mut v_x_2819_: *mut leanh::LeanObject,
    mut v_a_2820_: *mut leanh::LeanObject,
    mut v_a_2821_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_2880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: u8 = 0;
    let mut v___x_2887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_simprocType_2894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: u8 = 0;
    let mut v___x_2896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2906_: u8 = 0;
    let mut v___x_2907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2911_: u8 = 0;
    let mut v___x_2912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2913_: u8 = 0;
    let mut v___x_2914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_2916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: u8 = 0;
    let mut v___x_2919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2822_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0;
                v___x_2823_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1;
                v___x_2905_ =
                    l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__1;
                leanh::lean_inc(v_x_2819_);
                v___x_2906_ = l_Lean_Syntax_isOfKind(v_x_2819_, v___x_2905_);
                if v___x_2906_ == 0 {
                    leanh::lean_dec(v_x_2819_);
                    v___x_2907_ = leanh::lean_box(1);
                    v___x_2908_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2908_, 0, v___x_2907_);
                    leanh::lean_ctor_set(v___x_2908_, 1, v_a_2821_);
                    return v___x_2908_;
                } else {
                    v___x_2909_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2910_ = l_Lean_Syntax_getArg(v_x_2819_, v___x_2909_);
                    v___x_2911_ = l_Lean_Syntax_isNone(v___x_2910_);
                    if v___x_2911_ == 0 {
                        v___x_2912_ = leanh::lean_unsigned_to_nat(1);
                        leanh::lean_inc(v___x_2910_);
                        v___x_2913_ = l_Lean_Syntax_matchesNull(v___x_2910_, v___x_2912_);
                        if v___x_2913_ == 0 {
                            leanh::lean_dec(v___x_2910_);
                            leanh::lean_dec(v_x_2819_);
                            v___x_2914_ = leanh::lean_box(1);
                            v___x_2915_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_2915_, 0, v___x_2914_);
                            leanh::lean_ctor_set(v___x_2915_, 1, v_a_2821_);
                            return v___x_2915_;
                        } else {
                            v_doc_x3f_2916_ = l_Lean_Syntax_getArg(v___x_2910_, v___x_2909_);
                            leanh::lean_dec(v___x_2910_);
                            v___x_2917_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__29;
                            leanh::lean_inc(v_doc_x3f_2916_);
                            v___x_2918_ = l_Lean_Syntax_isOfKind(v_doc_x3f_2916_, v___x_2917_);
                            if v___x_2918_ == 0 {
                                leanh::lean_dec(v_doc_x3f_2916_);
                                leanh::lean_dec(v_x_2819_);
                                v___x_2919_ = leanh::lean_box(1);
                                v___x_2920_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_2920_, 0, v___x_2919_);
                                leanh::lean_ctor_set(v___x_2920_, 1, v_a_2821_);
                                return v___x_2920_;
                            } else {
                                v___x_2921_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_2921_, 0, v_doc_x3f_2916_);
                                v_doc_x3f_2880_ = v___x_2921_;
                                v___y_2881_ = v_a_2820_;
                                v___y_2882_ = v_a_2821_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v___x_2910_);
                        v___x_2922_ = leanh::lean_box(0);
                        v_doc_x3f_2880_ = v___x_2922_;
                        v___y_2881_ = v_a_2820_;
                        v___y_2882_ = v_a_2821_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref_n(v___y_2829_, 2);
                v___x_2837_ = l_Array_append___redArg(v___y_2829_, v___y_2836_);
                leanh::lean_dec_ref(v___y_2836_);
                leanh::lean_inc_n(v___y_2834_, 5);
                leanh::lean_inc_n(v___y_2827_, 20);
                v___x_2838_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2838_, 0, v___y_2827_);
                leanh::lean_ctor_set(v___x_2838_, 1, v___y_2834_);
                leanh::lean_ctor_set(v___x_2838_, 2, v___x_2837_);
                v___x_2839_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2839_, 0, v___y_2827_);
                leanh::lean_ctor_set(v___x_2839_, 1, v___y_2834_);
                leanh::lean_ctor_set(v___x_2839_, 2, v___y_2829_);
                v___x_2840_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__0;
                leanh::lean_inc_ref_n(v___y_2825_, 5);
                v___x_2841_ =
                    l_Lean_Name_mkStr4(v___x_2822_, v___x_2823_, v___y_2825_, v___x_2840_);
                v___x_2842_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2842_, 0, v___y_2827_);
                leanh::lean_ctor_set(v___x_2842_, 1, v___x_2840_);
                v___x_2843_ = l_Lean_Syntax_node1(v___y_2827_, v___x_2841_, v___x_2842_);
                v___x_2844_ = l_Lean_Syntax_node1(v___y_2827_, v___y_2834_, v___x_2843_);
                leanh::lean_inc_ref_n(v___x_2839_, 10);
                leanh::lean_inc(v___y_2833_);
                v___x_2845_ = l_Lean_Syntax_node7(
                    v___y_2827_,
                    v___y_2833_,
                    v___x_2838_,
                    v___x_2839_,
                    v___x_2839_,
                    v___x_2839_,
                    v___x_2844_,
                    v___x_2839_,
                    v___x_2839_,
                );
                v___x_2846_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__1;
                v___x_2847_ =
                    l_Lean_Name_mkStr4(v___x_2822_, v___x_2823_, v___y_2825_, v___x_2846_);
                v___x_2848_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__2;
                v___x_2849_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2849_, 0, v___y_2827_);
                leanh::lean_ctor_set(v___x_2849_, 1, v___x_2848_);
                v___x_2850_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__3;
                v___x_2851_ =
                    l_Lean_Name_mkStr4(v___x_2822_, v___x_2823_, v___y_2825_, v___x_2850_);
                leanh::lean_inc(v___y_2835_);
                v___x_2852_ =
                    l_Lean_Syntax_node2(v___y_2827_, v___x_2851_, v___y_2835_, v___x_2839_);
                v___x_2853_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__4;
                v___x_2854_ =
                    l_Lean_Name_mkStr4(v___x_2822_, v___x_2823_, v___y_2825_, v___x_2853_);
                v___x_2855_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__7;
                v___x_2856_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__8;
                v___x_2857_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2857_, 0, v___y_2827_);
                leanh::lean_ctor_set(v___x_2857_, 1, v___x_2856_);
                leanh::lean_inc(v___y_2832_);
                v___x_2858_ = lean_mk_syntax_ident(v___y_2832_);
                v___x_2859_ =
                    l_Lean_Syntax_node2(v___y_2827_, v___x_2855_, v___x_2857_, v___x_2858_);
                v___x_2860_ = l_Lean_Syntax_node1(v___y_2827_, v___y_2834_, v___x_2859_);
                v___x_2861_ =
                    l_Lean_Syntax_node2(v___y_2827_, v___x_2854_, v___x_2839_, v___x_2860_);
                v___x_2862_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__9;
                v___x_2863_ =
                    l_Lean_Name_mkStr4(v___x_2822_, v___x_2823_, v___y_2825_, v___x_2862_);
                v___x_2864_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__10;
                v___x_2865_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2865_, 0, v___y_2827_);
                leanh::lean_ctor_set(v___x_2865_, 1, v___x_2864_);
                v___x_2866_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__13;
                v___x_2867_ =
                    l_Lean_Syntax_node2(v___y_2827_, v___x_2866_, v___x_2839_, v___x_2839_);
                v___x_2868_ = l_Lean_Syntax_node4(
                    v___y_2827_,
                    v___x_2863_,
                    v___x_2865_,
                    v___y_2826_,
                    v___x_2867_,
                    v___x_2839_,
                );
                v___x_2869_ = l_Lean_Syntax_node5(
                    v___y_2827_,
                    v___x_2847_,
                    v___x_2849_,
                    v___x_2852_,
                    v___x_2861_,
                    v___x_2868_,
                    v___x_2839_,
                );
                leanh::lean_inc(v___y_2831_);
                v___x_2870_ =
                    l_Lean_Syntax_node2(v___y_2827_, v___y_2831_, v___x_2845_, v___x_2869_);
                v___x_2871_ = l_Lean_Parser_simprocPattern___closed__1;
                v___x_2872_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__14;
                v___x_2873_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2873_, 0, v___y_2827_);
                leanh::lean_ctor_set(v___x_2873_, 1, v___x_2872_);
                v___x_2874_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__15;
                v___x_2875_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2875_, 0, v___y_2827_);
                leanh::lean_ctor_set(v___x_2875_, 1, v___x_2874_);
                v___x_2876_ = l_Lean_Syntax_node4(
                    v___y_2827_,
                    v___x_2871_,
                    v___x_2873_,
                    v___y_2830_,
                    v___x_2875_,
                    v___y_2835_,
                );
                v___x_2877_ =
                    l_Lean_Syntax_node2(v___y_2827_, v___y_2834_, v___x_2870_, v___x_2876_);
                v___x_2878_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2878_, 0, v___x_2877_);
                leanh::lean_ctor_set(v___x_2878_, 1, v___y_2828_);
                return v___x_2878_;
            }
            2 => {
                v___x_2883_ = leanh::lean_unsigned_to_nat(2);
                v___x_2884_ = l_Lean_Syntax_getArg(v_x_2819_, v___x_2883_);
                v___x_2885_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__27;
                leanh::lean_inc(v___x_2884_);
                v___x_2886_ = l_Lean_Syntax_isOfKind(v___x_2884_, v___x_2885_);
                if v___x_2886_ == 0 {
                    leanh::lean_dec(v___x_2884_);
                    leanh::lean_dec(v_doc_x3f_2880_);
                    leanh::lean_dec(v_x_2819_);
                    v___x_2887_ = leanh::lean_box(1);
                    v___x_2888_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2888_, 0, v___x_2887_);
                    leanh::lean_ctor_set(v___x_2888_, 1, v___y_2882_);
                    return v___x_2888_;
                } else {
                    v_ref_2889_ = leanh::lean_ctor_get(v___y_2881_, 5);
                    v___x_2890_ = leanh::lean_unsigned_to_nat(4);
                    v___x_2891_ = l_Lean_Syntax_getArg(v_x_2819_, v___x_2890_);
                    v___x_2892_ = leanh::lean_unsigned_to_nat(7);
                    v___x_2893_ = l_Lean_Syntax_getArg(v_x_2819_, v___x_2892_);
                    leanh::lean_dec(v_x_2819_);
                    v_simprocType_2894_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__19;
                    v___x_2895_ = 0;
                    v___x_2896_ = l_Lean_SourceInfo_fromRef(v_ref_2889_, v___x_2895_);
                    v___x_2897_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__21;
                    v___x_2898_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__22;
                    v___x_2899_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__24;
                    v___x_2900_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__26;
                    v___x_2901_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27), core::ptr::addr_of_mut!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27_once), _init_l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27);
                    if leanh::lean_obj_tag(v_doc_x3f_2880_) == 1 {
                        v_val_2902_ = leanh::lean_ctor_get(v_doc_x3f_2880_, 0);
                        leanh::lean_inc(v_val_2902_);
                        leanh::lean_dec_ref_known(v_doc_x3f_2880_, 1);
                        v___x_2903_ = l_Array_mkArray1___redArg(v_val_2902_);
                        v___y_2825_ = v___x_2898_;
                        v___y_2826_ = v___x_2893_;
                        v___y_2827_ = v___x_2896_;
                        v___y_2828_ = v___y_2882_;
                        v___y_2829_ = v___x_2901_;
                        v___y_2830_ = v___x_2891_;
                        v___y_2831_ = v___x_2899_;
                        v___y_2832_ = v_simprocType_2894_;
                        v___y_2833_ = v___x_2900_;
                        v___y_2834_ = v___x_2897_;
                        v___y_2835_ = v___x_2884_;
                        v___y_2836_ = v___x_2903_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_doc_x3f_2880_);
                        v___x_2904_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__28;
                        v___y_2825_ = v___x_2898_;
                        v___y_2826_ = v___x_2893_;
                        v___y_2827_ = v___x_2896_;
                        v___y_2828_ = v___y_2882_;
                        v___y_2829_ = v___x_2901_;
                        v___y_2830_ = v___x_2891_;
                        v___y_2831_ = v___x_2899_;
                        v___y_2832_ = v_simprocType_2894_;
                        v___y_2833_ = v___x_2900_;
                        v___y_2834_ = v___x_2897_;
                        v___y_2835_ = v___x_2884_;
                        v___y_2836_ = v___x_2904_;
                        state = 1;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___boxed(
    mut v_x_2923_: *mut leanh::LeanObject,
    mut v_a_2924_: *mut leanh::LeanObject,
    mut v_a_2925_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2926_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2926_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1(v_x_2923_, v_a_2924_, v_a_2925_);
    leanh::lean_dec_ref(v_a_2924_);
    return v_res_2926_;
}
pub unsafe fn l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Dsimproc__decl___x28___x29_x3a_x3d____1(
    mut v_x_2933_: *mut leanh::LeanObject,
    mut v_a_2934_: *mut leanh::LeanObject,
    mut v_a_2935_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_2994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: u8 = 0;
    let mut v___x_3001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_simprocType_3008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: u8 = 0;
    let mut v___x_3010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3020_: u8 = 0;
    let mut v___x_3021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: u8 = 0;
    let mut v___x_3026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: u8 = 0;
    let mut v___x_3028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_3030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: u8 = 0;
    let mut v___x_3033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2936_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0;
                v___x_2937_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1;
                v___x_3019_ =
                    l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__1;
                leanh::lean_inc(v_x_2933_);
                v___x_3020_ = l_Lean_Syntax_isOfKind(v_x_2933_, v___x_3019_);
                if v___x_3020_ == 0 {
                    leanh::lean_dec(v_x_2933_);
                    v___x_3021_ = leanh::lean_box(1);
                    v___x_3022_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3022_, 0, v___x_3021_);
                    leanh::lean_ctor_set(v___x_3022_, 1, v_a_2935_);
                    return v___x_3022_;
                } else {
                    v___x_3023_ = leanh::lean_unsigned_to_nat(0);
                    v___x_3024_ = l_Lean_Syntax_getArg(v_x_2933_, v___x_3023_);
                    v___x_3025_ = l_Lean_Syntax_isNone(v___x_3024_);
                    if v___x_3025_ == 0 {
                        v___x_3026_ = leanh::lean_unsigned_to_nat(1);
                        leanh::lean_inc(v___x_3024_);
                        v___x_3027_ = l_Lean_Syntax_matchesNull(v___x_3024_, v___x_3026_);
                        if v___x_3027_ == 0 {
                            leanh::lean_dec(v___x_3024_);
                            leanh::lean_dec(v_x_2933_);
                            v___x_3028_ = leanh::lean_box(1);
                            v___x_3029_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_3029_, 0, v___x_3028_);
                            leanh::lean_ctor_set(v___x_3029_, 1, v_a_2935_);
                            return v___x_3029_;
                        } else {
                            v_doc_x3f_3030_ = l_Lean_Syntax_getArg(v___x_3024_, v___x_3023_);
                            leanh::lean_dec(v___x_3024_);
                            v___x_3031_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__29;
                            leanh::lean_inc(v_doc_x3f_3030_);
                            v___x_3032_ = l_Lean_Syntax_isOfKind(v_doc_x3f_3030_, v___x_3031_);
                            if v___x_3032_ == 0 {
                                leanh::lean_dec(v_doc_x3f_3030_);
                                leanh::lean_dec(v_x_2933_);
                                v___x_3033_ = leanh::lean_box(1);
                                v___x_3034_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3034_, 0, v___x_3033_);
                                leanh::lean_ctor_set(v___x_3034_, 1, v_a_2935_);
                                return v___x_3034_;
                            } else {
                                v___x_3035_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_3035_, 0, v_doc_x3f_3030_);
                                v_doc_x3f_2994_ = v___x_3035_;
                                v___y_2995_ = v_a_2934_;
                                v___y_2996_ = v_a_2935_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v___x_3024_);
                        v___x_3036_ = leanh::lean_box(0);
                        v_doc_x3f_2994_ = v___x_3036_;
                        v___y_2995_ = v_a_2934_;
                        v___y_2996_ = v_a_2935_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref_n(v___y_2947_, 2);
                v___x_2951_ = l_Array_append___redArg(v___y_2947_, v___y_2950_);
                leanh::lean_dec_ref(v___y_2950_);
                leanh::lean_inc_n(v___y_2940_, 5);
                leanh::lean_inc_n(v___y_2942_, 20);
                v___x_2952_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2952_, 0, v___y_2942_);
                leanh::lean_ctor_set(v___x_2952_, 1, v___y_2940_);
                leanh::lean_ctor_set(v___x_2952_, 2, v___x_2951_);
                v___x_2953_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2953_, 0, v___y_2942_);
                leanh::lean_ctor_set(v___x_2953_, 1, v___y_2940_);
                leanh::lean_ctor_set(v___x_2953_, 2, v___y_2947_);
                v___x_2954_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__0;
                leanh::lean_inc_ref_n(v___y_2946_, 5);
                v___x_2955_ =
                    l_Lean_Name_mkStr4(v___x_2936_, v___x_2937_, v___y_2946_, v___x_2954_);
                v___x_2956_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2956_, 0, v___y_2942_);
                leanh::lean_ctor_set(v___x_2956_, 1, v___x_2954_);
                v___x_2957_ = l_Lean_Syntax_node1(v___y_2942_, v___x_2955_, v___x_2956_);
                v___x_2958_ = l_Lean_Syntax_node1(v___y_2942_, v___y_2940_, v___x_2957_);
                leanh::lean_inc_ref_n(v___x_2953_, 10);
                leanh::lean_inc(v___y_2944_);
                v___x_2959_ = l_Lean_Syntax_node7(
                    v___y_2942_,
                    v___y_2944_,
                    v___x_2952_,
                    v___x_2953_,
                    v___x_2953_,
                    v___x_2953_,
                    v___x_2958_,
                    v___x_2953_,
                    v___x_2953_,
                );
                v___x_2960_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__1;
                v___x_2961_ =
                    l_Lean_Name_mkStr4(v___x_2936_, v___x_2937_, v___y_2946_, v___x_2960_);
                v___x_2962_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__2;
                v___x_2963_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2963_, 0, v___y_2942_);
                leanh::lean_ctor_set(v___x_2963_, 1, v___x_2962_);
                v___x_2964_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__3;
                v___x_2965_ =
                    l_Lean_Name_mkStr4(v___x_2936_, v___x_2937_, v___y_2946_, v___x_2964_);
                leanh::lean_inc(v___y_2941_);
                v___x_2966_ =
                    l_Lean_Syntax_node2(v___y_2942_, v___x_2965_, v___y_2941_, v___x_2953_);
                v___x_2967_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__4;
                v___x_2968_ =
                    l_Lean_Name_mkStr4(v___x_2936_, v___x_2937_, v___y_2946_, v___x_2967_);
                v___x_2969_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__7;
                v___x_2970_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__8;
                v___x_2971_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2971_, 0, v___y_2942_);
                leanh::lean_ctor_set(v___x_2971_, 1, v___x_2970_);
                leanh::lean_inc(v___y_2949_);
                v___x_2972_ = lean_mk_syntax_ident(v___y_2949_);
                v___x_2973_ =
                    l_Lean_Syntax_node2(v___y_2942_, v___x_2969_, v___x_2971_, v___x_2972_);
                v___x_2974_ = l_Lean_Syntax_node1(v___y_2942_, v___y_2940_, v___x_2973_);
                v___x_2975_ =
                    l_Lean_Syntax_node2(v___y_2942_, v___x_2968_, v___x_2953_, v___x_2974_);
                v___x_2976_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__9;
                v___x_2977_ =
                    l_Lean_Name_mkStr4(v___x_2936_, v___x_2937_, v___y_2946_, v___x_2976_);
                v___x_2978_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__10;
                v___x_2979_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2979_, 0, v___y_2942_);
                leanh::lean_ctor_set(v___x_2979_, 1, v___x_2978_);
                v___x_2980_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__13;
                v___x_2981_ =
                    l_Lean_Syntax_node2(v___y_2942_, v___x_2980_, v___x_2953_, v___x_2953_);
                v___x_2982_ = l_Lean_Syntax_node4(
                    v___y_2942_,
                    v___x_2977_,
                    v___x_2979_,
                    v___y_2948_,
                    v___x_2981_,
                    v___x_2953_,
                );
                v___x_2983_ = l_Lean_Syntax_node5(
                    v___y_2942_,
                    v___x_2961_,
                    v___x_2963_,
                    v___x_2966_,
                    v___x_2975_,
                    v___x_2982_,
                    v___x_2953_,
                );
                leanh::lean_inc(v___y_2945_);
                v___x_2984_ =
                    l_Lean_Syntax_node2(v___y_2942_, v___y_2945_, v___x_2959_, v___x_2983_);
                v___x_2985_ = l_Lean_Parser_simprocPattern___closed__1;
                v___x_2986_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__14;
                v___x_2987_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2987_, 0, v___y_2942_);
                leanh::lean_ctor_set(v___x_2987_, 1, v___x_2986_);
                v___x_2988_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__15;
                v___x_2989_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2989_, 0, v___y_2942_);
                leanh::lean_ctor_set(v___x_2989_, 1, v___x_2988_);
                v___x_2990_ = l_Lean_Syntax_node4(
                    v___y_2942_,
                    v___x_2985_,
                    v___x_2987_,
                    v___y_2943_,
                    v___x_2989_,
                    v___y_2941_,
                );
                v___x_2991_ =
                    l_Lean_Syntax_node2(v___y_2942_, v___y_2940_, v___x_2984_, v___x_2990_);
                v___x_2992_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2992_, 0, v___x_2991_);
                leanh::lean_ctor_set(v___x_2992_, 1, v___y_2939_);
                return v___x_2992_;
            }
            2 => {
                v___x_2997_ = leanh::lean_unsigned_to_nat(2);
                v___x_2998_ = l_Lean_Syntax_getArg(v_x_2933_, v___x_2997_);
                v___x_2999_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__27;
                leanh::lean_inc(v___x_2998_);
                v___x_3000_ = l_Lean_Syntax_isOfKind(v___x_2998_, v___x_2999_);
                if v___x_3000_ == 0 {
                    leanh::lean_dec(v___x_2998_);
                    leanh::lean_dec(v_doc_x3f_2994_);
                    leanh::lean_dec(v_x_2933_);
                    v___x_3001_ = leanh::lean_box(1);
                    v___x_3002_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3002_, 0, v___x_3001_);
                    leanh::lean_ctor_set(v___x_3002_, 1, v___y_2996_);
                    return v___x_3002_;
                } else {
                    v_ref_3003_ = leanh::lean_ctor_get(v___y_2995_, 5);
                    v___x_3004_ = leanh::lean_unsigned_to_nat(4);
                    v___x_3005_ = l_Lean_Syntax_getArg(v_x_2933_, v___x_3004_);
                    v___x_3006_ = leanh::lean_unsigned_to_nat(7);
                    v___x_3007_ = l_Lean_Syntax_getArg(v_x_2933_, v___x_3006_);
                    leanh::lean_dec(v_x_2933_);
                    v_simprocType_3008_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Dsimproc__decl___x28___x29_x3a_x3d____1___closed__1;
                    v___x_3009_ = 0;
                    v___x_3010_ = l_Lean_SourceInfo_fromRef(v_ref_3003_, v___x_3009_);
                    v___x_3011_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__21;
                    v___x_3012_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__22;
                    v___x_3013_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__24;
                    v___x_3014_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__26;
                    v___x_3015_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27), core::ptr::addr_of_mut!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27_once), _init_l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27);
                    if leanh::lean_obj_tag(v_doc_x3f_2994_) == 1 {
                        v_val_3016_ = leanh::lean_ctor_get(v_doc_x3f_2994_, 0);
                        leanh::lean_inc(v_val_3016_);
                        leanh::lean_dec_ref_known(v_doc_x3f_2994_, 1);
                        v___x_3017_ = l_Array_mkArray1___redArg(v_val_3016_);
                        v___y_2939_ = v___y_2996_;
                        v___y_2940_ = v___x_3011_;
                        v___y_2941_ = v___x_2998_;
                        v___y_2942_ = v___x_3010_;
                        v___y_2943_ = v___x_3005_;
                        v___y_2944_ = v___x_3014_;
                        v___y_2945_ = v___x_3013_;
                        v___y_2946_ = v___x_3012_;
                        v___y_2947_ = v___x_3015_;
                        v___y_2948_ = v___x_3007_;
                        v___y_2949_ = v_simprocType_3008_;
                        v___y_2950_ = v___x_3017_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_doc_x3f_2994_);
                        v___x_3018_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__28;
                        v___y_2939_ = v___y_2996_;
                        v___y_2940_ = v___x_3011_;
                        v___y_2941_ = v___x_2998_;
                        v___y_2942_ = v___x_3010_;
                        v___y_2943_ = v___x_3005_;
                        v___y_2944_ = v___x_3014_;
                        v___y_2945_ = v___x_3013_;
                        v___y_2946_ = v___x_3012_;
                        v___y_2947_ = v___x_3015_;
                        v___y_2948_ = v___x_3007_;
                        v___y_2949_ = v_simprocType_3008_;
                        v___y_2950_ = v___x_3018_;
                        state = 1;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Dsimproc__decl___x28___x29_x3a_x3d____1___boxed(
    mut v_x_3037_: *mut leanh::LeanObject,
    mut v_a_3038_: *mut leanh::LeanObject,
    mut v_a_3039_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3040_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3040_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Dsimproc__decl___x28___x29_x3a_x3d____1(v_x_3037_, v_a_3038_, v_a_3039_);
    leanh::lean_dec_ref(v_a_3038_);
    return v_res_3040_;
}
pub unsafe fn l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Builtin__simproc__decl___x28___x29_x3a_x3d____1(
    mut v_x_3042_: *mut leanh::LeanObject,
    mut v_a_3043_: *mut leanh::LeanObject,
    mut v_a_3044_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_3098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: u8 = 0;
    let mut v___x_3105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_simprocType_3112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3113_: u8 = 0;
    let mut v___x_3114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: u8 = 0;
    let mut v___x_3125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3129_: u8 = 0;
    let mut v___x_3130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: u8 = 0;
    let mut v___x_3132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_3134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3136_: u8 = 0;
    let mut v___x_3137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3045_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0;
                v___x_3046_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1;
                v___x_3123_ = l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__1;
                leanh::lean_inc(v_x_3042_);
                v___x_3124_ = l_Lean_Syntax_isOfKind(v_x_3042_, v___x_3123_);
                if v___x_3124_ == 0 {
                    leanh::lean_dec(v_x_3042_);
                    v___x_3125_ = leanh::lean_box(1);
                    v___x_3126_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3126_, 0, v___x_3125_);
                    leanh::lean_ctor_set(v___x_3126_, 1, v_a_3044_);
                    return v___x_3126_;
                } else {
                    v___x_3127_ = leanh::lean_unsigned_to_nat(0);
                    v___x_3128_ = l_Lean_Syntax_getArg(v_x_3042_, v___x_3127_);
                    v___x_3129_ = l_Lean_Syntax_isNone(v___x_3128_);
                    if v___x_3129_ == 0 {
                        v___x_3130_ = leanh::lean_unsigned_to_nat(1);
                        leanh::lean_inc(v___x_3128_);
                        v___x_3131_ = l_Lean_Syntax_matchesNull(v___x_3128_, v___x_3130_);
                        if v___x_3131_ == 0 {
                            leanh::lean_dec(v___x_3128_);
                            leanh::lean_dec(v_x_3042_);
                            v___x_3132_ = leanh::lean_box(1);
                            v___x_3133_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_3133_, 0, v___x_3132_);
                            leanh::lean_ctor_set(v___x_3133_, 1, v_a_3044_);
                            return v___x_3133_;
                        } else {
                            v_doc_x3f_3134_ = l_Lean_Syntax_getArg(v___x_3128_, v___x_3127_);
                            leanh::lean_dec(v___x_3128_);
                            v___x_3135_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__29;
                            leanh::lean_inc(v_doc_x3f_3134_);
                            v___x_3136_ = l_Lean_Syntax_isOfKind(v_doc_x3f_3134_, v___x_3135_);
                            if v___x_3136_ == 0 {
                                leanh::lean_dec(v_doc_x3f_3134_);
                                leanh::lean_dec(v_x_3042_);
                                v___x_3137_ = leanh::lean_box(1);
                                v___x_3138_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3138_, 0, v___x_3137_);
                                leanh::lean_ctor_set(v___x_3138_, 1, v_a_3044_);
                                return v___x_3138_;
                            } else {
                                v___x_3139_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_3139_, 0, v_doc_x3f_3134_);
                                v_doc_x3f_3098_ = v___x_3139_;
                                v___y_3099_ = v_a_3043_;
                                v___y_3100_ = v_a_3044_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v___x_3128_);
                        v___x_3140_ = leanh::lean_box(0);
                        v_doc_x3f_3098_ = v___x_3140_;
                        v___y_3099_ = v_a_3043_;
                        v___y_3100_ = v_a_3044_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref_n(v___y_3051_, 2);
                v___x_3060_ = l_Array_append___redArg(v___y_3051_, v___y_3059_);
                leanh::lean_dec_ref(v___y_3059_);
                leanh::lean_inc_n(v___y_3056_, 4);
                leanh::lean_inc_n(v___y_3048_, 17);
                v___x_3061_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3061_, 0, v___y_3048_);
                leanh::lean_ctor_set(v___x_3061_, 1, v___y_3056_);
                leanh::lean_ctor_set(v___x_3061_, 2, v___x_3060_);
                v___x_3062_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3062_, 0, v___y_3048_);
                leanh::lean_ctor_set(v___x_3062_, 1, v___y_3056_);
                leanh::lean_ctor_set(v___x_3062_, 2, v___y_3051_);
                leanh::lean_inc_ref_n(v___x_3062_, 11);
                leanh::lean_inc(v___y_3050_);
                v___x_3063_ = l_Lean_Syntax_node7(
                    v___y_3048_,
                    v___y_3050_,
                    v___x_3061_,
                    v___x_3062_,
                    v___x_3062_,
                    v___x_3062_,
                    v___x_3062_,
                    v___x_3062_,
                    v___x_3062_,
                );
                v___x_3064_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__1;
                leanh::lean_inc_ref_n(v___y_3049_, 4);
                v___x_3065_ =
                    l_Lean_Name_mkStr4(v___x_3045_, v___x_3046_, v___y_3049_, v___x_3064_);
                v___x_3066_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__2;
                v___x_3067_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3067_, 0, v___y_3048_);
                leanh::lean_ctor_set(v___x_3067_, 1, v___x_3066_);
                v___x_3068_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__3;
                v___x_3069_ =
                    l_Lean_Name_mkStr4(v___x_3045_, v___x_3046_, v___y_3049_, v___x_3068_);
                leanh::lean_inc(v___y_3055_);
                v___x_3070_ =
                    l_Lean_Syntax_node2(v___y_3048_, v___x_3069_, v___y_3055_, v___x_3062_);
                v___x_3071_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__4;
                v___x_3072_ =
                    l_Lean_Name_mkStr4(v___x_3045_, v___x_3046_, v___y_3049_, v___x_3071_);
                v___x_3073_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__7;
                v___x_3074_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__8;
                v___x_3075_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3075_, 0, v___y_3048_);
                leanh::lean_ctor_set(v___x_3075_, 1, v___x_3074_);
                leanh::lean_inc(v___y_3054_);
                v___x_3076_ = lean_mk_syntax_ident(v___y_3054_);
                v___x_3077_ =
                    l_Lean_Syntax_node2(v___y_3048_, v___x_3073_, v___x_3075_, v___x_3076_);
                v___x_3078_ = l_Lean_Syntax_node1(v___y_3048_, v___y_3056_, v___x_3077_);
                v___x_3079_ =
                    l_Lean_Syntax_node2(v___y_3048_, v___x_3072_, v___x_3062_, v___x_3078_);
                v___x_3080_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__9;
                v___x_3081_ =
                    l_Lean_Name_mkStr4(v___x_3045_, v___x_3046_, v___y_3049_, v___x_3080_);
                v___x_3082_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__10;
                v___x_3083_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3083_, 0, v___y_3048_);
                leanh::lean_ctor_set(v___x_3083_, 1, v___x_3082_);
                v___x_3084_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__13;
                v___x_3085_ =
                    l_Lean_Syntax_node2(v___y_3048_, v___x_3084_, v___x_3062_, v___x_3062_);
                v___x_3086_ = l_Lean_Syntax_node4(
                    v___y_3048_,
                    v___x_3081_,
                    v___x_3083_,
                    v___y_3058_,
                    v___x_3085_,
                    v___x_3062_,
                );
                v___x_3087_ = l_Lean_Syntax_node5(
                    v___y_3048_,
                    v___x_3065_,
                    v___x_3067_,
                    v___x_3070_,
                    v___x_3079_,
                    v___x_3086_,
                    v___x_3062_,
                );
                leanh::lean_inc(v___y_3057_);
                v___x_3088_ =
                    l_Lean_Syntax_node2(v___y_3048_, v___y_3057_, v___x_3063_, v___x_3087_);
                v___x_3089_ = l_Lean_Parser_simprocPatternBuiltin___closed__1;
                v___x_3090_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Builtin__simproc__decl___x28___x29_x3a_x3d____1___closed__0;
                v___x_3091_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3091_, 0, v___y_3048_);
                leanh::lean_ctor_set(v___x_3091_, 1, v___x_3090_);
                v___x_3092_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__15;
                v___x_3093_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3093_, 0, v___y_3048_);
                leanh::lean_ctor_set(v___x_3093_, 1, v___x_3092_);
                v___x_3094_ = l_Lean_Syntax_node4(
                    v___y_3048_,
                    v___x_3089_,
                    v___x_3091_,
                    v___y_3052_,
                    v___x_3093_,
                    v___y_3055_,
                );
                v___x_3095_ =
                    l_Lean_Syntax_node2(v___y_3048_, v___y_3056_, v___x_3088_, v___x_3094_);
                v___x_3096_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3096_, 0, v___x_3095_);
                leanh::lean_ctor_set(v___x_3096_, 1, v___y_3053_);
                return v___x_3096_;
            }
            2 => {
                v___x_3101_ = leanh::lean_unsigned_to_nat(2);
                v___x_3102_ = l_Lean_Syntax_getArg(v_x_3042_, v___x_3101_);
                v___x_3103_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__27;
                leanh::lean_inc(v___x_3102_);
                v___x_3104_ = l_Lean_Syntax_isOfKind(v___x_3102_, v___x_3103_);
                if v___x_3104_ == 0 {
                    leanh::lean_dec(v___x_3102_);
                    leanh::lean_dec(v_doc_x3f_3098_);
                    leanh::lean_dec(v_x_3042_);
                    v___x_3105_ = leanh::lean_box(1);
                    v___x_3106_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3106_, 0, v___x_3105_);
                    leanh::lean_ctor_set(v___x_3106_, 1, v___y_3100_);
                    return v___x_3106_;
                } else {
                    v_ref_3107_ = leanh::lean_ctor_get(v___y_3099_, 5);
                    v___x_3108_ = leanh::lean_unsigned_to_nat(4);
                    v___x_3109_ = l_Lean_Syntax_getArg(v_x_3042_, v___x_3108_);
                    v___x_3110_ = leanh::lean_unsigned_to_nat(7);
                    v___x_3111_ = l_Lean_Syntax_getArg(v_x_3042_, v___x_3110_);
                    leanh::lean_dec(v_x_3042_);
                    v_simprocType_3112_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__19;
                    v___x_3113_ = 0;
                    v___x_3114_ = l_Lean_SourceInfo_fromRef(v_ref_3107_, v___x_3113_);
                    v___x_3115_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__21;
                    v___x_3116_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__22;
                    v___x_3117_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__24;
                    v___x_3118_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__26;
                    v___x_3119_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27), core::ptr::addr_of_mut!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27_once), _init_l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27);
                    if leanh::lean_obj_tag(v_doc_x3f_3098_) == 1 {
                        v_val_3120_ = leanh::lean_ctor_get(v_doc_x3f_3098_, 0);
                        leanh::lean_inc(v_val_3120_);
                        leanh::lean_dec_ref_known(v_doc_x3f_3098_, 1);
                        v___x_3121_ = l_Array_mkArray1___redArg(v_val_3120_);
                        v___y_3048_ = v___x_3114_;
                        v___y_3049_ = v___x_3116_;
                        v___y_3050_ = v___x_3118_;
                        v___y_3051_ = v___x_3119_;
                        v___y_3052_ = v___x_3109_;
                        v___y_3053_ = v___y_3100_;
                        v___y_3054_ = v_simprocType_3112_;
                        v___y_3055_ = v___x_3102_;
                        v___y_3056_ = v___x_3115_;
                        v___y_3057_ = v___x_3117_;
                        v___y_3058_ = v___x_3111_;
                        v___y_3059_ = v___x_3121_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_doc_x3f_3098_);
                        v___x_3122_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__28;
                        v___y_3048_ = v___x_3114_;
                        v___y_3049_ = v___x_3116_;
                        v___y_3050_ = v___x_3118_;
                        v___y_3051_ = v___x_3119_;
                        v___y_3052_ = v___x_3109_;
                        v___y_3053_ = v___y_3100_;
                        v___y_3054_ = v_simprocType_3112_;
                        v___y_3055_ = v___x_3102_;
                        v___y_3056_ = v___x_3115_;
                        v___y_3057_ = v___x_3117_;
                        v___y_3058_ = v___x_3111_;
                        v___y_3059_ = v___x_3122_;
                        state = 1;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Builtin__simproc__decl___x28___x29_x3a_x3d____1___boxed(
    mut v_x_3141_: *mut leanh::LeanObject,
    mut v_a_3142_: *mut leanh::LeanObject,
    mut v_a_3143_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3144_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3144_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Builtin__simproc__decl___x28___x29_x3a_x3d____1(v_x_3141_, v_a_3142_, v_a_3143_);
    leanh::lean_dec_ref(v_a_3142_);
    return v_res_3144_;
}
pub unsafe fn l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Builtin__dsimproc__decl___x28___x29_x3a_x3d____1(
    mut v_x_3145_: *mut leanh::LeanObject,
    mut v_a_3146_: *mut leanh::LeanObject,
    mut v_a_3147_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_3201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: u8 = 0;
    let mut v___x_3208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_simprocType_3215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3216_: u8 = 0;
    let mut v___x_3217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: u8 = 0;
    let mut v___x_3228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: u8 = 0;
    let mut v___x_3233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3234_: u8 = 0;
    let mut v___x_3235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_3237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: u8 = 0;
    let mut v___x_3240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3148_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0;
                v___x_3149_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1;
                v___x_3226_ = l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__1;
                leanh::lean_inc(v_x_3145_);
                v___x_3227_ = l_Lean_Syntax_isOfKind(v_x_3145_, v___x_3226_);
                if v___x_3227_ == 0 {
                    leanh::lean_dec(v_x_3145_);
                    v___x_3228_ = leanh::lean_box(1);
                    v___x_3229_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3229_, 0, v___x_3228_);
                    leanh::lean_ctor_set(v___x_3229_, 1, v_a_3147_);
                    return v___x_3229_;
                } else {
                    v___x_3230_ = leanh::lean_unsigned_to_nat(0);
                    v___x_3231_ = l_Lean_Syntax_getArg(v_x_3145_, v___x_3230_);
                    v___x_3232_ = l_Lean_Syntax_isNone(v___x_3231_);
                    if v___x_3232_ == 0 {
                        v___x_3233_ = leanh::lean_unsigned_to_nat(1);
                        leanh::lean_inc(v___x_3231_);
                        v___x_3234_ = l_Lean_Syntax_matchesNull(v___x_3231_, v___x_3233_);
                        if v___x_3234_ == 0 {
                            leanh::lean_dec(v___x_3231_);
                            leanh::lean_dec(v_x_3145_);
                            v___x_3235_ = leanh::lean_box(1);
                            v___x_3236_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_3236_, 0, v___x_3235_);
                            leanh::lean_ctor_set(v___x_3236_, 1, v_a_3147_);
                            return v___x_3236_;
                        } else {
                            v_doc_x3f_3237_ = l_Lean_Syntax_getArg(v___x_3231_, v___x_3230_);
                            leanh::lean_dec(v___x_3231_);
                            v___x_3238_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__29;
                            leanh::lean_inc(v_doc_x3f_3237_);
                            v___x_3239_ = l_Lean_Syntax_isOfKind(v_doc_x3f_3237_, v___x_3238_);
                            if v___x_3239_ == 0 {
                                leanh::lean_dec(v_doc_x3f_3237_);
                                leanh::lean_dec(v_x_3145_);
                                v___x_3240_ = leanh::lean_box(1);
                                v___x_3241_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3241_, 0, v___x_3240_);
                                leanh::lean_ctor_set(v___x_3241_, 1, v_a_3147_);
                                return v___x_3241_;
                            } else {
                                v___x_3242_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_3242_, 0, v_doc_x3f_3237_);
                                v_doc_x3f_3201_ = v___x_3242_;
                                v___y_3202_ = v_a_3146_;
                                v___y_3203_ = v_a_3147_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v___x_3231_);
                        v___x_3243_ = leanh::lean_box(0);
                        v_doc_x3f_3201_ = v___x_3243_;
                        v___y_3202_ = v_a_3146_;
                        v___y_3203_ = v_a_3147_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref_n(v___y_3157_, 2);
                v___x_3163_ = l_Array_append___redArg(v___y_3157_, v___y_3162_);
                leanh::lean_dec_ref(v___y_3162_);
                leanh::lean_inc_n(v___y_3159_, 4);
                leanh::lean_inc_n(v___y_3153_, 17);
                v___x_3164_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3164_, 0, v___y_3153_);
                leanh::lean_ctor_set(v___x_3164_, 1, v___y_3159_);
                leanh::lean_ctor_set(v___x_3164_, 2, v___x_3163_);
                v___x_3165_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3165_, 0, v___y_3153_);
                leanh::lean_ctor_set(v___x_3165_, 1, v___y_3159_);
                leanh::lean_ctor_set(v___x_3165_, 2, v___y_3157_);
                leanh::lean_inc_ref_n(v___x_3165_, 11);
                leanh::lean_inc(v___y_3161_);
                v___x_3166_ = l_Lean_Syntax_node7(
                    v___y_3153_,
                    v___y_3161_,
                    v___x_3164_,
                    v___x_3165_,
                    v___x_3165_,
                    v___x_3165_,
                    v___x_3165_,
                    v___x_3165_,
                    v___x_3165_,
                );
                v___x_3167_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__1;
                leanh::lean_inc_ref_n(v___y_3155_, 4);
                v___x_3168_ =
                    l_Lean_Name_mkStr4(v___x_3148_, v___x_3149_, v___y_3155_, v___x_3167_);
                v___x_3169_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__2;
                v___x_3170_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3170_, 0, v___y_3153_);
                leanh::lean_ctor_set(v___x_3170_, 1, v___x_3169_);
                v___x_3171_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__3;
                v___x_3172_ =
                    l_Lean_Name_mkStr4(v___x_3148_, v___x_3149_, v___y_3155_, v___x_3171_);
                leanh::lean_inc(v___y_3151_);
                v___x_3173_ =
                    l_Lean_Syntax_node2(v___y_3153_, v___x_3172_, v___y_3151_, v___x_3165_);
                v___x_3174_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__4;
                v___x_3175_ =
                    l_Lean_Name_mkStr4(v___x_3148_, v___x_3149_, v___y_3155_, v___x_3174_);
                v___x_3176_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__7;
                v___x_3177_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__8;
                v___x_3178_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3178_, 0, v___y_3153_);
                leanh::lean_ctor_set(v___x_3178_, 1, v___x_3177_);
                leanh::lean_inc(v___y_3160_);
                v___x_3179_ = lean_mk_syntax_ident(v___y_3160_);
                v___x_3180_ =
                    l_Lean_Syntax_node2(v___y_3153_, v___x_3176_, v___x_3178_, v___x_3179_);
                v___x_3181_ = l_Lean_Syntax_node1(v___y_3153_, v___y_3159_, v___x_3180_);
                v___x_3182_ =
                    l_Lean_Syntax_node2(v___y_3153_, v___x_3175_, v___x_3165_, v___x_3181_);
                v___x_3183_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__9;
                v___x_3184_ =
                    l_Lean_Name_mkStr4(v___x_3148_, v___x_3149_, v___y_3155_, v___x_3183_);
                v___x_3185_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__10;
                v___x_3186_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3186_, 0, v___y_3153_);
                leanh::lean_ctor_set(v___x_3186_, 1, v___x_3185_);
                v___x_3187_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__13;
                v___x_3188_ =
                    l_Lean_Syntax_node2(v___y_3153_, v___x_3187_, v___x_3165_, v___x_3165_);
                v___x_3189_ = l_Lean_Syntax_node4(
                    v___y_3153_,
                    v___x_3184_,
                    v___x_3186_,
                    v___y_3158_,
                    v___x_3188_,
                    v___x_3165_,
                );
                v___x_3190_ = l_Lean_Syntax_node5(
                    v___y_3153_,
                    v___x_3168_,
                    v___x_3170_,
                    v___x_3173_,
                    v___x_3182_,
                    v___x_3189_,
                    v___x_3165_,
                );
                leanh::lean_inc(v___y_3154_);
                v___x_3191_ =
                    l_Lean_Syntax_node2(v___y_3153_, v___y_3154_, v___x_3166_, v___x_3190_);
                v___x_3192_ = l_Lean_Parser_simprocPatternBuiltin___closed__1;
                v___x_3193_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Builtin__simproc__decl___x28___x29_x3a_x3d____1___closed__0;
                v___x_3194_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3194_, 0, v___y_3153_);
                leanh::lean_ctor_set(v___x_3194_, 1, v___x_3193_);
                v___x_3195_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__15;
                v___x_3196_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3196_, 0, v___y_3153_);
                leanh::lean_ctor_set(v___x_3196_, 1, v___x_3195_);
                v___x_3197_ = l_Lean_Syntax_node4(
                    v___y_3153_,
                    v___x_3192_,
                    v___x_3194_,
                    v___y_3152_,
                    v___x_3196_,
                    v___y_3151_,
                );
                v___x_3198_ =
                    l_Lean_Syntax_node2(v___y_3153_, v___y_3159_, v___x_3191_, v___x_3197_);
                v___x_3199_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3199_, 0, v___x_3198_);
                leanh::lean_ctor_set(v___x_3199_, 1, v___y_3156_);
                return v___x_3199_;
            }
            2 => {
                v___x_3204_ = leanh::lean_unsigned_to_nat(2);
                v___x_3205_ = l_Lean_Syntax_getArg(v_x_3145_, v___x_3204_);
                v___x_3206_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__27;
                leanh::lean_inc(v___x_3205_);
                v___x_3207_ = l_Lean_Syntax_isOfKind(v___x_3205_, v___x_3206_);
                if v___x_3207_ == 0 {
                    leanh::lean_dec(v___x_3205_);
                    leanh::lean_dec(v_doc_x3f_3201_);
                    leanh::lean_dec(v_x_3145_);
                    v___x_3208_ = leanh::lean_box(1);
                    v___x_3209_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3209_, 0, v___x_3208_);
                    leanh::lean_ctor_set(v___x_3209_, 1, v___y_3203_);
                    return v___x_3209_;
                } else {
                    v_ref_3210_ = leanh::lean_ctor_get(v___y_3202_, 5);
                    v___x_3211_ = leanh::lean_unsigned_to_nat(4);
                    v___x_3212_ = l_Lean_Syntax_getArg(v_x_3145_, v___x_3211_);
                    v___x_3213_ = leanh::lean_unsigned_to_nat(7);
                    v___x_3214_ = l_Lean_Syntax_getArg(v_x_3145_, v___x_3213_);
                    leanh::lean_dec(v_x_3145_);
                    v_simprocType_3215_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Dsimproc__decl___x28___x29_x3a_x3d____1___closed__1;
                    v___x_3216_ = 0;
                    v___x_3217_ = l_Lean_SourceInfo_fromRef(v_ref_3210_, v___x_3216_);
                    v___x_3218_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__21;
                    v___x_3219_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__22;
                    v___x_3220_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__24;
                    v___x_3221_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__26;
                    v___x_3222_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27), core::ptr::addr_of_mut!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27_once), _init_l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27);
                    if leanh::lean_obj_tag(v_doc_x3f_3201_) == 1 {
                        v_val_3223_ = leanh::lean_ctor_get(v_doc_x3f_3201_, 0);
                        leanh::lean_inc(v_val_3223_);
                        leanh::lean_dec_ref_known(v_doc_x3f_3201_, 1);
                        v___x_3224_ = l_Array_mkArray1___redArg(v_val_3223_);
                        v___y_3151_ = v___x_3205_;
                        v___y_3152_ = v___x_3212_;
                        v___y_3153_ = v___x_3217_;
                        v___y_3154_ = v___x_3220_;
                        v___y_3155_ = v___x_3219_;
                        v___y_3156_ = v___y_3203_;
                        v___y_3157_ = v___x_3222_;
                        v___y_3158_ = v___x_3214_;
                        v___y_3159_ = v___x_3218_;
                        v___y_3160_ = v_simprocType_3215_;
                        v___y_3161_ = v___x_3221_;
                        v___y_3162_ = v___x_3224_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_doc_x3f_3201_);
                        v___x_3225_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__28;
                        v___y_3151_ = v___x_3205_;
                        v___y_3152_ = v___x_3212_;
                        v___y_3153_ = v___x_3217_;
                        v___y_3154_ = v___x_3220_;
                        v___y_3155_ = v___x_3219_;
                        v___y_3156_ = v___y_3203_;
                        v___y_3157_ = v___x_3222_;
                        v___y_3158_ = v___x_3214_;
                        v___y_3159_ = v___x_3218_;
                        v___y_3160_ = v_simprocType_3215_;
                        v___y_3161_ = v___x_3221_;
                        v___y_3162_ = v___x_3225_;
                        state = 1;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Builtin__dsimproc__decl___x28___x29_x3a_x3d____1___boxed(
    mut v_x_3244_: *mut leanh::LeanObject,
    mut v_a_3245_: *mut leanh::LeanObject,
    mut v_a_3246_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3247_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3247_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Builtin__dsimproc__decl___x28___x29_x3a_x3d____1(v_x_3244_, v_a_3245_, v_a_3246_);
    leanh::lean_dec_ref(v_a_3245_);
    return v_res_3247_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0(
    mut v_kind_3274_: *mut leanh::LeanObject,
    mut v_n_3275_: *mut leanh::LeanObject,
    mut v_pre_x3f_3276_: *mut leanh::LeanObject,
    mut v_as_3277_: *mut leanh::LeanObject,
    mut v_sz_3278_: usize,
    mut v_i_3279_: usize,
    mut v_b_3280_: *mut leanh::LeanObject,
    mut v___y_3281_: *mut leanh::LeanObject,
    mut v___y_3282_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: u8 = 0;
    let mut v___x_3296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3311_: usize = 0;
    let mut v___x_3312_: usize = 0;
    let mut v_fst_3315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: u8 = 0;
    let mut v___x_3322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: u8 = 0;
    let mut v___x_3327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: u8 = 0;
    let mut v___x_3329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3321_ = lean_usize_dec_lt(v_i_3279_, v_sz_3278_);
                if v___x_3321_ == 0 {
                    leanh::lean_dec(v_n_3275_);
                    leanh::lean_dec(v_kind_3274_);
                    v___x_3322_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3322_, 0, v_b_3280_);
                    leanh::lean_ctor_set(v___x_3322_, 1, v___y_3282_);
                    return v___x_3322_;
                } else {
                    v_a_3323_ = lean_array_uget_borrowed(v_as_3277_, v_i_3279_);
                    v___x_3324_ = l_Lean_TSyntax_getId(v_a_3323_);
                    v___x_3325_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__5;
                    v___x_3326_ = lean_name_eq(v___x_3324_, v___x_3325_);
                    if v___x_3326_ == 0 {
                        v___x_3327_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__7;
                        v___x_3328_ = lean_name_eq(v___x_3324_, v___x_3327_);
                        if v___x_3328_ == 0 {
                            v___x_3329_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__8;
                            v___x_3330_ = lean_name_append_after(v___x_3324_, v___x_3329_);
                            v___x_3331_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__9;
                            leanh::lean_inc(v___x_3330_);
                            v___x_3332_ = l_Lean_Name_append(v___x_3331_, v___x_3330_);
                            v___x_3333_ = l_Lean_Name_toString(v___x_3330_, v___x_3321_);
                            v_fst_3315_ = v___x_3332_;
                            v_snd_3316_ = v___x_3333_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_3324_);
                            v___x_3334_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__10;
                            v___x_3335_ = l_Lean_Parser_Attr_sevalprocAttr___closed__2;
                            v_fst_3315_ = v___x_3334_;
                            v_snd_3316_ = v___x_3335_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_3324_);
                        v___x_3336_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__11;
                        v___x_3337_ = l_Lean_Parser_Attr_simprocAttr___closed__3;
                        v_fst_3315_ = v___x_3336_;
                        v_snd_3316_ = v___x_3337_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v_ref_3287_ = leanh::lean_ctor_get(v___y_3281_, 5);
                v___x_3288_ = l_Lean_mkOptionalNode(v___y_3286_);
                v___x_3289_ = leanh::lean_unsigned_to_nat(2);
                v___x_3290_ = lean_mk_empty_array_with_capacity(v___x_3289_);
                v___x_3291_ = lean_array_push(v___x_3290_, v___y_3285_);
                v___x_3292_ = lean_array_push(v___x_3291_, v___x_3288_);
                v___x_3293_ = leanh::lean_box(2);
                v___x_3294_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3294_, 0, v___x_3293_);
                leanh::lean_ctor_set(v___x_3294_, 1, v___y_3284_);
                leanh::lean_ctor_set(v___x_3294_, 2, v___x_3292_);
                v___x_3295_ = 0;
                v___x_3296_ = l_Lean_SourceInfo_fromRef(v_ref_3287_, v___x_3295_);
                v___x_3297_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__0;
                v___x_3298_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__1;
                leanh::lean_inc_n(v___x_3296_, 6);
                v___x_3299_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3299_, 0, v___x_3296_);
                leanh::lean_ctor_set(v___x_3299_, 1, v___x_3297_);
                v___x_3300_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__24;
                v___x_3301_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3301_, 0, v___x_3296_);
                leanh::lean_ctor_set(v___x_3301_, 1, v___x_3300_);
                v___x_3302_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__21;
                v___x_3303_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__3;
                leanh::lean_inc(v_kind_3274_);
                v___x_3304_ =
                    l_Lean_Syntax_node2(v___x_3296_, v___x_3303_, v_kind_3274_, v___x_3294_);
                v___x_3305_ = l_Lean_Syntax_node1(v___x_3296_, v___x_3302_, v___x_3304_);
                v___x_3306_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__34;
                v___x_3307_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3307_, 0, v___x_3296_);
                leanh::lean_ctor_set(v___x_3307_, 1, v___x_3306_);
                leanh::lean_inc(v_n_3275_);
                v___x_3308_ = l_Lean_Syntax_node1(v___x_3296_, v___x_3302_, v_n_3275_);
                v___x_3309_ = l_Lean_Syntax_node5(
                    v___x_3296_,
                    v___x_3298_,
                    v___x_3299_,
                    v___x_3301_,
                    v___x_3305_,
                    v___x_3307_,
                    v___x_3308_,
                );
                v___x_3310_ = lean_array_push(v_b_3280_, v___x_3309_);
                v___x_3311_ = 1usize;
                v___x_3312_ = lean_usize_add(v_i_3279_, v___x_3311_);
                v_i_3279_ = v___x_3312_;
                v_b_3280_ = v___x_3310_;
                state = 0;
                continue;
            }
            2 => {
                v___x_3317_ = l_Lean_mkAtom(v_snd_3316_);
                if leanh::lean_obj_tag(v_pre_x3f_3276_) == 0 {
                    v___x_3318_ = leanh::lean_box(0);
                    v___y_3284_ = v_fst_3315_;
                    v___y_3285_ = v___x_3317_;
                    v___y_3286_ = v___x_3318_;
                    state = 1;
                    continue;
                } else {
                    v_val_3319_ = leanh::lean_ctor_get(v_pre_x3f_3276_, 0);
                    leanh::lean_inc(v_val_3319_);
                    v___x_3320_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3320_, 0, v_val_3319_);
                    v___y_3284_ = v_fst_3315_;
                    v___y_3285_ = v___x_3317_;
                    v___y_3286_ = v___x_3320_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___boxed(
    mut v_kind_3338_: *mut leanh::LeanObject,
    mut v_n_3339_: *mut leanh::LeanObject,
    mut v_pre_x3f_3340_: *mut leanh::LeanObject,
    mut v_as_3341_: *mut leanh::LeanObject,
    mut v_sz_3342_: *mut leanh::LeanObject,
    mut v_i_3343_: *mut leanh::LeanObject,
    mut v_b_3344_: *mut leanh::LeanObject,
    mut v___y_3345_: *mut leanh::LeanObject,
    mut v___y_3346_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3347_: usize = 0;
    let mut v_i_boxed_3348_: usize = 0;
    let mut v_res_3349_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3347_ = leanh::lean_unbox_usize(v_sz_3342_);
    leanh::lean_dec(v_sz_3342_);
    v_i_boxed_3348_ = leanh::lean_unbox_usize(v_i_3343_);
    leanh::lean_dec(v_i_3343_);
    v_res_3349_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0(v_kind_3338_, v_n_3339_, v_pre_x3f_3340_, v_as_3341_, v_sz_boxed_3347_, v_i_boxed_3348_, v_b_3344_, v___y_3345_, v___y_3346_);
    leanh::lean_dec_ref(v___y_3345_);
    leanh::lean_dec_ref(v_as_3341_);
    leanh::lean_dec(v_pre_x3f_3340_);
    return v_res_3349_;
}
pub unsafe fn l___private_Init_Simproc_0__Lean_Parser_mkAttributeCmds(
    mut v_kind_3352_: *mut leanh::LeanObject,
    mut v_pre_x3f_3353_: *mut leanh::LeanObject,
    mut v_ids_x3f_3354_: *mut leanh::LeanObject,
    mut v_n_3355_: *mut leanh::LeanObject,
    mut v_a_3356_: *mut leanh::LeanObject,
    mut v_a_3357_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cmds_3358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3361_: usize = 0;
    let mut v___x_3362_: usize = 0;
    let mut v___x_3363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3368_: u8 = 0;
    let mut v___x_3370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3372_: u8 = 0;
    let mut v_a_3373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3377_: u8 = 0;
    let mut v___x_3379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3381_: u8 = 0;
    let mut v_ref_3382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3383_: u8 = 0;
    let mut v___x_3384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_cmds_3358_ = l___private_Init_Simproc_0__Lean_Parser_mkAttributeCmds___closed__0;
                if leanh::lean_obj_tag(v_ids_x3f_3354_) == 1 {
                    v_val_3359_ = leanh::lean_ctor_get(v_ids_x3f_3354_, 0);
                    v___x_3360_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_3359_);
                    v_sz_3361_ = lean_array_size(v___x_3360_);
                    v___x_3362_ = 0usize;
                    v___x_3363_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0(v_kind_3352_, v_n_3355_, v_pre_x3f_3353_, v___x_3360_, v_sz_3361_, v___x_3362_, v_cmds_3358_, v_a_3356_, v_a_3357_);
                    leanh::lean_dec_ref(v___x_3360_);
                    leanh::lean_dec(v_pre_x3f_3353_);
                    if leanh::lean_obj_tag(v___x_3363_) == 0 {
                        v_a_3364_ = leanh::lean_ctor_get(v___x_3363_, 0);
                        v_a_3365_ = leanh::lean_ctor_get(v___x_3363_, 1);
                        v_isSharedCheck_3372_ =
                            (!leanh::lean_is_exclusive(v___x_3363_)) as u8;
                        if v_isSharedCheck_3372_ == 0 {
                            v___x_3367_ = v___x_3363_;
                            v_isShared_3368_ = v_isSharedCheck_3372_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3365_);
                            leanh::lean_inc(v_a_3364_);
                            leanh::lean_dec(v___x_3363_);
                            v___x_3367_ = leanh::lean_box(0);
                            v_isShared_3368_ = v_isSharedCheck_3372_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3373_ = leanh::lean_ctor_get(v___x_3363_, 0);
                        v_a_3374_ = leanh::lean_ctor_get(v___x_3363_, 1);
                        v_isSharedCheck_3381_ =
                            (!leanh::lean_is_exclusive(v___x_3363_)) as u8;
                        if v_isSharedCheck_3381_ == 0 {
                            v___x_3376_ = v___x_3363_;
                            v_isShared_3377_ = v_isSharedCheck_3381_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3374_);
                            leanh::lean_inc(v_a_3373_);
                            leanh::lean_dec(v___x_3363_);
                            v___x_3376_ = leanh::lean_box(0);
                            v_isShared_3377_ = v_isSharedCheck_3381_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_ref_3382_ = leanh::lean_ctor_get(v_a_3356_, 5);
                    v___x_3383_ = 0;
                    v___x_3384_ = l_Lean_SourceInfo_fromRef(v_ref_3382_, v___x_3383_);
                    v___x_3385_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__0;
                    v___x_3386_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__1;
                    leanh::lean_inc_n(v___x_3384_, 3);
                    v___x_3387_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3387_, 0, v___x_3384_);
                    leanh::lean_ctor_set(v___x_3387_, 1, v___x_3385_);
                    v___x_3388_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__24;
                    v___x_3389_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3389_, 0, v___x_3384_);
                    leanh::lean_ctor_set(v___x_3389_, 1, v___x_3388_);
                    v___x_3390_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__21;
                    v___x_3391_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__3;
                    v___x_3392_ = l_Lean_Parser_Attr_simprocAttr___closed__2;
                    v___x_3393_ = l_Lean_Parser_Attr_simprocAttr___closed__3;
                    v___x_3394_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3394_, 0, v___x_3384_);
                    leanh::lean_ctor_set(v___x_3394_, 1, v___x_3393_);
                    v___x_3395_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27), core::ptr::addr_of_mut!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27_once), _init_l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27);
                    if leanh::lean_obj_tag(v_pre_x3f_3353_) == 1 {
                        v_val_3409_ = leanh::lean_ctor_get(v_pre_x3f_3353_, 0);
                        leanh::lean_inc(v_val_3409_);
                        leanh::lean_dec_ref_known(v_pre_x3f_3353_, 1);
                        v___x_3410_ = l_Array_mkArray1___redArg(v_val_3409_);
                        v___y_3397_ = v___x_3410_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_dec(v_pre_x3f_3353_);
                        v___x_3411_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__28;
                        v___y_3397_ = v___x_3411_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3368_ == 0 {
                    v___x_3370_ = v___x_3367_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3371_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3371_, 0, v_a_3364_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3371_, 1, v_a_3365_);
                    v___x_3370_ = v_reuseFailAlloc_3371_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3370_;
            }
            3 => {
                if v_isShared_3377_ == 0 {
                    v___x_3379_ = v___x_3376_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3380_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3380_, 0, v_a_3373_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3380_, 1, v_a_3374_);
                    v___x_3379_ = v_reuseFailAlloc_3380_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3379_;
            }
            5 => {
                v___x_3398_ = l_Array_append___redArg(v___x_3395_, v___y_3397_);
                leanh::lean_dec_ref(v___y_3397_);
                leanh::lean_inc_n(v___x_3384_, 6);
                v___x_3399_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3399_, 0, v___x_3384_);
                leanh::lean_ctor_set(v___x_3399_, 1, v___x_3390_);
                leanh::lean_ctor_set(v___x_3399_, 2, v___x_3398_);
                v___x_3400_ =
                    l_Lean_Syntax_node2(v___x_3384_, v___x_3392_, v___x_3394_, v___x_3399_);
                v___x_3401_ =
                    l_Lean_Syntax_node2(v___x_3384_, v___x_3391_, v_kind_3352_, v___x_3400_);
                v___x_3402_ = l_Lean_Syntax_node1(v___x_3384_, v___x_3390_, v___x_3401_);
                v___x_3403_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__34;
                v___x_3404_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3404_, 0, v___x_3384_);
                leanh::lean_ctor_set(v___x_3404_, 1, v___x_3403_);
                v___x_3405_ = l_Lean_Syntax_node1(v___x_3384_, v___x_3390_, v_n_3355_);
                v___x_3406_ = l_Lean_Syntax_node5(
                    v___x_3384_,
                    v___x_3386_,
                    v___x_3387_,
                    v___x_3389_,
                    v___x_3402_,
                    v___x_3404_,
                    v___x_3405_,
                );
                v___x_3407_ = lean_array_push(v_cmds_3358_, v___x_3406_);
                v___x_3408_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3408_, 0, v___x_3407_);
                leanh::lean_ctor_set(v___x_3408_, 1, v_a_3357_);
                return v___x_3408_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Simproc_0__Lean_Parser_mkAttributeCmds___boxed(
    mut v_kind_3412_: *mut leanh::LeanObject,
    mut v_pre_x3f_3413_: *mut leanh::LeanObject,
    mut v_ids_x3f_3414_: *mut leanh::LeanObject,
    mut v_n_3415_: *mut leanh::LeanObject,
    mut v_a_3416_: *mut leanh::LeanObject,
    mut v_a_3417_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3418_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3418_ = l___private_Init_Simproc_0__Lean_Parser_mkAttributeCmds(
        v_kind_3412_,
        v_pre_x3f_3413_,
        v_ids_x3f_3414_,
        v_n_3415_,
        v_a_3416_,
        v_a_3417_,
    );
    leanh::lean_dec_ref(v_a_3416_);
    leanh::lean_dec(v_ids_x3f_3414_);
    return v_res_3418_;
}
pub unsafe fn l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1(
    mut v_x_3426_: *mut leanh::LeanObject,
    mut v_a_3427_: *mut leanh::LeanObject,
    mut v_a_3428_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3453_: u8 = 0;
    let mut v___x_3454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3469_: u8 = 0;
    let mut v_a_3470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3474_: u8 = 0;
    let mut v___x_3476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3478_: u8 = 0;
    let mut v___x_3479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: u8 = 0;
    let mut v___x_3481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ids_x3f_3489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_3493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3495_: u8 = 0;
    let mut v___x_3496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3503_: u8 = 0;
    let mut v___x_3504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_x3f_3516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3521_: u8 = 0;
    let mut v___x_3522_: u8 = 0;
    let mut v___x_3523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ids_x3f_3526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_3530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_3534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: u8 = 0;
    let mut v___x_3537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: u8 = 0;
    let mut v___x_3542_: u8 = 0;
    let mut v___x_3543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_x3f_3545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: u8 = 0;
    let mut v___x_3550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3551_: u8 = 0;
    let mut v___x_3552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_3554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3556_: u8 = 0;
    let mut v___x_3557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3479_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__3;
                leanh::lean_inc(v_x_3426_);
                v___x_3480_ = l_Lean_Syntax_isOfKind(v_x_3426_, v___x_3479_);
                if v___x_3480_ == 0 {
                    leanh::lean_dec(v_x_3426_);
                    v___x_3481_ = leanh::lean_box(1);
                    v___x_3482_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3482_, 0, v___x_3481_);
                    leanh::lean_ctor_set(v___x_3482_, 1, v_a_3428_);
                    return v___x_3482_;
                } else {
                    v___x_3483_ = leanh::lean_unsigned_to_nat(0);
                    v___x_3548_ = l_Lean_Syntax_getArg(v_x_3426_, v___x_3483_);
                    v___x_3549_ = l_Lean_Syntax_isNone(v___x_3548_);
                    if v___x_3549_ == 0 {
                        v___x_3550_ = leanh::lean_unsigned_to_nat(1);
                        leanh::lean_inc(v___x_3548_);
                        v___x_3551_ = l_Lean_Syntax_matchesNull(v___x_3548_, v___x_3550_);
                        if v___x_3551_ == 0 {
                            leanh::lean_dec(v___x_3548_);
                            leanh::lean_dec(v_x_3426_);
                            v___x_3552_ = leanh::lean_box(1);
                            v___x_3553_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_3553_, 0, v___x_3552_);
                            leanh::lean_ctor_set(v___x_3553_, 1, v_a_3428_);
                            return v___x_3553_;
                        } else {
                            v_doc_x3f_3554_ = l_Lean_Syntax_getArg(v___x_3548_, v___x_3483_);
                            leanh::lean_dec(v___x_3548_);
                            v___x_3555_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__29;
                            leanh::lean_inc(v_doc_x3f_3554_);
                            v___x_3556_ = l_Lean_Syntax_isOfKind(v_doc_x3f_3554_, v___x_3555_);
                            if v___x_3556_ == 0 {
                                leanh::lean_dec(v_doc_x3f_3554_);
                                leanh::lean_dec(v_x_3426_);
                                v___x_3557_ = leanh::lean_box(1);
                                v___x_3558_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3558_, 0, v___x_3557_);
                                leanh::lean_ctor_set(v___x_3558_, 1, v_a_3428_);
                                return v___x_3558_;
                            } else {
                                v___x_3559_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_3559_, 0, v_doc_x3f_3554_);
                                v_doc_x3f_3530_ = v___x_3559_;
                                v___y_3531_ = v_a_3427_;
                                v___y_3532_ = v_a_3428_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v___x_3548_);
                        v___x_3560_ = leanh::lean_box(0);
                        v_doc_x3f_3530_ = v___x_3560_;
                        v___y_3531_ = v_a_3427_;
                        v___y_3532_ = v_a_3428_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref(v___y_3434_);
                v___x_3444_ = l_Array_append___redArg(v___y_3434_, v___y_3443_);
                leanh::lean_dec_ref(v___y_3443_);
                leanh::lean_inc(v___y_3439_);
                leanh::lean_inc_n(v___y_3441_, 2);
                v___x_3445_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3445_, 0, v___y_3441_);
                leanh::lean_ctor_set(v___x_3445_, 1, v___y_3439_);
                leanh::lean_ctor_set(v___x_3445_, 2, v___x_3444_);
                v___x_3446_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0;
                v___x_3447_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3447_, 0, v___y_3441_);
                leanh::lean_ctor_set(v___x_3447_, 1, v___x_3446_);
                leanh::lean_inc(v___y_3435_);
                v___x_3448_ = l___private_Init_Simproc_0__Lean_Parser_mkAttributeCmds(
                    v___y_3438_,
                    v___y_3437_,
                    v___y_3433_,
                    v___y_3435_,
                    v___y_3436_,
                    v___y_3430_,
                );
                leanh::lean_dec(v___y_3433_);
                if leanh::lean_obj_tag(v___x_3448_) == 0 {
                    v_a_3449_ = leanh::lean_ctor_get(v___x_3448_, 0);
                    v_a_3450_ = leanh::lean_ctor_get(v___x_3448_, 1);
                    v_isSharedCheck_3469_ = (!leanh::lean_is_exclusive(v___x_3448_)) as u8;
                    if v_isSharedCheck_3469_ == 0 {
                        v___x_3452_ = v___x_3448_;
                        v_isShared_3453_ = v_isSharedCheck_3469_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3450_);
                        leanh::lean_inc(v_a_3449_);
                        leanh::lean_dec(v___x_3448_);
                        v___x_3452_ = leanh::lean_box(0);
                        v_isShared_3453_ = v_isSharedCheck_3469_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref_known(v___x_3447_, 2);
                    leanh::lean_dec_ref_known(v___x_3445_, 3);
                    leanh::lean_dec(v___y_3442_);
                    leanh::lean_dec(v___y_3441_);
                    leanh::lean_dec(v___y_3435_);
                    leanh::lean_dec(v___y_3431_);
                    v_a_3470_ = leanh::lean_ctor_get(v___x_3448_, 0);
                    v_a_3471_ = leanh::lean_ctor_get(v___x_3448_, 1);
                    v_isSharedCheck_3478_ = (!leanh::lean_is_exclusive(v___x_3448_)) as u8;
                    if v_isSharedCheck_3478_ == 0 {
                        v___x_3473_ = v___x_3448_;
                        v_isShared_3474_ = v_isSharedCheck_3478_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3471_);
                        leanh::lean_inc(v_a_3470_);
                        leanh::lean_dec(v___x_3448_);
                        v___x_3473_ = leanh::lean_box(0);
                        v_isShared_3474_ = v_isSharedCheck_3478_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3454_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__1;
                leanh::lean_inc_n(v___y_3441_, 3);
                v___x_3455_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3455_, 0, v___y_3441_);
                leanh::lean_ctor_set(v___x_3455_, 1, v___x_3454_);
                v___x_3456_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__47;
                v___x_3457_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3457_, 0, v___y_3441_);
                leanh::lean_ctor_set(v___x_3457_, 1, v___x_3456_);
                v___x_3458_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__10;
                v___x_3459_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3459_, 0, v___y_3441_);
                leanh::lean_ctor_set(v___x_3459_, 1, v___x_3458_);
                leanh::lean_inc(v___y_3432_);
                v___x_3460_ = l_Lean_Syntax_node8(
                    v___y_3441_,
                    v___y_3432_,
                    v___x_3445_,
                    v___x_3447_,
                    v___y_3435_,
                    v___x_3455_,
                    v___y_3431_,
                    v___x_3457_,
                    v___x_3459_,
                    v___y_3442_,
                );
                v___x_3461_ = lean_mk_empty_array_with_capacity(v___y_3440_);
                v___x_3462_ = lean_array_push(v___x_3461_, v___x_3460_);
                v___x_3463_ = l_Array_append___redArg(v___x_3462_, v_a_3449_);
                leanh::lean_dec(v_a_3449_);
                v___x_3464_ = leanh::lean_box(2);
                leanh::lean_inc(v___y_3439_);
                v___x_3465_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3465_, 0, v___x_3464_);
                leanh::lean_ctor_set(v___x_3465_, 1, v___y_3439_);
                leanh::lean_ctor_set(v___x_3465_, 2, v___x_3463_);
                if v_isShared_3453_ == 0 {
                    leanh::lean_ctor_set(v___x_3452_, 0, v___x_3465_);
                    v___x_3467_ = v___x_3452_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3468_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3468_, 0, v___x_3465_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3468_, 1, v_a_3450_);
                    v___x_3467_ = v_reuseFailAlloc_3468_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3467_;
            }
            4 => {
                if v_isShared_3474_ == 0 {
                    v___x_3476_ = v___x_3473_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3477_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3477_, 0, v_a_3470_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3477_, 1, v_a_3471_);
                    v___x_3476_ = v_reuseFailAlloc_3477_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3476_;
            }
            6 => {
                v___x_3492_ = leanh::lean_unsigned_to_nat(5);
                v_n_3493_ = l_Lean_Syntax_getArg(v_x_3426_, v___x_3492_);
                v___x_3494_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__27;
                leanh::lean_inc(v_n_3493_);
                v___x_3495_ = l_Lean_Syntax_isOfKind(v_n_3493_, v___x_3494_);
                if v___x_3495_ == 0 {
                    leanh::lean_dec(v_n_3493_);
                    leanh::lean_dec(v_ids_x3f_3489_);
                    leanh::lean_dec(v___y_3487_);
                    leanh::lean_dec(v___y_3486_);
                    leanh::lean_dec(v___y_3485_);
                    leanh::lean_dec(v_x_3426_);
                    v___x_3496_ = leanh::lean_box(1);
                    v___x_3497_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3497_, 0, v___x_3496_);
                    leanh::lean_ctor_set(v___x_3497_, 1, v___y_3491_);
                    return v___x_3497_;
                } else {
                    v_ref_3498_ = leanh::lean_ctor_get(v___y_3490_, 5);
                    v___x_3499_ = leanh::lean_unsigned_to_nat(7);
                    v___x_3500_ = l_Lean_Syntax_getArg(v_x_3426_, v___x_3499_);
                    v___x_3501_ = leanh::lean_unsigned_to_nat(10);
                    v___x_3502_ = l_Lean_Syntax_getArg(v_x_3426_, v___x_3501_);
                    leanh::lean_dec(v_x_3426_);
                    v___x_3503_ = 0;
                    v___x_3504_ = l_Lean_SourceInfo_fromRef(v_ref_3498_, v___x_3503_);
                    v___x_3505_ =
                        l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__1;
                    v___x_3506_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__21;
                    v___x_3507_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27), core::ptr::addr_of_mut!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27_once), _init_l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27);
                    if leanh::lean_obj_tag(v___y_3487_) == 1 {
                        v_val_3508_ = leanh::lean_ctor_get(v___y_3487_, 0);
                        leanh::lean_inc(v_val_3508_);
                        leanh::lean_dec_ref_known(v___y_3487_, 1);
                        v___x_3509_ = l_Array_mkArray1___redArg(v_val_3508_);
                        v___y_3430_ = v___y_3491_;
                        v___y_3431_ = v___x_3500_;
                        v___y_3432_ = v___x_3505_;
                        v___y_3433_ = v_ids_x3f_3489_;
                        v___y_3434_ = v___x_3507_;
                        v___y_3435_ = v_n_3493_;
                        v___y_3436_ = v___y_3490_;
                        v___y_3437_ = v___y_3485_;
                        v___y_3438_ = v___y_3486_;
                        v___y_3439_ = v___x_3506_;
                        v___y_3440_ = v___y_3488_;
                        v___y_3441_ = v___x_3504_;
                        v___y_3442_ = v___x_3502_;
                        v___y_3443_ = v___x_3509_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___y_3487_);
                        v___x_3510_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__28;
                        v___y_3430_ = v___y_3491_;
                        v___y_3431_ = v___x_3500_;
                        v___y_3432_ = v___x_3505_;
                        v___y_3433_ = v_ids_x3f_3489_;
                        v___y_3434_ = v___x_3507_;
                        v___y_3435_ = v_n_3493_;
                        v___y_3436_ = v___y_3490_;
                        v___y_3437_ = v___y_3485_;
                        v___y_3438_ = v___y_3486_;
                        v___y_3439_ = v___x_3506_;
                        v___y_3440_ = v___y_3488_;
                        v___y_3441_ = v___x_3504_;
                        v___y_3442_ = v___x_3502_;
                        v___y_3443_ = v___x_3510_;
                        state = 1;
                        continue;
                    }
                }
            }
            7 => {
                v___x_3519_ = leanh::lean_unsigned_to_nat(4);
                v___x_3520_ = l_Lean_Syntax_getArg(v_x_3426_, v___x_3519_);
                v___x_3521_ = l_Lean_Syntax_isNone(v___x_3520_);
                if v___x_3521_ == 0 {
                    leanh::lean_inc(v___x_3520_);
                    v___x_3522_ = l_Lean_Syntax_matchesNull(v___x_3520_, v___y_3514_);
                    if v___x_3522_ == 0 {
                        leanh::lean_dec(v___x_3520_);
                        leanh::lean_dec(v_pre_x3f_3516_);
                        leanh::lean_dec(v___y_3513_);
                        leanh::lean_dec(v___y_3512_);
                        leanh::lean_dec(v_x_3426_);
                        v___x_3523_ = leanh::lean_box(1);
                        v___x_3524_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3524_, 0, v___x_3523_);
                        leanh::lean_ctor_set(v___x_3524_, 1, v___y_3518_);
                        return v___x_3524_;
                    } else {
                        v___x_3525_ = l_Lean_Syntax_getArg(v___x_3520_, v___y_3515_);
                        leanh::lean_dec(v___x_3520_);
                        v_ids_x3f_3526_ = l_Lean_Syntax_getArgs(v___x_3525_);
                        leanh::lean_dec(v___x_3525_);
                        v___x_3527_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3527_, 0, v_ids_x3f_3526_);
                        v___y_3485_ = v_pre_x3f_3516_;
                        v___y_3486_ = v___y_3512_;
                        v___y_3487_ = v___y_3513_;
                        v___y_3488_ = v___y_3515_;
                        v_ids_x3f_3489_ = v___x_3527_;
                        v___y_3490_ = v___y_3517_;
                        v___y_3491_ = v___y_3518_;
                        state = 6;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_3520_);
                    v___x_3528_ = leanh::lean_box(0);
                    v___y_3485_ = v_pre_x3f_3516_;
                    v___y_3486_ = v___y_3512_;
                    v___y_3487_ = v___y_3513_;
                    v___y_3488_ = v___y_3515_;
                    v_ids_x3f_3489_ = v___x_3528_;
                    v___y_3490_ = v___y_3517_;
                    v___y_3491_ = v___y_3518_;
                    state = 6;
                    continue;
                }
            }
            8 => {
                v___x_3533_ = leanh::lean_unsigned_to_nat(1);
                v_kind_3534_ = l_Lean_Syntax_getArg(v_x_3426_, v___x_3533_);
                v___x_3535_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__2;
                leanh::lean_inc(v_kind_3534_);
                v___x_3536_ = l_Lean_Syntax_isOfKind(v_kind_3534_, v___x_3535_);
                if v___x_3536_ == 0 {
                    leanh::lean_dec(v_kind_3534_);
                    leanh::lean_dec(v_doc_x3f_3530_);
                    leanh::lean_dec(v_x_3426_);
                    v___x_3537_ = leanh::lean_box(1);
                    v___x_3538_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3538_, 0, v___x_3537_);
                    leanh::lean_ctor_set(v___x_3538_, 1, v___y_3532_);
                    return v___x_3538_;
                } else {
                    v___x_3539_ = leanh::lean_unsigned_to_nat(3);
                    v___x_3540_ = l_Lean_Syntax_getArg(v_x_3426_, v___x_3539_);
                    v___x_3541_ = l_Lean_Syntax_isNone(v___x_3540_);
                    if v___x_3541_ == 0 {
                        leanh::lean_inc(v___x_3540_);
                        v___x_3542_ = l_Lean_Syntax_matchesNull(v___x_3540_, v___x_3533_);
                        if v___x_3542_ == 0 {
                            leanh::lean_dec(v___x_3540_);
                            leanh::lean_dec(v_kind_3534_);
                            leanh::lean_dec(v_doc_x3f_3530_);
                            leanh::lean_dec(v_x_3426_);
                            v___x_3543_ = leanh::lean_box(1);
                            v___x_3544_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_3544_, 0, v___x_3543_);
                            leanh::lean_ctor_set(v___x_3544_, 1, v___y_3532_);
                            return v___x_3544_;
                        } else {
                            v_pre_x3f_3545_ = l_Lean_Syntax_getArg(v___x_3540_, v___x_3483_);
                            leanh::lean_dec(v___x_3540_);
                            v___x_3546_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_3546_, 0, v_pre_x3f_3545_);
                            v___y_3512_ = v_kind_3534_;
                            v___y_3513_ = v_doc_x3f_3530_;
                            v___y_3514_ = v___x_3539_;
                            v___y_3515_ = v___x_3533_;
                            v_pre_x3f_3516_ = v___x_3546_;
                            v___y_3517_ = v___y_3531_;
                            v___y_3518_ = v___y_3532_;
                            state = 7;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_3540_);
                        v___x_3547_ = leanh::lean_box(0);
                        v___y_3512_ = v_kind_3534_;
                        v___y_3513_ = v_doc_x3f_3530_;
                        v___y_3514_ = v___x_3539_;
                        v___y_3515_ = v___x_3533_;
                        v_pre_x3f_3516_ = v___x_3547_;
                        v___y_3517_ = v___y_3531_;
                        v___y_3518_ = v___y_3532_;
                        state = 7;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___boxed(
    mut v_x_3561_: *mut leanh::LeanObject,
    mut v_a_3562_: *mut leanh::LeanObject,
    mut v_a_3563_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3564_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3564_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1(v_x_3561_, v_a_3562_, v_a_3563_);
    leanh::lean_dec_ref(v_a_3562_);
    return v_res_3564_;
}
pub unsafe fn l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d____1(
    mut v_x_3566_: *mut leanh::LeanObject,
    mut v_a_3567_: *mut leanh::LeanObject,
    mut v_a_3568_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3593_: u8 = 0;
    let mut v___x_3594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3609_: u8 = 0;
    let mut v_a_3610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3614_: u8 = 0;
    let mut v___x_3616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3618_: u8 = 0;
    let mut v___x_3619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3620_: u8 = 0;
    let mut v___x_3621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ids_x3f_3629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_3633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: u8 = 0;
    let mut v___x_3636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: u8 = 0;
    let mut v___x_3644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_x3f_3656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3661_: u8 = 0;
    let mut v___x_3662_: u8 = 0;
    let mut v___x_3663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ids_x3f_3666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_3670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_3674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3676_: u8 = 0;
    let mut v___x_3677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: u8 = 0;
    let mut v___x_3682_: u8 = 0;
    let mut v___x_3683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_x3f_3685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: u8 = 0;
    let mut v___x_3690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3691_: u8 = 0;
    let mut v___x_3692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_3694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3696_: u8 = 0;
    let mut v___x_3697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3619_ = l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1;
                leanh::lean_inc(v_x_3566_);
                v___x_3620_ = l_Lean_Syntax_isOfKind(v_x_3566_, v___x_3619_);
                if v___x_3620_ == 0 {
                    leanh::lean_dec(v_x_3566_);
                    v___x_3621_ = leanh::lean_box(1);
                    v___x_3622_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3622_, 0, v___x_3621_);
                    leanh::lean_ctor_set(v___x_3622_, 1, v_a_3568_);
                    return v___x_3622_;
                } else {
                    v___x_3623_ = leanh::lean_unsigned_to_nat(0);
                    v___x_3688_ = l_Lean_Syntax_getArg(v_x_3566_, v___x_3623_);
                    v___x_3689_ = l_Lean_Syntax_isNone(v___x_3688_);
                    if v___x_3689_ == 0 {
                        v___x_3690_ = leanh::lean_unsigned_to_nat(1);
                        leanh::lean_inc(v___x_3688_);
                        v___x_3691_ = l_Lean_Syntax_matchesNull(v___x_3688_, v___x_3690_);
                        if v___x_3691_ == 0 {
                            leanh::lean_dec(v___x_3688_);
                            leanh::lean_dec(v_x_3566_);
                            v___x_3692_ = leanh::lean_box(1);
                            v___x_3693_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_3693_, 0, v___x_3692_);
                            leanh::lean_ctor_set(v___x_3693_, 1, v_a_3568_);
                            return v___x_3693_;
                        } else {
                            v_doc_x3f_3694_ = l_Lean_Syntax_getArg(v___x_3688_, v___x_3623_);
                            leanh::lean_dec(v___x_3688_);
                            v___x_3695_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__29;
                            leanh::lean_inc(v_doc_x3f_3694_);
                            v___x_3696_ = l_Lean_Syntax_isOfKind(v_doc_x3f_3694_, v___x_3695_);
                            if v___x_3696_ == 0 {
                                leanh::lean_dec(v_doc_x3f_3694_);
                                leanh::lean_dec(v_x_3566_);
                                v___x_3697_ = leanh::lean_box(1);
                                v___x_3698_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3698_, 0, v___x_3697_);
                                leanh::lean_ctor_set(v___x_3698_, 1, v_a_3568_);
                                return v___x_3698_;
                            } else {
                                v___x_3699_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_3699_, 0, v_doc_x3f_3694_);
                                v_doc_x3f_3670_ = v___x_3699_;
                                v___y_3671_ = v_a_3567_;
                                v___y_3672_ = v_a_3568_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v___x_3688_);
                        v___x_3700_ = leanh::lean_box(0);
                        v_doc_x3f_3670_ = v___x_3700_;
                        v___y_3671_ = v_a_3567_;
                        v___y_3672_ = v_a_3568_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref(v___y_3572_);
                v___x_3584_ = l_Array_append___redArg(v___y_3572_, v___y_3583_);
                leanh::lean_dec_ref(v___y_3583_);
                leanh::lean_inc(v___y_3574_);
                leanh::lean_inc_n(v___y_3573_, 2);
                v___x_3585_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3585_, 0, v___y_3573_);
                leanh::lean_ctor_set(v___x_3585_, 1, v___y_3574_);
                leanh::lean_ctor_set(v___x_3585_, 2, v___x_3584_);
                v___x_3586_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0;
                v___x_3587_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3587_, 0, v___y_3573_);
                leanh::lean_ctor_set(v___x_3587_, 1, v___x_3586_);
                leanh::lean_inc(v___y_3577_);
                v___x_3588_ = l___private_Init_Simproc_0__Lean_Parser_mkAttributeCmds(
                    v___y_3576_,
                    v___y_3571_,
                    v___y_3581_,
                    v___y_3577_,
                    v___y_3582_,
                    v___y_3578_,
                );
                leanh::lean_dec(v___y_3581_);
                if leanh::lean_obj_tag(v___x_3588_) == 0 {
                    v_a_3589_ = leanh::lean_ctor_get(v___x_3588_, 0);
                    v_a_3590_ = leanh::lean_ctor_get(v___x_3588_, 1);
                    v_isSharedCheck_3609_ = (!leanh::lean_is_exclusive(v___x_3588_)) as u8;
                    if v_isSharedCheck_3609_ == 0 {
                        v___x_3592_ = v___x_3588_;
                        v_isShared_3593_ = v_isSharedCheck_3609_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3590_);
                        leanh::lean_inc(v_a_3589_);
                        leanh::lean_dec(v___x_3588_);
                        v___x_3592_ = leanh::lean_box(0);
                        v_isShared_3593_ = v_isSharedCheck_3609_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref_known(v___x_3587_, 2);
                    leanh::lean_dec_ref_known(v___x_3585_, 3);
                    leanh::lean_dec(v___y_3577_);
                    leanh::lean_dec(v___y_3575_);
                    leanh::lean_dec(v___y_3573_);
                    leanh::lean_dec(v___y_3570_);
                    v_a_3610_ = leanh::lean_ctor_get(v___x_3588_, 0);
                    v_a_3611_ = leanh::lean_ctor_get(v___x_3588_, 1);
                    v_isSharedCheck_3618_ = (!leanh::lean_is_exclusive(v___x_3588_)) as u8;
                    if v_isSharedCheck_3618_ == 0 {
                        v___x_3613_ = v___x_3588_;
                        v_isShared_3614_ = v_isSharedCheck_3618_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3611_);
                        leanh::lean_inc(v_a_3610_);
                        leanh::lean_dec(v___x_3588_);
                        v___x_3613_ = leanh::lean_box(0);
                        v_isShared_3614_ = v_isSharedCheck_3618_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3594_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__1;
                leanh::lean_inc_n(v___y_3573_, 3);
                v___x_3595_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3595_, 0, v___y_3573_);
                leanh::lean_ctor_set(v___x_3595_, 1, v___x_3594_);
                v___x_3596_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__47;
                v___x_3597_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3597_, 0, v___y_3573_);
                leanh::lean_ctor_set(v___x_3597_, 1, v___x_3596_);
                v___x_3598_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__10;
                v___x_3599_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3599_, 0, v___y_3573_);
                leanh::lean_ctor_set(v___x_3599_, 1, v___x_3598_);
                leanh::lean_inc(v___y_3579_);
                v___x_3600_ = l_Lean_Syntax_node8(
                    v___y_3573_,
                    v___y_3579_,
                    v___x_3585_,
                    v___x_3587_,
                    v___y_3577_,
                    v___x_3595_,
                    v___y_3570_,
                    v___x_3597_,
                    v___x_3599_,
                    v___y_3575_,
                );
                v___x_3601_ = lean_mk_empty_array_with_capacity(v___y_3580_);
                v___x_3602_ = lean_array_push(v___x_3601_, v___x_3600_);
                v___x_3603_ = l_Array_append___redArg(v___x_3602_, v_a_3589_);
                leanh::lean_dec(v_a_3589_);
                v___x_3604_ = leanh::lean_box(2);
                leanh::lean_inc(v___y_3574_);
                v___x_3605_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3605_, 0, v___x_3604_);
                leanh::lean_ctor_set(v___x_3605_, 1, v___y_3574_);
                leanh::lean_ctor_set(v___x_3605_, 2, v___x_3603_);
                if v_isShared_3593_ == 0 {
                    leanh::lean_ctor_set(v___x_3592_, 0, v___x_3605_);
                    v___x_3607_ = v___x_3592_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3608_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3608_, 0, v___x_3605_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3608_, 1, v_a_3590_);
                    v___x_3607_ = v_reuseFailAlloc_3608_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3607_;
            }
            4 => {
                if v_isShared_3614_ == 0 {
                    v___x_3616_ = v___x_3613_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3617_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3617_, 0, v_a_3610_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3617_, 1, v_a_3611_);
                    v___x_3616_ = v_reuseFailAlloc_3617_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3616_;
            }
            6 => {
                v___x_3632_ = leanh::lean_unsigned_to_nat(5);
                v_n_3633_ = l_Lean_Syntax_getArg(v_x_3566_, v___x_3632_);
                v___x_3634_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__27;
                leanh::lean_inc(v_n_3633_);
                v___x_3635_ = l_Lean_Syntax_isOfKind(v_n_3633_, v___x_3634_);
                if v___x_3635_ == 0 {
                    leanh::lean_dec(v_n_3633_);
                    leanh::lean_dec(v_ids_x3f_3629_);
                    leanh::lean_dec(v___y_3628_);
                    leanh::lean_dec(v___y_3626_);
                    leanh::lean_dec(v___y_3625_);
                    leanh::lean_dec(v_x_3566_);
                    v___x_3636_ = leanh::lean_box(1);
                    v___x_3637_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3637_, 0, v___x_3636_);
                    leanh::lean_ctor_set(v___x_3637_, 1, v___y_3631_);
                    return v___x_3637_;
                } else {
                    v_ref_3638_ = leanh::lean_ctor_get(v___y_3630_, 5);
                    v___x_3639_ = leanh::lean_unsigned_to_nat(7);
                    v___x_3640_ = l_Lean_Syntax_getArg(v_x_3566_, v___x_3639_);
                    v___x_3641_ = leanh::lean_unsigned_to_nat(10);
                    v___x_3642_ = l_Lean_Syntax_getArg(v_x_3566_, v___x_3641_);
                    leanh::lean_dec(v_x_3566_);
                    v___x_3643_ = 0;
                    v___x_3644_ = l_Lean_SourceInfo_fromRef(v_ref_3638_, v___x_3643_);
                    v___x_3645_ =
                        l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__1;
                    v___x_3646_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__21;
                    v___x_3647_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27), core::ptr::addr_of_mut!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27_once), _init_l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27);
                    if leanh::lean_obj_tag(v___y_3628_) == 1 {
                        v_val_3648_ = leanh::lean_ctor_get(v___y_3628_, 0);
                        leanh::lean_inc(v_val_3648_);
                        leanh::lean_dec_ref_known(v___y_3628_, 1);
                        v___x_3649_ = l_Array_mkArray1___redArg(v_val_3648_);
                        v___y_3570_ = v___x_3640_;
                        v___y_3571_ = v___y_3626_;
                        v___y_3572_ = v___x_3647_;
                        v___y_3573_ = v___x_3644_;
                        v___y_3574_ = v___x_3646_;
                        v___y_3575_ = v___x_3642_;
                        v___y_3576_ = v___y_3625_;
                        v___y_3577_ = v_n_3633_;
                        v___y_3578_ = v___y_3631_;
                        v___y_3579_ = v___x_3645_;
                        v___y_3580_ = v___y_3627_;
                        v___y_3581_ = v_ids_x3f_3629_;
                        v___y_3582_ = v___y_3630_;
                        v___y_3583_ = v___x_3649_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___y_3628_);
                        v___x_3650_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__28;
                        v___y_3570_ = v___x_3640_;
                        v___y_3571_ = v___y_3626_;
                        v___y_3572_ = v___x_3647_;
                        v___y_3573_ = v___x_3644_;
                        v___y_3574_ = v___x_3646_;
                        v___y_3575_ = v___x_3642_;
                        v___y_3576_ = v___y_3625_;
                        v___y_3577_ = v_n_3633_;
                        v___y_3578_ = v___y_3631_;
                        v___y_3579_ = v___x_3645_;
                        v___y_3580_ = v___y_3627_;
                        v___y_3581_ = v_ids_x3f_3629_;
                        v___y_3582_ = v___y_3630_;
                        v___y_3583_ = v___x_3650_;
                        state = 1;
                        continue;
                    }
                }
            }
            7 => {
                v___x_3659_ = leanh::lean_unsigned_to_nat(4);
                v___x_3660_ = l_Lean_Syntax_getArg(v_x_3566_, v___x_3659_);
                v___x_3661_ = l_Lean_Syntax_isNone(v___x_3660_);
                if v___x_3661_ == 0 {
                    leanh::lean_inc(v___x_3660_);
                    v___x_3662_ = l_Lean_Syntax_matchesNull(v___x_3660_, v___y_3654_);
                    if v___x_3662_ == 0 {
                        leanh::lean_dec(v___x_3660_);
                        leanh::lean_dec(v_pre_x3f_3656_);
                        leanh::lean_dec(v___y_3655_);
                        leanh::lean_dec(v___y_3652_);
                        leanh::lean_dec(v_x_3566_);
                        v___x_3663_ = leanh::lean_box(1);
                        v___x_3664_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3664_, 0, v___x_3663_);
                        leanh::lean_ctor_set(v___x_3664_, 1, v___y_3658_);
                        return v___x_3664_;
                    } else {
                        v___x_3665_ = l_Lean_Syntax_getArg(v___x_3660_, v___y_3653_);
                        leanh::lean_dec(v___x_3660_);
                        v_ids_x3f_3666_ = l_Lean_Syntax_getArgs(v___x_3665_);
                        leanh::lean_dec(v___x_3665_);
                        v___x_3667_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3667_, 0, v_ids_x3f_3666_);
                        v___y_3625_ = v___y_3652_;
                        v___y_3626_ = v_pre_x3f_3656_;
                        v___y_3627_ = v___y_3653_;
                        v___y_3628_ = v___y_3655_;
                        v_ids_x3f_3629_ = v___x_3667_;
                        v___y_3630_ = v___y_3657_;
                        v___y_3631_ = v___y_3658_;
                        state = 6;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_3660_);
                    v___x_3668_ = leanh::lean_box(0);
                    v___y_3625_ = v___y_3652_;
                    v___y_3626_ = v_pre_x3f_3656_;
                    v___y_3627_ = v___y_3653_;
                    v___y_3628_ = v___y_3655_;
                    v_ids_x3f_3629_ = v___x_3668_;
                    v___y_3630_ = v___y_3657_;
                    v___y_3631_ = v___y_3658_;
                    state = 6;
                    continue;
                }
            }
            8 => {
                v___x_3673_ = leanh::lean_unsigned_to_nat(1);
                v_kind_3674_ = l_Lean_Syntax_getArg(v_x_3566_, v___x_3673_);
                v___x_3675_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__2;
                leanh::lean_inc(v_kind_3674_);
                v___x_3676_ = l_Lean_Syntax_isOfKind(v_kind_3674_, v___x_3675_);
                if v___x_3676_ == 0 {
                    leanh::lean_dec(v_kind_3674_);
                    leanh::lean_dec(v_doc_x3f_3670_);
                    leanh::lean_dec(v_x_3566_);
                    v___x_3677_ = leanh::lean_box(1);
                    v___x_3678_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3678_, 0, v___x_3677_);
                    leanh::lean_ctor_set(v___x_3678_, 1, v___y_3672_);
                    return v___x_3678_;
                } else {
                    v___x_3679_ = leanh::lean_unsigned_to_nat(3);
                    v___x_3680_ = l_Lean_Syntax_getArg(v_x_3566_, v___x_3679_);
                    v___x_3681_ = l_Lean_Syntax_isNone(v___x_3680_);
                    if v___x_3681_ == 0 {
                        leanh::lean_inc(v___x_3680_);
                        v___x_3682_ = l_Lean_Syntax_matchesNull(v___x_3680_, v___x_3673_);
                        if v___x_3682_ == 0 {
                            leanh::lean_dec(v___x_3680_);
                            leanh::lean_dec(v_kind_3674_);
                            leanh::lean_dec(v_doc_x3f_3670_);
                            leanh::lean_dec(v_x_3566_);
                            v___x_3683_ = leanh::lean_box(1);
                            v___x_3684_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_3684_, 0, v___x_3683_);
                            leanh::lean_ctor_set(v___x_3684_, 1, v___y_3672_);
                            return v___x_3684_;
                        } else {
                            v_pre_x3f_3685_ = l_Lean_Syntax_getArg(v___x_3680_, v___x_3623_);
                            leanh::lean_dec(v___x_3680_);
                            v___x_3686_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_3686_, 0, v_pre_x3f_3685_);
                            v___y_3652_ = v_kind_3674_;
                            v___y_3653_ = v___x_3673_;
                            v___y_3654_ = v___x_3679_;
                            v___y_3655_ = v_doc_x3f_3670_;
                            v_pre_x3f_3656_ = v___x_3686_;
                            v___y_3657_ = v___y_3671_;
                            v___y_3658_ = v___y_3672_;
                            state = 7;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_3680_);
                        v___x_3687_ = leanh::lean_box(0);
                        v___y_3652_ = v_kind_3674_;
                        v___y_3653_ = v___x_3673_;
                        v___y_3654_ = v___x_3679_;
                        v___y_3655_ = v_doc_x3f_3670_;
                        v_pre_x3f_3656_ = v___x_3687_;
                        v___y_3657_ = v___y_3671_;
                        v___y_3658_ = v___y_3672_;
                        state = 7;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d____1___boxed(
    mut v_x_3701_: *mut leanh::LeanObject,
    mut v_a_3702_: *mut leanh::LeanObject,
    mut v_a_3703_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3704_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3704_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d____1(v_x_3701_, v_a_3702_, v_a_3703_);
    leanh::lean_dec_ref(v_a_3702_);
    return v_res_3704_;
}
pub unsafe fn l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1(
    mut v_x_3706_: *mut leanh::LeanObject,
    mut v_a_3707_: *mut leanh::LeanObject,
    mut v_a_3708_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3799_: u8 = 0;
    let mut v___x_3800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_x3f_3922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: u8 = 0;
    let mut v___x_3928_: u8 = 0;
    let mut v___x_3929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3932_: u8 = 0;
    let mut v___x_3933_: u8 = 0;
    let mut v___x_3934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3938_: u8 = 0;
    let mut v___x_3939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3943_: u8 = 0;
    let mut v___x_3944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: u8 = 0;
    let mut v___x_3950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3966_: u8 = 0;
    let mut v___x_3967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3972_: u8 = 0;
    let mut v___x_3973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3990_: u8 = 0;
    let mut v___x_3991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: u8 = 0;
    let mut v___x_3999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_4007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4014_: u8 = 0;
    let mut v___x_4015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4020_: u8 = 0;
    let mut v___x_4021_: u8 = 0;
    let mut v___x_4022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_x3f_4024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4028_: u8 = 0;
    let mut v___x_4029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: u8 = 0;
    let mut v___x_4031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_4033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4035_: u8 = 0;
    let mut v___x_4036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3761_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0;
                v___x_3762_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1;
                v___x_3798_ = l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1;
                leanh::lean_inc(v_x_3706_);
                v___x_3799_ = l_Lean_Syntax_isOfKind(v_x_3706_, v___x_3798_);
                if v___x_3799_ == 0 {
                    leanh::lean_dec(v_x_3706_);
                    v___x_3800_ = leanh::lean_box(1);
                    v___x_3801_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3801_, 0, v___x_3800_);
                    leanh::lean_ctor_set(v___x_3801_, 1, v_a_3708_);
                    return v___x_3801_;
                } else {
                    v___x_3802_ = leanh::lean_unsigned_to_nat(0);
                    v___x_4027_ = l_Lean_Syntax_getArg(v_x_3706_, v___x_3802_);
                    v___x_4028_ = l_Lean_Syntax_isNone(v___x_4027_);
                    if v___x_4028_ == 0 {
                        v___x_4029_ = leanh::lean_unsigned_to_nat(1);
                        leanh::lean_inc(v___x_4027_);
                        v___x_4030_ = l_Lean_Syntax_matchesNull(v___x_4027_, v___x_4029_);
                        if v___x_4030_ == 0 {
                            leanh::lean_dec(v___x_4027_);
                            leanh::lean_dec(v_x_3706_);
                            v___x_4031_ = leanh::lean_box(1);
                            v___x_4032_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_4032_, 0, v___x_4031_);
                            leanh::lean_ctor_set(v___x_4032_, 1, v_a_3708_);
                            return v___x_4032_;
                        } else {
                            v_doc_x3f_4033_ = l_Lean_Syntax_getArg(v___x_4027_, v___x_3802_);
                            leanh::lean_dec(v___x_4027_);
                            v___x_4034_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__29;
                            leanh::lean_inc(v_doc_x3f_4033_);
                            v___x_4035_ = l_Lean_Syntax_isOfKind(v_doc_x3f_4033_, v___x_4034_);
                            if v___x_4035_ == 0 {
                                leanh::lean_dec(v_doc_x3f_4033_);
                                leanh::lean_dec(v_x_3706_);
                                v___x_4036_ = leanh::lean_box(1);
                                v___x_4037_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_4037_, 0, v___x_4036_);
                                leanh::lean_ctor_set(v___x_4037_, 1, v_a_3708_);
                                return v___x_4037_;
                            } else {
                                v___x_4038_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_4038_, 0, v_doc_x3f_4033_);
                                v_doc_x3f_4007_ = v___x_4038_;
                                v___y_4008_ = v_a_3707_;
                                v___y_4009_ = v_a_3708_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v___x_4027_);
                        v___x_4039_ = leanh::lean_box(0);
                        v_doc_x3f_4007_ = v___x_4039_;
                        v___y_4008_ = v_a_3707_;
                        v___y_4009_ = v_a_3708_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref(v___y_3721_);
                v___x_3724_ = l_Array_append___redArg(v___y_3721_, v___y_3723_);
                leanh::lean_dec_ref(v___y_3723_);
                leanh::lean_inc_n(v___y_3712_, 4);
                leanh::lean_inc_n(v___y_3719_, 7);
                v___x_3725_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3725_, 0, v___y_3719_);
                leanh::lean_ctor_set(v___x_3725_, 1, v___y_3712_);
                leanh::lean_ctor_set(v___x_3725_, 2, v___x_3724_);
                leanh::lean_inc(v___y_3715_);
                v___x_3726_ =
                    l_Lean_Syntax_node2(v___y_3719_, v___y_3715_, v___y_3718_, v___x_3725_);
                v___x_3727_ =
                    l_Lean_Syntax_node2(v___y_3719_, v___y_3713_, v___y_3710_, v___x_3726_);
                v___x_3728_ = l_Lean_Syntax_node1(v___y_3719_, v___y_3712_, v___x_3727_);
                v___x_3729_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__34;
                v___x_3730_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3730_, 0, v___y_3719_);
                leanh::lean_ctor_set(v___x_3730_, 1, v___x_3729_);
                v___x_3731_ = l_Lean_Syntax_node1(v___y_3719_, v___y_3712_, v___y_3717_);
                leanh::lean_inc(v___y_3711_);
                v___x_3732_ = l_Lean_Syntax_node5(
                    v___y_3719_,
                    v___y_3711_,
                    v___y_3714_,
                    v___y_3720_,
                    v___x_3728_,
                    v___x_3730_,
                    v___x_3731_,
                );
                v___x_3733_ =
                    l_Lean_Syntax_node2(v___y_3719_, v___y_3712_, v___y_3722_, v___x_3732_);
                v___x_3734_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3734_, 0, v___x_3733_);
                leanh::lean_ctor_set(v___x_3734_, 1, v___y_3716_);
                return v___x_3734_;
            }
            2 => {
                leanh::lean_inc_ref(v___y_3748_);
                v___x_3750_ = l_Array_append___redArg(v___y_3748_, v___y_3749_);
                leanh::lean_dec_ref(v___y_3749_);
                leanh::lean_inc_n(v___y_3740_, 4);
                leanh::lean_inc_n(v___y_3744_, 7);
                v___x_3751_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3751_, 0, v___y_3744_);
                leanh::lean_ctor_set(v___x_3751_, 1, v___y_3740_);
                leanh::lean_ctor_set(v___x_3751_, 2, v___x_3750_);
                leanh::lean_inc(v___y_3738_);
                v___x_3752_ =
                    l_Lean_Syntax_node2(v___y_3744_, v___y_3738_, v___y_3739_, v___x_3751_);
                v___x_3753_ =
                    l_Lean_Syntax_node2(v___y_3744_, v___y_3742_, v___y_3736_, v___x_3752_);
                v___x_3754_ = l_Lean_Syntax_node1(v___y_3744_, v___y_3740_, v___x_3753_);
                v___x_3755_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__34;
                v___x_3756_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3756_, 0, v___y_3744_);
                leanh::lean_ctor_set(v___x_3756_, 1, v___x_3755_);
                v___x_3757_ = l_Lean_Syntax_node1(v___y_3744_, v___y_3740_, v___y_3745_);
                leanh::lean_inc(v___y_3746_);
                v___x_3758_ = l_Lean_Syntax_node5(
                    v___y_3744_,
                    v___y_3746_,
                    v___y_3737_,
                    v___y_3747_,
                    v___x_3754_,
                    v___x_3756_,
                    v___x_3757_,
                );
                v___x_3759_ =
                    l_Lean_Syntax_node2(v___y_3744_, v___y_3740_, v___y_3743_, v___x_3758_);
                v___x_3760_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3760_, 0, v___x_3759_);
                leanh::lean_ctor_set(v___x_3760_, 1, v___y_3741_);
                return v___x_3760_;
            }
            3 => {
                leanh::lean_inc_ref(v___y_3768_);
                v___x_3779_ = l_Array_append___redArg(v___y_3768_, v___y_3778_);
                leanh::lean_dec_ref(v___y_3778_);
                leanh::lean_inc_n(v___y_3767_, 5);
                leanh::lean_inc_n(v___y_3765_, 12);
                v___x_3780_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3780_, 0, v___y_3765_);
                leanh::lean_ctor_set(v___x_3780_, 1, v___y_3767_);
                leanh::lean_ctor_set(v___x_3780_, 2, v___x_3779_);
                leanh::lean_inc_ref(v___x_3780_);
                leanh::lean_inc(v___y_3770_);
                v___x_3781_ =
                    l_Lean_Syntax_node2(v___y_3765_, v___y_3770_, v___y_3766_, v___x_3780_);
                leanh::lean_inc(v___y_3764_);
                leanh::lean_inc(v___y_3769_);
                v___x_3782_ =
                    l_Lean_Syntax_node2(v___y_3765_, v___y_3769_, v___y_3764_, v___x_3781_);
                v___x_3783_ = l_Lean_Syntax_node1(v___y_3765_, v___y_3767_, v___x_3782_);
                v___x_3784_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__34;
                v___x_3785_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3785_, 0, v___y_3765_);
                leanh::lean_ctor_set(v___x_3785_, 1, v___x_3784_);
                v___x_3786_ = l_Lean_Syntax_node1(v___y_3765_, v___y_3767_, v___y_3773_);
                leanh::lean_inc(v___x_3786_);
                leanh::lean_inc_ref(v___x_3785_);
                leanh::lean_inc(v___y_3776_);
                leanh::lean_inc(v___y_3777_);
                leanh::lean_inc_n(v___y_3775_, 2);
                v___x_3787_ = l_Lean_Syntax_node5(
                    v___y_3765_,
                    v___y_3775_,
                    v___y_3777_,
                    v___y_3776_,
                    v___x_3783_,
                    v___x_3785_,
                    v___x_3786_,
                );
                v___x_3788_ = l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__0;
                leanh::lean_inc_ref(v___y_3771_);
                v___x_3789_ =
                    l_Lean_Name_mkStr4(v___x_3761_, v___x_3762_, v___y_3771_, v___x_3788_);
                v___x_3790_ = l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__2;
                v___x_3791_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3791_, 0, v___y_3765_);
                leanh::lean_ctor_set(v___x_3791_, 1, v___x_3790_);
                v___x_3792_ =
                    l_Lean_Syntax_node2(v___y_3765_, v___x_3789_, v___x_3791_, v___x_3780_);
                v___x_3793_ =
                    l_Lean_Syntax_node2(v___y_3765_, v___y_3769_, v___y_3764_, v___x_3792_);
                v___x_3794_ = l_Lean_Syntax_node1(v___y_3765_, v___y_3767_, v___x_3793_);
                v___x_3795_ = l_Lean_Syntax_node5(
                    v___y_3765_,
                    v___y_3775_,
                    v___y_3777_,
                    v___y_3776_,
                    v___x_3794_,
                    v___x_3785_,
                    v___x_3786_,
                );
                v___x_3796_ = l_Lean_Syntax_node3(
                    v___y_3765_,
                    v___y_3767_,
                    v___y_3772_,
                    v___x_3787_,
                    v___x_3795_,
                );
                v___x_3797_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3797_, 0, v___x_3796_);
                leanh::lean_ctor_set(v___x_3797_, 1, v___y_3774_);
                return v___x_3797_;
            }
            4 => {
                leanh::lean_inc_ref(v___y_3812_);
                v___x_3816_ = l_Array_append___redArg(v___y_3812_, v___y_3815_);
                leanh::lean_dec_ref(v___y_3815_);
                leanh::lean_inc(v___y_3811_);
                leanh::lean_inc_n(v___y_3810_, 9);
                v___x_3817_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3817_, 0, v___y_3810_);
                leanh::lean_ctor_set(v___x_3817_, 1, v___y_3811_);
                leanh::lean_ctor_set(v___x_3817_, 2, v___x_3816_);
                v___x_3818_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0;
                v___x_3819_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3819_, 0, v___y_3810_);
                leanh::lean_ctor_set(v___x_3819_, 1, v___x_3818_);
                v___x_3820_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__1;
                v___x_3821_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3821_, 0, v___y_3810_);
                leanh::lean_ctor_set(v___x_3821_, 1, v___x_3820_);
                v___x_3822_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__47;
                v___x_3823_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3823_, 0, v___y_3810_);
                leanh::lean_ctor_set(v___x_3823_, 1, v___x_3822_);
                v___x_3824_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__10;
                v___x_3825_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3825_, 0, v___y_3810_);
                leanh::lean_ctor_set(v___x_3825_, 1, v___x_3824_);
                leanh::lean_inc(v___y_3806_);
                leanh::lean_inc(v___y_3814_);
                v___x_3826_ = l_Lean_Syntax_node8(
                    v___y_3810_,
                    v___y_3814_,
                    v___x_3817_,
                    v___x_3819_,
                    v___y_3806_,
                    v___x_3821_,
                    v___y_3809_,
                    v___x_3823_,
                    v___x_3825_,
                    v___y_3804_,
                );
                v___x_3827_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__0;
                v___x_3828_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__1;
                v___x_3829_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3829_, 0, v___y_3810_);
                leanh::lean_ctor_set(v___x_3829_, 1, v___x_3827_);
                v___x_3830_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__24;
                v___x_3831_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3831_, 0, v___y_3810_);
                leanh::lean_ctor_set(v___x_3831_, 1, v___x_3830_);
                v___x_3832_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__2;
                leanh::lean_inc_ref(v___y_3808_);
                v___x_3833_ =
                    l_Lean_Name_mkStr4(v___x_3761_, v___x_3762_, v___y_3808_, v___x_3832_);
                v___x_3834_ = l_Lean_Parser_Attr_simprocAttr___closed__0;
                v___x_3835_ = l_Lean_Parser_Attr_simprocBuiltinAttr___closed__1;
                v___x_3836_ = l_Lean_Parser_Attr_simprocBuiltinAttr___closed__2;
                v___x_3837_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3837_, 0, v___y_3810_);
                leanh::lean_ctor_set(v___x_3837_, 1, v___x_3836_);
                if leanh::lean_obj_tag(v___y_3813_) == 1 {
                    v_val_3838_ = leanh::lean_ctor_get(v___y_3813_, 0);
                    leanh::lean_inc(v_val_3838_);
                    leanh::lean_dec_ref_known(v___y_3813_, 1);
                    v___x_3839_ = l_Array_mkArray1___redArg(v_val_3838_);
                    v___y_3764_ = v___y_3805_;
                    v___y_3765_ = v___y_3810_;
                    v___y_3766_ = v___x_3837_;
                    v___y_3767_ = v___y_3811_;
                    v___y_3768_ = v___y_3812_;
                    v___y_3769_ = v___x_3833_;
                    v___y_3770_ = v___x_3835_;
                    v___y_3771_ = v___x_3834_;
                    v___y_3772_ = v___x_3826_;
                    v___y_3773_ = v___y_3806_;
                    v___y_3774_ = v___y_3807_;
                    v___y_3775_ = v___x_3828_;
                    v___y_3776_ = v___x_3831_;
                    v___y_3777_ = v___x_3829_;
                    v___y_3778_ = v___x_3839_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_dec(v___y_3813_);
                    v___x_3840_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__28;
                    v___y_3764_ = v___y_3805_;
                    v___y_3765_ = v___y_3810_;
                    v___y_3766_ = v___x_3837_;
                    v___y_3767_ = v___y_3811_;
                    v___y_3768_ = v___y_3812_;
                    v___y_3769_ = v___x_3833_;
                    v___y_3770_ = v___x_3835_;
                    v___y_3771_ = v___x_3834_;
                    v___y_3772_ = v___x_3826_;
                    v___y_3773_ = v___y_3806_;
                    v___y_3774_ = v___y_3807_;
                    v___y_3775_ = v___x_3828_;
                    v___y_3776_ = v___x_3831_;
                    v___y_3777_ = v___x_3829_;
                    v___y_3778_ = v___x_3840_;
                    state = 3;
                    continue;
                }
            }
            5 => {
                leanh::lean_inc_ref(v___y_3849_);
                v___x_3854_ = l_Array_append___redArg(v___y_3849_, v___y_3853_);
                leanh::lean_dec_ref(v___y_3853_);
                leanh::lean_inc(v___y_3845_);
                leanh::lean_inc_n(v___y_3848_, 9);
                v___x_3855_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3855_, 0, v___y_3848_);
                leanh::lean_ctor_set(v___x_3855_, 1, v___y_3845_);
                leanh::lean_ctor_set(v___x_3855_, 2, v___x_3854_);
                v___x_3856_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0;
                v___x_3857_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3857_, 0, v___y_3848_);
                leanh::lean_ctor_set(v___x_3857_, 1, v___x_3856_);
                v___x_3858_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__1;
                v___x_3859_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3859_, 0, v___y_3848_);
                leanh::lean_ctor_set(v___x_3859_, 1, v___x_3858_);
                v___x_3860_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__47;
                v___x_3861_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3861_, 0, v___y_3848_);
                leanh::lean_ctor_set(v___x_3861_, 1, v___x_3860_);
                v___x_3862_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__10;
                v___x_3863_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3863_, 0, v___y_3848_);
                leanh::lean_ctor_set(v___x_3863_, 1, v___x_3862_);
                leanh::lean_inc(v___y_3846_);
                leanh::lean_inc(v___y_3850_);
                v___x_3864_ = l_Lean_Syntax_node8(
                    v___y_3848_,
                    v___y_3850_,
                    v___x_3855_,
                    v___x_3857_,
                    v___y_3846_,
                    v___x_3859_,
                    v___y_3847_,
                    v___x_3861_,
                    v___x_3863_,
                    v___y_3851_,
                );
                v___x_3865_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__0;
                v___x_3866_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__1;
                v___x_3867_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3867_, 0, v___y_3848_);
                leanh::lean_ctor_set(v___x_3867_, 1, v___x_3865_);
                v___x_3868_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__24;
                v___x_3869_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3869_, 0, v___y_3848_);
                leanh::lean_ctor_set(v___x_3869_, 1, v___x_3868_);
                v___x_3870_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__2;
                leanh::lean_inc_ref(v___y_3844_);
                v___x_3871_ =
                    l_Lean_Name_mkStr4(v___x_3761_, v___x_3762_, v___y_3844_, v___x_3870_);
                v___x_3872_ = l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__1;
                v___x_3873_ = l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__2;
                v___x_3874_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3874_, 0, v___y_3848_);
                leanh::lean_ctor_set(v___x_3874_, 1, v___x_3873_);
                if leanh::lean_obj_tag(v___y_3852_) == 1 {
                    v_val_3875_ = leanh::lean_ctor_get(v___y_3852_, 0);
                    leanh::lean_inc(v_val_3875_);
                    leanh::lean_dec_ref_known(v___y_3852_, 1);
                    v___x_3876_ = l_Array_mkArray1___redArg(v_val_3875_);
                    v___y_3710_ = v___y_3842_;
                    v___y_3711_ = v___x_3866_;
                    v___y_3712_ = v___y_3845_;
                    v___y_3713_ = v___x_3871_;
                    v___y_3714_ = v___x_3867_;
                    v___y_3715_ = v___x_3872_;
                    v___y_3716_ = v___y_3843_;
                    v___y_3717_ = v___y_3846_;
                    v___y_3718_ = v___x_3874_;
                    v___y_3719_ = v___y_3848_;
                    v___y_3720_ = v___x_3869_;
                    v___y_3721_ = v___y_3849_;
                    v___y_3722_ = v___x_3864_;
                    v___y_3723_ = v___x_3876_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v___y_3852_);
                    v___x_3877_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__28;
                    v___y_3710_ = v___y_3842_;
                    v___y_3711_ = v___x_3866_;
                    v___y_3712_ = v___y_3845_;
                    v___y_3713_ = v___x_3871_;
                    v___y_3714_ = v___x_3867_;
                    v___y_3715_ = v___x_3872_;
                    v___y_3716_ = v___y_3843_;
                    v___y_3717_ = v___y_3846_;
                    v___y_3718_ = v___x_3874_;
                    v___y_3719_ = v___y_3848_;
                    v___y_3720_ = v___x_3869_;
                    v___y_3721_ = v___y_3849_;
                    v___y_3722_ = v___x_3864_;
                    v___y_3723_ = v___x_3877_;
                    state = 1;
                    continue;
                }
            }
            6 => {
                leanh::lean_inc_ref(v___y_3889_);
                v___x_3891_ = l_Array_append___redArg(v___y_3889_, v___y_3890_);
                leanh::lean_dec_ref(v___y_3890_);
                leanh::lean_inc(v___y_3882_);
                leanh::lean_inc_n(v___y_3883_, 9);
                v___x_3892_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3892_, 0, v___y_3883_);
                leanh::lean_ctor_set(v___x_3892_, 1, v___y_3882_);
                leanh::lean_ctor_set(v___x_3892_, 2, v___x_3891_);
                v___x_3893_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0;
                v___x_3894_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3894_, 0, v___y_3883_);
                leanh::lean_ctor_set(v___x_3894_, 1, v___x_3893_);
                v___x_3895_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__1;
                v___x_3896_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3896_, 0, v___y_3883_);
                leanh::lean_ctor_set(v___x_3896_, 1, v___x_3895_);
                v___x_3897_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__47;
                v___x_3898_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3898_, 0, v___y_3883_);
                leanh::lean_ctor_set(v___x_3898_, 1, v___x_3897_);
                v___x_3899_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__10;
                v___x_3900_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3900_, 0, v___y_3883_);
                leanh::lean_ctor_set(v___x_3900_, 1, v___x_3899_);
                leanh::lean_inc(v___y_3884_);
                leanh::lean_inc(v___y_3885_);
                v___x_3901_ = l_Lean_Syntax_node8(
                    v___y_3883_,
                    v___y_3885_,
                    v___x_3892_,
                    v___x_3894_,
                    v___y_3884_,
                    v___x_3896_,
                    v___y_3888_,
                    v___x_3898_,
                    v___x_3900_,
                    v___y_3887_,
                );
                v___x_3902_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__0;
                v___x_3903_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__1;
                v___x_3904_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3904_, 0, v___y_3883_);
                leanh::lean_ctor_set(v___x_3904_, 1, v___x_3902_);
                v___x_3905_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__24;
                v___x_3906_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3906_, 0, v___y_3883_);
                leanh::lean_ctor_set(v___x_3906_, 1, v___x_3905_);
                v___x_3907_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__2;
                leanh::lean_inc_ref(v___y_3881_);
                v___x_3908_ =
                    l_Lean_Name_mkStr4(v___x_3761_, v___x_3762_, v___y_3881_, v___x_3907_);
                v___x_3909_ = l_Lean_Parser_Attr_simprocBuiltinAttr___closed__1;
                v___x_3910_ = l_Lean_Parser_Attr_simprocBuiltinAttr___closed__2;
                v___x_3911_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3911_, 0, v___y_3883_);
                leanh::lean_ctor_set(v___x_3911_, 1, v___x_3910_);
                if leanh::lean_obj_tag(v___y_3886_) == 1 {
                    v_val_3912_ = leanh::lean_ctor_get(v___y_3886_, 0);
                    leanh::lean_inc(v_val_3912_);
                    leanh::lean_dec_ref_known(v___y_3886_, 1);
                    v___x_3913_ = l_Array_mkArray1___redArg(v_val_3912_);
                    v___y_3736_ = v___y_3879_;
                    v___y_3737_ = v___x_3904_;
                    v___y_3738_ = v___x_3909_;
                    v___y_3739_ = v___x_3911_;
                    v___y_3740_ = v___y_3882_;
                    v___y_3741_ = v___y_3880_;
                    v___y_3742_ = v___x_3908_;
                    v___y_3743_ = v___x_3901_;
                    v___y_3744_ = v___y_3883_;
                    v___y_3745_ = v___y_3884_;
                    v___y_3746_ = v___x_3903_;
                    v___y_3747_ = v___x_3906_;
                    v___y_3748_ = v___y_3889_;
                    v___y_3749_ = v___x_3913_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v___y_3886_);
                    v___x_3914_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__28;
                    v___y_3736_ = v___y_3879_;
                    v___y_3737_ = v___x_3904_;
                    v___y_3738_ = v___x_3909_;
                    v___y_3739_ = v___x_3911_;
                    v___y_3740_ = v___y_3882_;
                    v___y_3741_ = v___y_3880_;
                    v___y_3742_ = v___x_3908_;
                    v___y_3743_ = v___x_3901_;
                    v___y_3744_ = v___y_3883_;
                    v___y_3745_ = v___y_3884_;
                    v___y_3746_ = v___x_3903_;
                    v___y_3747_ = v___x_3906_;
                    v___y_3748_ = v___y_3889_;
                    v___y_3749_ = v___x_3914_;
                    state = 2;
                    continue;
                }
            }
            7 => {
                v___x_3925_ = leanh::lean_unsigned_to_nat(4);
                v___x_3926_ = l_Lean_Syntax_getArg(v_x_3706_, v___x_3925_);
                leanh::lean_inc(v___x_3926_);
                v___x_3927_ = l_Lean_Syntax_matchesNull(v___x_3926_, v___x_3802_);
                if v___x_3927_ == 0 {
                    leanh::lean_inc(v___x_3926_);
                    v___x_3928_ = l_Lean_Syntax_matchesNull(v___x_3926_, v___y_3921_);
                    if v___x_3928_ == 0 {
                        leanh::lean_dec(v___x_3926_);
                        leanh::lean_dec(v_pre_x3f_3922_);
                        leanh::lean_dec(v___y_3920_);
                        leanh::lean_dec(v___y_3916_);
                        leanh::lean_dec(v_x_3706_);
                        v___x_3929_ = leanh::lean_box(1);
                        v___x_3930_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3930_, 0, v___x_3929_);
                        leanh::lean_ctor_set(v___x_3930_, 1, v___y_3924_);
                        return v___x_3930_;
                    } else {
                        v___x_3931_ = l_Lean_Syntax_getArg(v___x_3926_, v___y_3919_);
                        leanh::lean_dec(v___x_3926_);
                        leanh::lean_inc(v___x_3931_);
                        v___x_3932_ = l_Lean_Syntax_matchesNull(v___x_3931_, v___y_3919_);
                        if v___x_3932_ == 0 {
                            leanh::lean_inc(v___x_3931_);
                            v___x_3933_ = l_Lean_Syntax_matchesNull(v___x_3931_, v___y_3921_);
                            if v___x_3933_ == 0 {
                                leanh::lean_dec(v___x_3931_);
                                leanh::lean_dec(v_pre_x3f_3922_);
                                leanh::lean_dec(v___y_3920_);
                                leanh::lean_dec(v___y_3916_);
                                leanh::lean_dec(v_x_3706_);
                                v___x_3934_ = leanh::lean_box(1);
                                v___x_3935_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3935_, 0, v___x_3934_);
                                leanh::lean_ctor_set(v___x_3935_, 1, v___y_3924_);
                                return v___x_3935_;
                            } else {
                                v___x_3936_ = l_Lean_Syntax_getArg(v___x_3931_, v___x_3802_);
                                v___x_3937_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__5;
                                v___x_3938_ = l_Lean_Syntax_matchesIdent(v___x_3936_, v___x_3937_);
                                leanh::lean_dec(v___x_3936_);
                                if v___x_3938_ == 0 {
                                    leanh::lean_dec(v___x_3931_);
                                    leanh::lean_dec(v_pre_x3f_3922_);
                                    leanh::lean_dec(v___y_3920_);
                                    leanh::lean_dec(v___y_3916_);
                                    leanh::lean_dec(v_x_3706_);
                                    v___x_3939_ = leanh::lean_box(1);
                                    v___x_3940_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_3940_, 0, v___x_3939_);
                                    leanh::lean_ctor_set(v___x_3940_, 1, v___y_3924_);
                                    return v___x_3940_;
                                } else {
                                    v___x_3941_ = l_Lean_Syntax_getArg(v___x_3931_, v___y_3917_);
                                    leanh::lean_dec(v___x_3931_);
                                    v___x_3942_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__7;
                                    v___x_3943_ =
                                        l_Lean_Syntax_matchesIdent(v___x_3941_, v___x_3942_);
                                    leanh::lean_dec(v___x_3941_);
                                    if v___x_3943_ == 0 {
                                        leanh::lean_dec(v_pre_x3f_3922_);
                                        leanh::lean_dec(v___y_3920_);
                                        leanh::lean_dec(v___y_3916_);
                                        leanh::lean_dec(v_x_3706_);
                                        v___x_3944_ = leanh::lean_box(1);
                                        v___x_3945_ =
                                            leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                        leanh::lean_ctor_set(v___x_3945_, 0, v___x_3944_);
                                        leanh::lean_ctor_set(v___x_3945_, 1, v___y_3924_);
                                        return v___x_3945_;
                                    } else {
                                        v___x_3946_ = leanh::lean_unsigned_to_nat(5);
                                        v___x_3947_ = l_Lean_Syntax_getArg(v_x_3706_, v___x_3946_);
                                        v___x_3948_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__27;
                                        leanh::lean_inc(v___x_3947_);
                                        v___x_3949_ =
                                            l_Lean_Syntax_isOfKind(v___x_3947_, v___x_3948_);
                                        if v___x_3949_ == 0 {
                                            leanh::lean_dec(v___x_3947_);
                                            leanh::lean_dec(v_pre_x3f_3922_);
                                            leanh::lean_dec(v___y_3920_);
                                            leanh::lean_dec(v___y_3916_);
                                            leanh::lean_dec(v_x_3706_);
                                            v___x_3950_ = leanh::lean_box(1);
                                            v___x_3951_ =
                                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                            leanh::lean_ctor_set(
                                                v___x_3951_,
                                                0,
                                                v___x_3950_,
                                            );
                                            leanh::lean_ctor_set(
                                                v___x_3951_,
                                                1,
                                                v___y_3924_,
                                            );
                                            return v___x_3951_;
                                        } else {
                                            v_ref_3952_ =
                                                leanh::lean_ctor_get(v___y_3923_, 5);
                                            v___x_3953_ = leanh::lean_unsigned_to_nat(7);
                                            v___x_3954_ =
                                                l_Lean_Syntax_getArg(v_x_3706_, v___x_3953_);
                                            v___x_3955_ = leanh::lean_unsigned_to_nat(10);
                                            v___x_3956_ =
                                                l_Lean_Syntax_getArg(v_x_3706_, v___x_3955_);
                                            leanh::lean_dec(v_x_3706_);
                                            v___x_3957_ =
                                                l_Lean_SourceInfo_fromRef(v_ref_3952_, v___x_3932_);
                                            v___x_3958_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__21;
                                            v___x_3959_ = l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__1;
                                            v___x_3960_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27), core::ptr::addr_of_mut!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27_once), _init_l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27);
                                            if leanh::lean_obj_tag(v___y_3920_) == 1 {
                                                v_val_3961_ =
                                                    leanh::lean_ctor_get(v___y_3920_, 0);
                                                leanh::lean_inc(v_val_3961_);
                                                leanh::lean_dec_ref_known(v___y_3920_, 1);
                                                v___x_3962_ =
                                                    l_Array_mkArray1___redArg(v_val_3961_);
                                                v___y_3804_ = v___x_3956_;
                                                v___y_3805_ = v___y_3916_;
                                                v___y_3806_ = v___x_3947_;
                                                v___y_3807_ = v___y_3924_;
                                                v___y_3808_ = v___y_3918_;
                                                v___y_3809_ = v___x_3954_;
                                                v___y_3810_ = v___x_3957_;
                                                v___y_3811_ = v___x_3958_;
                                                v___y_3812_ = v___x_3960_;
                                                v___y_3813_ = v_pre_x3f_3922_;
                                                v___y_3814_ = v___x_3959_;
                                                v___y_3815_ = v___x_3962_;
                                                state = 4;
                                                continue;
                                            } else {
                                                leanh::lean_dec(v___y_3920_);
                                                v___x_3963_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__28;
                                                v___y_3804_ = v___x_3956_;
                                                v___y_3805_ = v___y_3916_;
                                                v___y_3806_ = v___x_3947_;
                                                v___y_3807_ = v___y_3924_;
                                                v___y_3808_ = v___y_3918_;
                                                v___y_3809_ = v___x_3954_;
                                                v___y_3810_ = v___x_3957_;
                                                v___y_3811_ = v___x_3958_;
                                                v___y_3812_ = v___x_3960_;
                                                v___y_3813_ = v_pre_x3f_3922_;
                                                v___y_3814_ = v___x_3959_;
                                                v___y_3815_ = v___x_3963_;
                                                state = 4;
                                                continue;
                                            }
                                        }
                                    }
                                }
                            }
                        } else {
                            v___x_3964_ = l_Lean_Syntax_getArg(v___x_3931_, v___x_3802_);
                            leanh::lean_dec(v___x_3931_);
                            v___x_3965_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__7;
                            v___x_3966_ = l_Lean_Syntax_matchesIdent(v___x_3964_, v___x_3965_);
                            leanh::lean_dec(v___x_3964_);
                            if v___x_3966_ == 0 {
                                leanh::lean_dec(v_pre_x3f_3922_);
                                leanh::lean_dec(v___y_3920_);
                                leanh::lean_dec(v___y_3916_);
                                leanh::lean_dec(v_x_3706_);
                                v___x_3967_ = leanh::lean_box(1);
                                v___x_3968_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3968_, 0, v___x_3967_);
                                leanh::lean_ctor_set(v___x_3968_, 1, v___y_3924_);
                                return v___x_3968_;
                            } else {
                                v___x_3969_ = leanh::lean_unsigned_to_nat(5);
                                v___x_3970_ = l_Lean_Syntax_getArg(v_x_3706_, v___x_3969_);
                                v___x_3971_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__27;
                                leanh::lean_inc(v___x_3970_);
                                v___x_3972_ = l_Lean_Syntax_isOfKind(v___x_3970_, v___x_3971_);
                                if v___x_3972_ == 0 {
                                    leanh::lean_dec(v___x_3970_);
                                    leanh::lean_dec(v_pre_x3f_3922_);
                                    leanh::lean_dec(v___y_3920_);
                                    leanh::lean_dec(v___y_3916_);
                                    leanh::lean_dec(v_x_3706_);
                                    v___x_3973_ = leanh::lean_box(1);
                                    v___x_3974_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_3974_, 0, v___x_3973_);
                                    leanh::lean_ctor_set(v___x_3974_, 1, v___y_3924_);
                                    return v___x_3974_;
                                } else {
                                    v_ref_3975_ = leanh::lean_ctor_get(v___y_3923_, 5);
                                    v___x_3976_ = leanh::lean_unsigned_to_nat(7);
                                    v___x_3977_ = l_Lean_Syntax_getArg(v_x_3706_, v___x_3976_);
                                    v___x_3978_ = leanh::lean_unsigned_to_nat(10);
                                    v___x_3979_ = l_Lean_Syntax_getArg(v_x_3706_, v___x_3978_);
                                    leanh::lean_dec(v_x_3706_);
                                    v___x_3980_ =
                                        l_Lean_SourceInfo_fromRef(v_ref_3975_, v___x_3927_);
                                    v___x_3981_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__21;
                                    v___x_3982_ = l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__1;
                                    v___x_3983_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27), core::ptr::addr_of_mut!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27_once), _init_l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27);
                                    if leanh::lean_obj_tag(v___y_3920_) == 1 {
                                        v_val_3984_ = leanh::lean_ctor_get(v___y_3920_, 0);
                                        leanh::lean_inc(v_val_3984_);
                                        leanh::lean_dec_ref_known(v___y_3920_, 1);
                                        v___x_3985_ = l_Array_mkArray1___redArg(v_val_3984_);
                                        v___y_3842_ = v___y_3916_;
                                        v___y_3843_ = v___y_3924_;
                                        v___y_3844_ = v___y_3918_;
                                        v___y_3845_ = v___x_3981_;
                                        v___y_3846_ = v___x_3970_;
                                        v___y_3847_ = v___x_3977_;
                                        v___y_3848_ = v___x_3980_;
                                        v___y_3849_ = v___x_3983_;
                                        v___y_3850_ = v___x_3982_;
                                        v___y_3851_ = v___x_3979_;
                                        v___y_3852_ = v_pre_x3f_3922_;
                                        v___y_3853_ = v___x_3985_;
                                        state = 5;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v___y_3920_);
                                        v___x_3986_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__28;
                                        v___y_3842_ = v___y_3916_;
                                        v___y_3843_ = v___y_3924_;
                                        v___y_3844_ = v___y_3918_;
                                        v___y_3845_ = v___x_3981_;
                                        v___y_3846_ = v___x_3970_;
                                        v___y_3847_ = v___x_3977_;
                                        v___y_3848_ = v___x_3980_;
                                        v___y_3849_ = v___x_3983_;
                                        v___y_3850_ = v___x_3982_;
                                        v___y_3851_ = v___x_3979_;
                                        v___y_3852_ = v_pre_x3f_3922_;
                                        v___y_3853_ = v___x_3986_;
                                        state = 5;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_3926_);
                    v___x_3987_ = leanh::lean_unsigned_to_nat(5);
                    v___x_3988_ = l_Lean_Syntax_getArg(v_x_3706_, v___x_3987_);
                    v___x_3989_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__27;
                    leanh::lean_inc(v___x_3988_);
                    v___x_3990_ = l_Lean_Syntax_isOfKind(v___x_3988_, v___x_3989_);
                    if v___x_3990_ == 0 {
                        leanh::lean_dec(v___x_3988_);
                        leanh::lean_dec(v_pre_x3f_3922_);
                        leanh::lean_dec(v___y_3920_);
                        leanh::lean_dec(v___y_3916_);
                        leanh::lean_dec(v_x_3706_);
                        v___x_3991_ = leanh::lean_box(1);
                        v___x_3992_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3992_, 0, v___x_3991_);
                        leanh::lean_ctor_set(v___x_3992_, 1, v___y_3924_);
                        return v___x_3992_;
                    } else {
                        v_ref_3993_ = leanh::lean_ctor_get(v___y_3923_, 5);
                        v___x_3994_ = leanh::lean_unsigned_to_nat(7);
                        v___x_3995_ = l_Lean_Syntax_getArg(v_x_3706_, v___x_3994_);
                        v___x_3996_ = leanh::lean_unsigned_to_nat(10);
                        v___x_3997_ = l_Lean_Syntax_getArg(v_x_3706_, v___x_3996_);
                        leanh::lean_dec(v_x_3706_);
                        v___x_3998_ = 0;
                        v___x_3999_ = l_Lean_SourceInfo_fromRef(v_ref_3993_, v___x_3998_);
                        v___x_4000_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__21;
                        v___x_4001_ = l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__1;
                        v___x_4002_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27), core::ptr::addr_of_mut!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27_once), _init_l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27);
                        if leanh::lean_obj_tag(v___y_3920_) == 1 {
                            v_val_4003_ = leanh::lean_ctor_get(v___y_3920_, 0);
                            leanh::lean_inc(v_val_4003_);
                            leanh::lean_dec_ref_known(v___y_3920_, 1);
                            v___x_4004_ = l_Array_mkArray1___redArg(v_val_4003_);
                            v___y_3879_ = v___y_3916_;
                            v___y_3880_ = v___y_3924_;
                            v___y_3881_ = v___y_3918_;
                            v___y_3882_ = v___x_4000_;
                            v___y_3883_ = v___x_3999_;
                            v___y_3884_ = v___x_3988_;
                            v___y_3885_ = v___x_4001_;
                            v___y_3886_ = v_pre_x3f_3922_;
                            v___y_3887_ = v___x_3997_;
                            v___y_3888_ = v___x_3995_;
                            v___y_3889_ = v___x_4002_;
                            v___y_3890_ = v___x_4004_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_dec(v___y_3920_);
                            v___x_4005_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__28;
                            v___y_3879_ = v___y_3916_;
                            v___y_3880_ = v___y_3924_;
                            v___y_3881_ = v___y_3918_;
                            v___y_3882_ = v___x_4000_;
                            v___y_3883_ = v___x_3999_;
                            v___y_3884_ = v___x_3988_;
                            v___y_3885_ = v___x_4001_;
                            v___y_3886_ = v_pre_x3f_3922_;
                            v___y_3887_ = v___x_3997_;
                            v___y_3888_ = v___x_3995_;
                            v___y_3889_ = v___x_4002_;
                            v___y_3890_ = v___x_4005_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            8 => {
                v___x_4010_ = leanh::lean_unsigned_to_nat(1);
                v___x_4011_ = l_Lean_Syntax_getArg(v_x_3706_, v___x_4010_);
                v___x_4012_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__5;
                v___x_4013_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__2;
                leanh::lean_inc(v___x_4011_);
                v___x_4014_ = l_Lean_Syntax_isOfKind(v___x_4011_, v___x_4013_);
                if v___x_4014_ == 0 {
                    leanh::lean_dec(v___x_4011_);
                    leanh::lean_dec(v_doc_x3f_4007_);
                    leanh::lean_dec(v_x_3706_);
                    v___x_4015_ = leanh::lean_box(1);
                    v___x_4016_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4016_, 0, v___x_4015_);
                    leanh::lean_ctor_set(v___x_4016_, 1, v___y_4009_);
                    return v___x_4016_;
                } else {
                    v___x_4017_ = leanh::lean_unsigned_to_nat(2);
                    v___x_4018_ = leanh::lean_unsigned_to_nat(3);
                    v___x_4019_ = l_Lean_Syntax_getArg(v_x_3706_, v___x_4018_);
                    v___x_4020_ = l_Lean_Syntax_isNone(v___x_4019_);
                    if v___x_4020_ == 0 {
                        leanh::lean_inc(v___x_4019_);
                        v___x_4021_ = l_Lean_Syntax_matchesNull(v___x_4019_, v___x_4010_);
                        if v___x_4021_ == 0 {
                            leanh::lean_dec(v___x_4019_);
                            leanh::lean_dec(v___x_4011_);
                            leanh::lean_dec(v_doc_x3f_4007_);
                            leanh::lean_dec(v_x_3706_);
                            v___x_4022_ = leanh::lean_box(1);
                            v___x_4023_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_4023_, 0, v___x_4022_);
                            leanh::lean_ctor_set(v___x_4023_, 1, v___y_4009_);
                            return v___x_4023_;
                        } else {
                            v_pre_x3f_4024_ = l_Lean_Syntax_getArg(v___x_4019_, v___x_3802_);
                            leanh::lean_dec(v___x_4019_);
                            v___x_4025_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_4025_, 0, v_pre_x3f_4024_);
                            v___y_3916_ = v___x_4011_;
                            v___y_3917_ = v___x_4017_;
                            v___y_3918_ = v___x_4012_;
                            v___y_3919_ = v___x_4010_;
                            v___y_3920_ = v_doc_x3f_4007_;
                            v___y_3921_ = v___x_4018_;
                            v_pre_x3f_3922_ = v___x_4025_;
                            v___y_3923_ = v___y_4008_;
                            v___y_3924_ = v___y_4009_;
                            state = 7;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_4019_);
                        v___x_4026_ = leanh::lean_box(0);
                        v___y_3916_ = v___x_4011_;
                        v___y_3917_ = v___x_4017_;
                        v___y_3918_ = v___x_4012_;
                        v___y_3919_ = v___x_4010_;
                        v___y_3920_ = v_doc_x3f_4007_;
                        v___y_3921_ = v___x_4018_;
                        v_pre_x3f_3922_ = v___x_4026_;
                        v___y_3923_ = v___y_4008_;
                        v___y_3924_ = v___y_4009_;
                        state = 7;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___boxed(
    mut v_x_4040_: *mut leanh::LeanObject,
    mut v_a_4041_: *mut leanh::LeanObject,
    mut v_a_4042_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4043_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4043_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1(v_x_4040_, v_a_4041_, v_a_4042_);
    leanh::lean_dec_ref(v_a_4041_);
    return v_res_4043_;
}
pub unsafe fn l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d____1(
    mut v_x_4045_: *mut leanh::LeanObject,
    mut v_a_4046_: *mut leanh::LeanObject,
    mut v_a_4047_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4138_: u8 = 0;
    let mut v___x_4139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_x3f_4261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4266_: u8 = 0;
    let mut v___x_4267_: u8 = 0;
    let mut v___x_4268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4271_: u8 = 0;
    let mut v___x_4272_: u8 = 0;
    let mut v___x_4273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4277_: u8 = 0;
    let mut v___x_4278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4282_: u8 = 0;
    let mut v___x_4283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4288_: u8 = 0;
    let mut v___x_4289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4305_: u8 = 0;
    let mut v___x_4306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4311_: u8 = 0;
    let mut v___x_4312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: u8 = 0;
    let mut v___x_4330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4337_: u8 = 0;
    let mut v___x_4338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_4346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4353_: u8 = 0;
    let mut v___x_4354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4359_: u8 = 0;
    let mut v___x_4360_: u8 = 0;
    let mut v___x_4361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_x3f_4363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4367_: u8 = 0;
    let mut v___x_4368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4369_: u8 = 0;
    let mut v___x_4370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_4372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4374_: u8 = 0;
    let mut v___x_4375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4100_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0;
                v___x_4101_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1;
                v___x_4137_ = l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1;
                leanh::lean_inc(v_x_4045_);
                v___x_4138_ = l_Lean_Syntax_isOfKind(v_x_4045_, v___x_4137_);
                if v___x_4138_ == 0 {
                    leanh::lean_dec(v_x_4045_);
                    v___x_4139_ = leanh::lean_box(1);
                    v___x_4140_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4140_, 0, v___x_4139_);
                    leanh::lean_ctor_set(v___x_4140_, 1, v_a_4047_);
                    return v___x_4140_;
                } else {
                    v___x_4141_ = leanh::lean_unsigned_to_nat(0);
                    v___x_4366_ = l_Lean_Syntax_getArg(v_x_4045_, v___x_4141_);
                    v___x_4367_ = l_Lean_Syntax_isNone(v___x_4366_);
                    if v___x_4367_ == 0 {
                        v___x_4368_ = leanh::lean_unsigned_to_nat(1);
                        leanh::lean_inc(v___x_4366_);
                        v___x_4369_ = l_Lean_Syntax_matchesNull(v___x_4366_, v___x_4368_);
                        if v___x_4369_ == 0 {
                            leanh::lean_dec(v___x_4366_);
                            leanh::lean_dec(v_x_4045_);
                            v___x_4370_ = leanh::lean_box(1);
                            v___x_4371_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_4371_, 0, v___x_4370_);
                            leanh::lean_ctor_set(v___x_4371_, 1, v_a_4047_);
                            return v___x_4371_;
                        } else {
                            v_doc_x3f_4372_ = l_Lean_Syntax_getArg(v___x_4366_, v___x_4141_);
                            leanh::lean_dec(v___x_4366_);
                            v___x_4373_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__29;
                            leanh::lean_inc(v_doc_x3f_4372_);
                            v___x_4374_ = l_Lean_Syntax_isOfKind(v_doc_x3f_4372_, v___x_4373_);
                            if v___x_4374_ == 0 {
                                leanh::lean_dec(v_doc_x3f_4372_);
                                leanh::lean_dec(v_x_4045_);
                                v___x_4375_ = leanh::lean_box(1);
                                v___x_4376_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_4376_, 0, v___x_4375_);
                                leanh::lean_ctor_set(v___x_4376_, 1, v_a_4047_);
                                return v___x_4376_;
                            } else {
                                v___x_4377_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_4377_, 0, v_doc_x3f_4372_);
                                v_doc_x3f_4346_ = v___x_4377_;
                                v___y_4347_ = v_a_4046_;
                                v___y_4348_ = v_a_4047_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v___x_4366_);
                        v___x_4378_ = leanh::lean_box(0);
                        v_doc_x3f_4346_ = v___x_4378_;
                        v___y_4347_ = v_a_4046_;
                        v___y_4348_ = v_a_4047_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref(v___y_4056_);
                v___x_4063_ = l_Array_append___redArg(v___y_4056_, v___y_4062_);
                leanh::lean_dec_ref(v___y_4062_);
                leanh::lean_inc_n(v___y_4054_, 4);
                leanh::lean_inc_n(v___y_4055_, 7);
                v___x_4064_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_4064_, 0, v___y_4055_);
                leanh::lean_ctor_set(v___x_4064_, 1, v___y_4054_);
                leanh::lean_ctor_set(v___x_4064_, 2, v___x_4063_);
                leanh::lean_inc(v___y_4061_);
                v___x_4065_ =
                    l_Lean_Syntax_node2(v___y_4055_, v___y_4061_, v___y_4053_, v___x_4064_);
                v___x_4066_ =
                    l_Lean_Syntax_node2(v___y_4055_, v___y_4050_, v___y_4058_, v___x_4065_);
                v___x_4067_ = l_Lean_Syntax_node1(v___y_4055_, v___y_4054_, v___x_4066_);
                v___x_4068_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__34;
                v___x_4069_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4069_, 0, v___y_4055_);
                leanh::lean_ctor_set(v___x_4069_, 1, v___x_4068_);
                v___x_4070_ = l_Lean_Syntax_node1(v___y_4055_, v___y_4054_, v___y_4059_);
                leanh::lean_inc(v___y_4051_);
                v___x_4071_ = l_Lean_Syntax_node5(
                    v___y_4055_,
                    v___y_4051_,
                    v___y_4060_,
                    v___y_4049_,
                    v___x_4067_,
                    v___x_4069_,
                    v___x_4070_,
                );
                v___x_4072_ =
                    l_Lean_Syntax_node2(v___y_4055_, v___y_4054_, v___y_4052_, v___x_4071_);
                v___x_4073_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4073_, 0, v___x_4072_);
                leanh::lean_ctor_set(v___x_4073_, 1, v___y_4057_);
                return v___x_4073_;
            }
            2 => {
                leanh::lean_inc_ref(v___y_4081_);
                v___x_4089_ = l_Array_append___redArg(v___y_4081_, v___y_4088_);
                leanh::lean_dec_ref(v___y_4088_);
                leanh::lean_inc_n(v___y_4079_, 4);
                leanh::lean_inc_n(v___y_4082_, 7);
                v___x_4090_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_4090_, 0, v___y_4082_);
                leanh::lean_ctor_set(v___x_4090_, 1, v___y_4079_);
                leanh::lean_ctor_set(v___x_4090_, 2, v___x_4089_);
                leanh::lean_inc(v___y_4080_);
                v___x_4091_ =
                    l_Lean_Syntax_node2(v___y_4082_, v___y_4080_, v___y_4086_, v___x_4090_);
                v___x_4092_ =
                    l_Lean_Syntax_node2(v___y_4082_, v___y_4087_, v___y_4085_, v___x_4091_);
                v___x_4093_ = l_Lean_Syntax_node1(v___y_4082_, v___y_4079_, v___x_4092_);
                v___x_4094_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__34;
                v___x_4095_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4095_, 0, v___y_4082_);
                leanh::lean_ctor_set(v___x_4095_, 1, v___x_4094_);
                v___x_4096_ = l_Lean_Syntax_node1(v___y_4082_, v___y_4079_, v___y_4075_);
                leanh::lean_inc(v___y_4076_);
                v___x_4097_ = l_Lean_Syntax_node5(
                    v___y_4082_,
                    v___y_4076_,
                    v___y_4078_,
                    v___y_4077_,
                    v___x_4093_,
                    v___x_4095_,
                    v___x_4096_,
                );
                v___x_4098_ =
                    l_Lean_Syntax_node2(v___y_4082_, v___y_4079_, v___y_4084_, v___x_4097_);
                v___x_4099_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4099_, 0, v___x_4098_);
                leanh::lean_ctor_set(v___x_4099_, 1, v___y_4083_);
                return v___x_4099_;
            }
            3 => {
                leanh::lean_inc_ref(v___y_4110_);
                v___x_4118_ = l_Array_append___redArg(v___y_4110_, v___y_4117_);
                leanh::lean_dec_ref(v___y_4117_);
                leanh::lean_inc_n(v___y_4104_, 5);
                leanh::lean_inc_n(v___y_4113_, 12);
                v___x_4119_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_4119_, 0, v___y_4113_);
                leanh::lean_ctor_set(v___x_4119_, 1, v___y_4104_);
                leanh::lean_ctor_set(v___x_4119_, 2, v___x_4118_);
                leanh::lean_inc_ref(v___x_4119_);
                leanh::lean_inc(v___y_4103_);
                v___x_4120_ =
                    l_Lean_Syntax_node2(v___y_4113_, v___y_4103_, v___y_4115_, v___x_4119_);
                leanh::lean_inc(v___y_4116_);
                leanh::lean_inc(v___y_4105_);
                v___x_4121_ =
                    l_Lean_Syntax_node2(v___y_4113_, v___y_4105_, v___y_4116_, v___x_4120_);
                v___x_4122_ = l_Lean_Syntax_node1(v___y_4113_, v___y_4104_, v___x_4121_);
                v___x_4123_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__34;
                v___x_4124_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4124_, 0, v___y_4113_);
                leanh::lean_ctor_set(v___x_4124_, 1, v___x_4123_);
                v___x_4125_ = l_Lean_Syntax_node1(v___y_4113_, v___y_4104_, v___y_4107_);
                leanh::lean_inc(v___x_4125_);
                leanh::lean_inc_ref(v___x_4124_);
                leanh::lean_inc(v___y_4106_);
                leanh::lean_inc(v___y_4109_);
                leanh::lean_inc_n(v___y_4111_, 2);
                v___x_4126_ = l_Lean_Syntax_node5(
                    v___y_4113_,
                    v___y_4111_,
                    v___y_4109_,
                    v___y_4106_,
                    v___x_4122_,
                    v___x_4124_,
                    v___x_4125_,
                );
                v___x_4127_ = l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__0;
                leanh::lean_inc_ref(v___y_4108_);
                v___x_4128_ =
                    l_Lean_Name_mkStr4(v___x_4100_, v___x_4101_, v___y_4108_, v___x_4127_);
                v___x_4129_ = l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__2;
                v___x_4130_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4130_, 0, v___y_4113_);
                leanh::lean_ctor_set(v___x_4130_, 1, v___x_4129_);
                v___x_4131_ =
                    l_Lean_Syntax_node2(v___y_4113_, v___x_4128_, v___x_4130_, v___x_4119_);
                v___x_4132_ =
                    l_Lean_Syntax_node2(v___y_4113_, v___y_4105_, v___y_4116_, v___x_4131_);
                v___x_4133_ = l_Lean_Syntax_node1(v___y_4113_, v___y_4104_, v___x_4132_);
                v___x_4134_ = l_Lean_Syntax_node5(
                    v___y_4113_,
                    v___y_4111_,
                    v___y_4109_,
                    v___y_4106_,
                    v___x_4133_,
                    v___x_4124_,
                    v___x_4125_,
                );
                v___x_4135_ = l_Lean_Syntax_node3(
                    v___y_4113_,
                    v___y_4104_,
                    v___y_4112_,
                    v___x_4126_,
                    v___x_4134_,
                );
                v___x_4136_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4136_, 0, v___x_4135_);
                leanh::lean_ctor_set(v___x_4136_, 1, v___y_4114_);
                return v___x_4136_;
            }
            4 => {
                leanh::lean_inc_ref(v___y_4152_);
                v___x_4155_ = l_Array_append___redArg(v___y_4152_, v___y_4154_);
                leanh::lean_dec_ref(v___y_4154_);
                leanh::lean_inc(v___y_4145_);
                leanh::lean_inc_n(v___y_4146_, 9);
                v___x_4156_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_4156_, 0, v___y_4146_);
                leanh::lean_ctor_set(v___x_4156_, 1, v___y_4145_);
                leanh::lean_ctor_set(v___x_4156_, 2, v___x_4155_);
                v___x_4157_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0;
                v___x_4158_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4158_, 0, v___y_4146_);
                leanh::lean_ctor_set(v___x_4158_, 1, v___x_4157_);
                v___x_4159_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__1;
                v___x_4160_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4160_, 0, v___y_4146_);
                leanh::lean_ctor_set(v___x_4160_, 1, v___x_4159_);
                v___x_4161_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__47;
                v___x_4162_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4162_, 0, v___y_4146_);
                leanh::lean_ctor_set(v___x_4162_, 1, v___x_4161_);
                v___x_4163_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__10;
                v___x_4164_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4164_, 0, v___y_4146_);
                leanh::lean_ctor_set(v___x_4164_, 1, v___x_4163_);
                leanh::lean_inc(v___y_4150_);
                leanh::lean_inc(v___y_4144_);
                v___x_4165_ = l_Lean_Syntax_node8(
                    v___y_4146_,
                    v___y_4144_,
                    v___x_4156_,
                    v___x_4158_,
                    v___y_4150_,
                    v___x_4160_,
                    v___y_4153_,
                    v___x_4162_,
                    v___x_4164_,
                    v___y_4149_,
                );
                v___x_4166_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__0;
                v___x_4167_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__1;
                v___x_4168_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4168_, 0, v___y_4146_);
                leanh::lean_ctor_set(v___x_4168_, 1, v___x_4166_);
                v___x_4169_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__24;
                v___x_4170_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4170_, 0, v___y_4146_);
                leanh::lean_ctor_set(v___x_4170_, 1, v___x_4169_);
                v___x_4171_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__2;
                leanh::lean_inc_ref(v___y_4143_);
                v___x_4172_ =
                    l_Lean_Name_mkStr4(v___x_4100_, v___x_4101_, v___y_4143_, v___x_4171_);
                v___x_4173_ = l_Lean_Parser_Attr_simprocAttr___closed__0;
                v___x_4174_ = l_Lean_Parser_Attr_simprocBuiltinAttr___closed__1;
                v___x_4175_ = l_Lean_Parser_Attr_simprocBuiltinAttr___closed__2;
                v___x_4176_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4176_, 0, v___y_4146_);
                leanh::lean_ctor_set(v___x_4176_, 1, v___x_4175_);
                if leanh::lean_obj_tag(v___y_4147_) == 1 {
                    v_val_4177_ = leanh::lean_ctor_get(v___y_4147_, 0);
                    leanh::lean_inc(v_val_4177_);
                    leanh::lean_dec_ref_known(v___y_4147_, 1);
                    v___x_4178_ = l_Array_mkArray1___redArg(v_val_4177_);
                    v___y_4103_ = v___x_4174_;
                    v___y_4104_ = v___y_4145_;
                    v___y_4105_ = v___x_4172_;
                    v___y_4106_ = v___x_4170_;
                    v___y_4107_ = v___y_4150_;
                    v___y_4108_ = v___x_4173_;
                    v___y_4109_ = v___x_4168_;
                    v___y_4110_ = v___y_4152_;
                    v___y_4111_ = v___x_4167_;
                    v___y_4112_ = v___x_4165_;
                    v___y_4113_ = v___y_4146_;
                    v___y_4114_ = v___y_4148_;
                    v___y_4115_ = v___x_4176_;
                    v___y_4116_ = v___y_4151_;
                    v___y_4117_ = v___x_4178_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_dec(v___y_4147_);
                    v___x_4179_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__28;
                    v___y_4103_ = v___x_4174_;
                    v___y_4104_ = v___y_4145_;
                    v___y_4105_ = v___x_4172_;
                    v___y_4106_ = v___x_4170_;
                    v___y_4107_ = v___y_4150_;
                    v___y_4108_ = v___x_4173_;
                    v___y_4109_ = v___x_4168_;
                    v___y_4110_ = v___y_4152_;
                    v___y_4111_ = v___x_4167_;
                    v___y_4112_ = v___x_4165_;
                    v___y_4113_ = v___y_4146_;
                    v___y_4114_ = v___y_4148_;
                    v___y_4115_ = v___x_4176_;
                    v___y_4116_ = v___y_4151_;
                    v___y_4117_ = v___x_4179_;
                    state = 3;
                    continue;
                }
            }
            5 => {
                leanh::lean_inc_ref(v___y_4187_);
                v___x_4193_ = l_Array_append___redArg(v___y_4187_, v___y_4192_);
                leanh::lean_dec_ref(v___y_4192_);
                leanh::lean_inc(v___y_4191_);
                leanh::lean_inc_n(v___y_4182_, 9);
                v___x_4194_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_4194_, 0, v___y_4182_);
                leanh::lean_ctor_set(v___x_4194_, 1, v___y_4191_);
                leanh::lean_ctor_set(v___x_4194_, 2, v___x_4193_);
                v___x_4195_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0;
                v___x_4196_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4196_, 0, v___y_4182_);
                leanh::lean_ctor_set(v___x_4196_, 1, v___x_4195_);
                v___x_4197_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__1;
                v___x_4198_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4198_, 0, v___y_4182_);
                leanh::lean_ctor_set(v___x_4198_, 1, v___x_4197_);
                v___x_4199_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__47;
                v___x_4200_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4200_, 0, v___y_4182_);
                leanh::lean_ctor_set(v___x_4200_, 1, v___x_4199_);
                v___x_4201_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__10;
                v___x_4202_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4202_, 0, v___y_4182_);
                leanh::lean_ctor_set(v___x_4202_, 1, v___x_4201_);
                leanh::lean_inc(v___y_4190_);
                leanh::lean_inc(v___y_4184_);
                v___x_4203_ = l_Lean_Syntax_node8(
                    v___y_4182_,
                    v___y_4184_,
                    v___x_4194_,
                    v___x_4196_,
                    v___y_4190_,
                    v___x_4198_,
                    v___y_4186_,
                    v___x_4200_,
                    v___x_4202_,
                    v___y_4188_,
                );
                v___x_4204_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__0;
                v___x_4205_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__1;
                v___x_4206_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4206_, 0, v___y_4182_);
                leanh::lean_ctor_set(v___x_4206_, 1, v___x_4204_);
                v___x_4207_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__24;
                v___x_4208_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4208_, 0, v___y_4182_);
                leanh::lean_ctor_set(v___x_4208_, 1, v___x_4207_);
                v___x_4209_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__2;
                leanh::lean_inc_ref(v___y_4181_);
                v___x_4210_ =
                    l_Lean_Name_mkStr4(v___x_4100_, v___x_4101_, v___y_4181_, v___x_4209_);
                v___x_4211_ = l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__1;
                v___x_4212_ = l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__2;
                v___x_4213_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4213_, 0, v___y_4182_);
                leanh::lean_ctor_set(v___x_4213_, 1, v___x_4212_);
                if leanh::lean_obj_tag(v___y_4183_) == 1 {
                    v_val_4214_ = leanh::lean_ctor_get(v___y_4183_, 0);
                    leanh::lean_inc(v_val_4214_);
                    leanh::lean_dec_ref_known(v___y_4183_, 1);
                    v___x_4215_ = l_Array_mkArray1___redArg(v_val_4214_);
                    v___y_4049_ = v___x_4208_;
                    v___y_4050_ = v___x_4210_;
                    v___y_4051_ = v___x_4205_;
                    v___y_4052_ = v___x_4203_;
                    v___y_4053_ = v___x_4213_;
                    v___y_4054_ = v___y_4191_;
                    v___y_4055_ = v___y_4182_;
                    v___y_4056_ = v___y_4187_;
                    v___y_4057_ = v___y_4185_;
                    v___y_4058_ = v___y_4189_;
                    v___y_4059_ = v___y_4190_;
                    v___y_4060_ = v___x_4206_;
                    v___y_4061_ = v___x_4211_;
                    v___y_4062_ = v___x_4215_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v___y_4183_);
                    v___x_4216_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__28;
                    v___y_4049_ = v___x_4208_;
                    v___y_4050_ = v___x_4210_;
                    v___y_4051_ = v___x_4205_;
                    v___y_4052_ = v___x_4203_;
                    v___y_4053_ = v___x_4213_;
                    v___y_4054_ = v___y_4191_;
                    v___y_4055_ = v___y_4182_;
                    v___y_4056_ = v___y_4187_;
                    v___y_4057_ = v___y_4185_;
                    v___y_4058_ = v___y_4189_;
                    v___y_4059_ = v___y_4190_;
                    v___y_4060_ = v___x_4206_;
                    v___y_4061_ = v___x_4211_;
                    v___y_4062_ = v___x_4216_;
                    state = 1;
                    continue;
                }
            }
            6 => {
                leanh::lean_inc_ref(v___y_4219_);
                v___x_4230_ = l_Array_append___redArg(v___y_4219_, v___y_4229_);
                leanh::lean_dec_ref(v___y_4229_);
                leanh::lean_inc(v___y_4227_);
                leanh::lean_inc_n(v___y_4221_, 9);
                v___x_4231_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_4231_, 0, v___y_4221_);
                leanh::lean_ctor_set(v___x_4231_, 1, v___y_4227_);
                leanh::lean_ctor_set(v___x_4231_, 2, v___x_4230_);
                v___x_4232_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0;
                v___x_4233_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4233_, 0, v___y_4221_);
                leanh::lean_ctor_set(v___x_4233_, 1, v___x_4232_);
                v___x_4234_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__1;
                v___x_4235_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4235_, 0, v___y_4221_);
                leanh::lean_ctor_set(v___x_4235_, 1, v___x_4234_);
                v___x_4236_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__47;
                v___x_4237_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4237_, 0, v___y_4221_);
                leanh::lean_ctor_set(v___x_4237_, 1, v___x_4236_);
                v___x_4238_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__10;
                v___x_4239_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4239_, 0, v___y_4221_);
                leanh::lean_ctor_set(v___x_4239_, 1, v___x_4238_);
                leanh::lean_inc(v___y_4220_);
                leanh::lean_inc(v___y_4228_);
                v___x_4240_ = l_Lean_Syntax_node8(
                    v___y_4221_,
                    v___y_4228_,
                    v___x_4231_,
                    v___x_4233_,
                    v___y_4220_,
                    v___x_4235_,
                    v___y_4225_,
                    v___x_4237_,
                    v___x_4239_,
                    v___y_4224_,
                );
                v___x_4241_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__0;
                v___x_4242_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__1;
                v___x_4243_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4243_, 0, v___y_4221_);
                leanh::lean_ctor_set(v___x_4243_, 1, v___x_4241_);
                v___x_4244_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__24;
                v___x_4245_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4245_, 0, v___y_4221_);
                leanh::lean_ctor_set(v___x_4245_, 1, v___x_4244_);
                v___x_4246_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__2;
                leanh::lean_inc_ref(v___y_4218_);
                v___x_4247_ =
                    l_Lean_Name_mkStr4(v___x_4100_, v___x_4101_, v___y_4218_, v___x_4246_);
                v___x_4248_ = l_Lean_Parser_Attr_simprocBuiltinAttr___closed__1;
                v___x_4249_ = l_Lean_Parser_Attr_simprocBuiltinAttr___closed__2;
                v___x_4250_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4250_, 0, v___y_4221_);
                leanh::lean_ctor_set(v___x_4250_, 1, v___x_4249_);
                if leanh::lean_obj_tag(v___y_4222_) == 1 {
                    v_val_4251_ = leanh::lean_ctor_get(v___y_4222_, 0);
                    leanh::lean_inc(v_val_4251_);
                    leanh::lean_dec_ref_known(v___y_4222_, 1);
                    v___x_4252_ = l_Array_mkArray1___redArg(v_val_4251_);
                    v___y_4075_ = v___y_4220_;
                    v___y_4076_ = v___x_4242_;
                    v___y_4077_ = v___x_4245_;
                    v___y_4078_ = v___x_4243_;
                    v___y_4079_ = v___y_4227_;
                    v___y_4080_ = v___x_4248_;
                    v___y_4081_ = v___y_4219_;
                    v___y_4082_ = v___y_4221_;
                    v___y_4083_ = v___y_4223_;
                    v___y_4084_ = v___x_4240_;
                    v___y_4085_ = v___y_4226_;
                    v___y_4086_ = v___x_4250_;
                    v___y_4087_ = v___x_4247_;
                    v___y_4088_ = v___x_4252_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v___y_4222_);
                    v___x_4253_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__28;
                    v___y_4075_ = v___y_4220_;
                    v___y_4076_ = v___x_4242_;
                    v___y_4077_ = v___x_4245_;
                    v___y_4078_ = v___x_4243_;
                    v___y_4079_ = v___y_4227_;
                    v___y_4080_ = v___x_4248_;
                    v___y_4081_ = v___y_4219_;
                    v___y_4082_ = v___y_4221_;
                    v___y_4083_ = v___y_4223_;
                    v___y_4084_ = v___x_4240_;
                    v___y_4085_ = v___y_4226_;
                    v___y_4086_ = v___x_4250_;
                    v___y_4087_ = v___x_4247_;
                    v___y_4088_ = v___x_4253_;
                    state = 2;
                    continue;
                }
            }
            7 => {
                v___x_4264_ = leanh::lean_unsigned_to_nat(4);
                v___x_4265_ = l_Lean_Syntax_getArg(v_x_4045_, v___x_4264_);
                leanh::lean_inc(v___x_4265_);
                v___x_4266_ = l_Lean_Syntax_matchesNull(v___x_4265_, v___x_4141_);
                if v___x_4266_ == 0 {
                    leanh::lean_inc(v___x_4265_);
                    v___x_4267_ = l_Lean_Syntax_matchesNull(v___x_4265_, v___y_4260_);
                    if v___x_4267_ == 0 {
                        leanh::lean_dec(v___x_4265_);
                        leanh::lean_dec(v_pre_x3f_4261_);
                        leanh::lean_dec(v___y_4259_);
                        leanh::lean_dec(v___y_4257_);
                        leanh::lean_dec(v_x_4045_);
                        v___x_4268_ = leanh::lean_box(1);
                        v___x_4269_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_4269_, 0, v___x_4268_);
                        leanh::lean_ctor_set(v___x_4269_, 1, v___y_4263_);
                        return v___x_4269_;
                    } else {
                        v___x_4270_ = l_Lean_Syntax_getArg(v___x_4265_, v___y_4256_);
                        leanh::lean_dec(v___x_4265_);
                        leanh::lean_inc(v___x_4270_);
                        v___x_4271_ = l_Lean_Syntax_matchesNull(v___x_4270_, v___y_4256_);
                        if v___x_4271_ == 0 {
                            leanh::lean_inc(v___x_4270_);
                            v___x_4272_ = l_Lean_Syntax_matchesNull(v___x_4270_, v___y_4260_);
                            if v___x_4272_ == 0 {
                                leanh::lean_dec(v___x_4270_);
                                leanh::lean_dec(v_pre_x3f_4261_);
                                leanh::lean_dec(v___y_4259_);
                                leanh::lean_dec(v___y_4257_);
                                leanh::lean_dec(v_x_4045_);
                                v___x_4273_ = leanh::lean_box(1);
                                v___x_4274_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_4274_, 0, v___x_4273_);
                                leanh::lean_ctor_set(v___x_4274_, 1, v___y_4263_);
                                return v___x_4274_;
                            } else {
                                v___x_4275_ = l_Lean_Syntax_getArg(v___x_4270_, v___x_4141_);
                                v___x_4276_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__5;
                                v___x_4277_ = l_Lean_Syntax_matchesIdent(v___x_4275_, v___x_4276_);
                                leanh::lean_dec(v___x_4275_);
                                if v___x_4277_ == 0 {
                                    leanh::lean_dec(v___x_4270_);
                                    leanh::lean_dec(v_pre_x3f_4261_);
                                    leanh::lean_dec(v___y_4259_);
                                    leanh::lean_dec(v___y_4257_);
                                    leanh::lean_dec(v_x_4045_);
                                    v___x_4278_ = leanh::lean_box(1);
                                    v___x_4279_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_4279_, 0, v___x_4278_);
                                    leanh::lean_ctor_set(v___x_4279_, 1, v___y_4263_);
                                    return v___x_4279_;
                                } else {
                                    v___x_4280_ = l_Lean_Syntax_getArg(v___x_4270_, v___y_4258_);
                                    leanh::lean_dec(v___x_4270_);
                                    v___x_4281_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__7;
                                    v___x_4282_ =
                                        l_Lean_Syntax_matchesIdent(v___x_4280_, v___x_4281_);
                                    leanh::lean_dec(v___x_4280_);
                                    if v___x_4282_ == 0 {
                                        leanh::lean_dec(v_pre_x3f_4261_);
                                        leanh::lean_dec(v___y_4259_);
                                        leanh::lean_dec(v___y_4257_);
                                        leanh::lean_dec(v_x_4045_);
                                        v___x_4283_ = leanh::lean_box(1);
                                        v___x_4284_ =
                                            leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                        leanh::lean_ctor_set(v___x_4284_, 0, v___x_4283_);
                                        leanh::lean_ctor_set(v___x_4284_, 1, v___y_4263_);
                                        return v___x_4284_;
                                    } else {
                                        v___x_4285_ = leanh::lean_unsigned_to_nat(5);
                                        v___x_4286_ = l_Lean_Syntax_getArg(v_x_4045_, v___x_4285_);
                                        v___x_4287_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__27;
                                        leanh::lean_inc(v___x_4286_);
                                        v___x_4288_ =
                                            l_Lean_Syntax_isOfKind(v___x_4286_, v___x_4287_);
                                        if v___x_4288_ == 0 {
                                            leanh::lean_dec(v___x_4286_);
                                            leanh::lean_dec(v_pre_x3f_4261_);
                                            leanh::lean_dec(v___y_4259_);
                                            leanh::lean_dec(v___y_4257_);
                                            leanh::lean_dec(v_x_4045_);
                                            v___x_4289_ = leanh::lean_box(1);
                                            v___x_4290_ =
                                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                            leanh::lean_ctor_set(
                                                v___x_4290_,
                                                0,
                                                v___x_4289_,
                                            );
                                            leanh::lean_ctor_set(
                                                v___x_4290_,
                                                1,
                                                v___y_4263_,
                                            );
                                            return v___x_4290_;
                                        } else {
                                            v_ref_4291_ =
                                                leanh::lean_ctor_get(v___y_4262_, 5);
                                            v___x_4292_ = leanh::lean_unsigned_to_nat(7);
                                            v___x_4293_ =
                                                l_Lean_Syntax_getArg(v_x_4045_, v___x_4292_);
                                            v___x_4294_ = leanh::lean_unsigned_to_nat(10);
                                            v___x_4295_ =
                                                l_Lean_Syntax_getArg(v_x_4045_, v___x_4294_);
                                            leanh::lean_dec(v_x_4045_);
                                            v___x_4296_ =
                                                l_Lean_SourceInfo_fromRef(v_ref_4291_, v___x_4271_);
                                            v___x_4297_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__21;
                                            v___x_4298_ = l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__1;
                                            v___x_4299_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27), core::ptr::addr_of_mut!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27_once), _init_l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27);
                                            if leanh::lean_obj_tag(v___y_4259_) == 1 {
                                                v_val_4300_ =
                                                    leanh::lean_ctor_get(v___y_4259_, 0);
                                                leanh::lean_inc(v_val_4300_);
                                                leanh::lean_dec_ref_known(v___y_4259_, 1);
                                                v___x_4301_ =
                                                    l_Array_mkArray1___redArg(v_val_4300_);
                                                v___y_4143_ = v___y_4255_;
                                                v___y_4144_ = v___x_4298_;
                                                v___y_4145_ = v___x_4297_;
                                                v___y_4146_ = v___x_4296_;
                                                v___y_4147_ = v_pre_x3f_4261_;
                                                v___y_4148_ = v___y_4263_;
                                                v___y_4149_ = v___x_4295_;
                                                v___y_4150_ = v___x_4286_;
                                                v___y_4151_ = v___y_4257_;
                                                v___y_4152_ = v___x_4299_;
                                                v___y_4153_ = v___x_4293_;
                                                v___y_4154_ = v___x_4301_;
                                                state = 4;
                                                continue;
                                            } else {
                                                leanh::lean_dec(v___y_4259_);
                                                v___x_4302_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__28;
                                                v___y_4143_ = v___y_4255_;
                                                v___y_4144_ = v___x_4298_;
                                                v___y_4145_ = v___x_4297_;
                                                v___y_4146_ = v___x_4296_;
                                                v___y_4147_ = v_pre_x3f_4261_;
                                                v___y_4148_ = v___y_4263_;
                                                v___y_4149_ = v___x_4295_;
                                                v___y_4150_ = v___x_4286_;
                                                v___y_4151_ = v___y_4257_;
                                                v___y_4152_ = v___x_4299_;
                                                v___y_4153_ = v___x_4293_;
                                                v___y_4154_ = v___x_4302_;
                                                state = 4;
                                                continue;
                                            }
                                        }
                                    }
                                }
                            }
                        } else {
                            v___x_4303_ = l_Lean_Syntax_getArg(v___x_4270_, v___x_4141_);
                            leanh::lean_dec(v___x_4270_);
                            v___x_4304_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__7;
                            v___x_4305_ = l_Lean_Syntax_matchesIdent(v___x_4303_, v___x_4304_);
                            leanh::lean_dec(v___x_4303_);
                            if v___x_4305_ == 0 {
                                leanh::lean_dec(v_pre_x3f_4261_);
                                leanh::lean_dec(v___y_4259_);
                                leanh::lean_dec(v___y_4257_);
                                leanh::lean_dec(v_x_4045_);
                                v___x_4306_ = leanh::lean_box(1);
                                v___x_4307_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_4307_, 0, v___x_4306_);
                                leanh::lean_ctor_set(v___x_4307_, 1, v___y_4263_);
                                return v___x_4307_;
                            } else {
                                v___x_4308_ = leanh::lean_unsigned_to_nat(5);
                                v___x_4309_ = l_Lean_Syntax_getArg(v_x_4045_, v___x_4308_);
                                v___x_4310_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__27;
                                leanh::lean_inc(v___x_4309_);
                                v___x_4311_ = l_Lean_Syntax_isOfKind(v___x_4309_, v___x_4310_);
                                if v___x_4311_ == 0 {
                                    leanh::lean_dec(v___x_4309_);
                                    leanh::lean_dec(v_pre_x3f_4261_);
                                    leanh::lean_dec(v___y_4259_);
                                    leanh::lean_dec(v___y_4257_);
                                    leanh::lean_dec(v_x_4045_);
                                    v___x_4312_ = leanh::lean_box(1);
                                    v___x_4313_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_4313_, 0, v___x_4312_);
                                    leanh::lean_ctor_set(v___x_4313_, 1, v___y_4263_);
                                    return v___x_4313_;
                                } else {
                                    v_ref_4314_ = leanh::lean_ctor_get(v___y_4262_, 5);
                                    v___x_4315_ = leanh::lean_unsigned_to_nat(7);
                                    v___x_4316_ = l_Lean_Syntax_getArg(v_x_4045_, v___x_4315_);
                                    v___x_4317_ = leanh::lean_unsigned_to_nat(10);
                                    v___x_4318_ = l_Lean_Syntax_getArg(v_x_4045_, v___x_4317_);
                                    leanh::lean_dec(v_x_4045_);
                                    v___x_4319_ =
                                        l_Lean_SourceInfo_fromRef(v_ref_4314_, v___x_4266_);
                                    v___x_4320_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__21;
                                    v___x_4321_ = l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__1;
                                    v___x_4322_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27), core::ptr::addr_of_mut!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27_once), _init_l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27);
                                    if leanh::lean_obj_tag(v___y_4259_) == 1 {
                                        v_val_4323_ = leanh::lean_ctor_get(v___y_4259_, 0);
                                        leanh::lean_inc(v_val_4323_);
                                        leanh::lean_dec_ref_known(v___y_4259_, 1);
                                        v___x_4324_ = l_Array_mkArray1___redArg(v_val_4323_);
                                        v___y_4181_ = v___y_4255_;
                                        v___y_4182_ = v___x_4319_;
                                        v___y_4183_ = v_pre_x3f_4261_;
                                        v___y_4184_ = v___x_4321_;
                                        v___y_4185_ = v___y_4263_;
                                        v___y_4186_ = v___x_4316_;
                                        v___y_4187_ = v___x_4322_;
                                        v___y_4188_ = v___x_4318_;
                                        v___y_4189_ = v___y_4257_;
                                        v___y_4190_ = v___x_4309_;
                                        v___y_4191_ = v___x_4320_;
                                        v___y_4192_ = v___x_4324_;
                                        state = 5;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v___y_4259_);
                                        v___x_4325_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__28;
                                        v___y_4181_ = v___y_4255_;
                                        v___y_4182_ = v___x_4319_;
                                        v___y_4183_ = v_pre_x3f_4261_;
                                        v___y_4184_ = v___x_4321_;
                                        v___y_4185_ = v___y_4263_;
                                        v___y_4186_ = v___x_4316_;
                                        v___y_4187_ = v___x_4322_;
                                        v___y_4188_ = v___x_4318_;
                                        v___y_4189_ = v___y_4257_;
                                        v___y_4190_ = v___x_4309_;
                                        v___y_4191_ = v___x_4320_;
                                        v___y_4192_ = v___x_4325_;
                                        state = 5;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_4265_);
                    v___x_4326_ = leanh::lean_unsigned_to_nat(5);
                    v___x_4327_ = l_Lean_Syntax_getArg(v_x_4045_, v___x_4326_);
                    v___x_4328_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__27;
                    leanh::lean_inc(v___x_4327_);
                    v___x_4329_ = l_Lean_Syntax_isOfKind(v___x_4327_, v___x_4328_);
                    if v___x_4329_ == 0 {
                        leanh::lean_dec(v___x_4327_);
                        leanh::lean_dec(v_pre_x3f_4261_);
                        leanh::lean_dec(v___y_4259_);
                        leanh::lean_dec(v___y_4257_);
                        leanh::lean_dec(v_x_4045_);
                        v___x_4330_ = leanh::lean_box(1);
                        v___x_4331_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_4331_, 0, v___x_4330_);
                        leanh::lean_ctor_set(v___x_4331_, 1, v___y_4263_);
                        return v___x_4331_;
                    } else {
                        v_ref_4332_ = leanh::lean_ctor_get(v___y_4262_, 5);
                        v___x_4333_ = leanh::lean_unsigned_to_nat(7);
                        v___x_4334_ = l_Lean_Syntax_getArg(v_x_4045_, v___x_4333_);
                        v___x_4335_ = leanh::lean_unsigned_to_nat(10);
                        v___x_4336_ = l_Lean_Syntax_getArg(v_x_4045_, v___x_4335_);
                        leanh::lean_dec(v_x_4045_);
                        v___x_4337_ = 0;
                        v___x_4338_ = l_Lean_SourceInfo_fromRef(v_ref_4332_, v___x_4337_);
                        v___x_4339_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__21;
                        v___x_4340_ = l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__1;
                        v___x_4341_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27), core::ptr::addr_of_mut!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27_once), _init_l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27);
                        if leanh::lean_obj_tag(v___y_4259_) == 1 {
                            v_val_4342_ = leanh::lean_ctor_get(v___y_4259_, 0);
                            leanh::lean_inc(v_val_4342_);
                            leanh::lean_dec_ref_known(v___y_4259_, 1);
                            v___x_4343_ = l_Array_mkArray1___redArg(v_val_4342_);
                            v___y_4218_ = v___y_4255_;
                            v___y_4219_ = v___x_4341_;
                            v___y_4220_ = v___x_4327_;
                            v___y_4221_ = v___x_4338_;
                            v___y_4222_ = v_pre_x3f_4261_;
                            v___y_4223_ = v___y_4263_;
                            v___y_4224_ = v___x_4336_;
                            v___y_4225_ = v___x_4334_;
                            v___y_4226_ = v___y_4257_;
                            v___y_4227_ = v___x_4339_;
                            v___y_4228_ = v___x_4340_;
                            v___y_4229_ = v___x_4343_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_dec(v___y_4259_);
                            v___x_4344_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__28;
                            v___y_4218_ = v___y_4255_;
                            v___y_4219_ = v___x_4341_;
                            v___y_4220_ = v___x_4327_;
                            v___y_4221_ = v___x_4338_;
                            v___y_4222_ = v_pre_x3f_4261_;
                            v___y_4223_ = v___y_4263_;
                            v___y_4224_ = v___x_4336_;
                            v___y_4225_ = v___x_4334_;
                            v___y_4226_ = v___y_4257_;
                            v___y_4227_ = v___x_4339_;
                            v___y_4228_ = v___x_4340_;
                            v___y_4229_ = v___x_4344_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            8 => {
                v___x_4349_ = leanh::lean_unsigned_to_nat(1);
                v___x_4350_ = l_Lean_Syntax_getArg(v_x_4045_, v___x_4349_);
                v___x_4351_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__5;
                v___x_4352_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__2;
                leanh::lean_inc(v___x_4350_);
                v___x_4353_ = l_Lean_Syntax_isOfKind(v___x_4350_, v___x_4352_);
                if v___x_4353_ == 0 {
                    leanh::lean_dec(v___x_4350_);
                    leanh::lean_dec(v_doc_x3f_4346_);
                    leanh::lean_dec(v_x_4045_);
                    v___x_4354_ = leanh::lean_box(1);
                    v___x_4355_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4355_, 0, v___x_4354_);
                    leanh::lean_ctor_set(v___x_4355_, 1, v___y_4348_);
                    return v___x_4355_;
                } else {
                    v___x_4356_ = leanh::lean_unsigned_to_nat(2);
                    v___x_4357_ = leanh::lean_unsigned_to_nat(3);
                    v___x_4358_ = l_Lean_Syntax_getArg(v_x_4045_, v___x_4357_);
                    v___x_4359_ = l_Lean_Syntax_isNone(v___x_4358_);
                    if v___x_4359_ == 0 {
                        leanh::lean_inc(v___x_4358_);
                        v___x_4360_ = l_Lean_Syntax_matchesNull(v___x_4358_, v___x_4349_);
                        if v___x_4360_ == 0 {
                            leanh::lean_dec(v___x_4358_);
                            leanh::lean_dec(v___x_4350_);
                            leanh::lean_dec(v_doc_x3f_4346_);
                            leanh::lean_dec(v_x_4045_);
                            v___x_4361_ = leanh::lean_box(1);
                            v___x_4362_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_4362_, 0, v___x_4361_);
                            leanh::lean_ctor_set(v___x_4362_, 1, v___y_4348_);
                            return v___x_4362_;
                        } else {
                            v_pre_x3f_4363_ = l_Lean_Syntax_getArg(v___x_4358_, v___x_4141_);
                            leanh::lean_dec(v___x_4358_);
                            v___x_4364_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_4364_, 0, v_pre_x3f_4363_);
                            v___y_4255_ = v___x_4351_;
                            v___y_4256_ = v___x_4349_;
                            v___y_4257_ = v___x_4350_;
                            v___y_4258_ = v___x_4356_;
                            v___y_4259_ = v_doc_x3f_4346_;
                            v___y_4260_ = v___x_4357_;
                            v_pre_x3f_4261_ = v___x_4364_;
                            v___y_4262_ = v___y_4347_;
                            v___y_4263_ = v___y_4348_;
                            state = 7;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_4358_);
                        v___x_4365_ = leanh::lean_box(0);
                        v___y_4255_ = v___x_4351_;
                        v___y_4256_ = v___x_4349_;
                        v___y_4257_ = v___x_4350_;
                        v___y_4258_ = v___x_4356_;
                        v___y_4259_ = v_doc_x3f_4346_;
                        v___y_4260_ = v___x_4357_;
                        v_pre_x3f_4261_ = v___x_4365_;
                        v___y_4262_ = v___y_4347_;
                        v___y_4263_ = v___y_4348_;
                        state = 7;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d____1___boxed(
    mut v_x_4379_: *mut leanh::LeanObject,
    mut v_a_4380_: *mut leanh::LeanObject,
    mut v_a_4381_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4382_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4382_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d____1(v_x_4379_, v_a_4380_, v_a_4381_);
    leanh::lean_dec_ref(v_a_4380_);
    return v_res_4382_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Simproc(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Tactics(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Meta_Defs(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Simproc(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Init_Data_ToString_Name(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d__ =
        _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d__();
    leanh::lean_mark_persistent(
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d__,
    );
    l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d__ =
        _init_l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d__();
    leanh::lean_mark_persistent(
        l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d__,
    );
    l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d__ =
        _init_l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d__();
    leanh::lean_mark_persistent(
        l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d__,
    );
    l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d__ =
        _init_l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d__();
    leanh::lean_mark_persistent(
        l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d__,
    );
    l_Lean_Parser_Attr_simprocAttr = _init_l_Lean_Parser_Attr_simprocAttr();
    leanh::lean_mark_persistent(l_Lean_Parser_Attr_simprocAttr);
    l_Lean_Parser_Attr_sevalprocAttr = _init_l_Lean_Parser_Attr_sevalprocAttr();
    leanh::lean_mark_persistent(l_Lean_Parser_Attr_sevalprocAttr);
    l_Lean_Parser_Attr_simprocBuiltinAttr = _init_l_Lean_Parser_Attr_simprocBuiltinAttr();
    leanh::lean_mark_persistent(l_Lean_Parser_Attr_simprocBuiltinAttr);
    l_Lean_Parser_Attr_sevalprocBuiltinAttr = _init_l_Lean_Parser_Attr_sevalprocBuiltinAttr();
    leanh::lean_mark_persistent(l_Lean_Parser_Attr_sevalprocBuiltinAttr);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Simproc(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_ToString_Name(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Tactics(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Meta_Defs(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Simproc(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Simproc(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Simproc(builtin);
}