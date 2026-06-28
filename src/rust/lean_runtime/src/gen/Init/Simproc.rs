// Lean compiler output
// Module: Init.Simproc
// Imports: Init.Data.ToString.Name Init.Tactics Init.Meta.Defs
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::ToString::Name::{
    initialize_Init_Data_ToString_Name, l_Lean_Name_toString,
    meta_initialize_Init_Data_ToString_Name,
};
use crate::r#gen::Init::Meta::Defs::{
    initialize_Init_Meta_Defs, l_Lean_Syntax_TSepArray_getElems___redArg, l_Lean_Syntax_isNone,
    l_Lean_TSyntax_getId, l_Lean_mkOptionalNode, lean_mk_syntax_ident, lean_name_append_after,
    runtime_initialize_Init_Meta_Defs,
};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Array_mkArray1___redArg, l_Lean_Name_append, l_Lean_Name_mkStr1,
    l_Lean_Name_mkStr2, l_Lean_Name_mkStr3, l_Lean_Name_mkStr4, l_Lean_SourceInfo_fromRef,
    l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_matchesIdent, l_Lean_Syntax_matchesNull, l_Lean_Syntax_node1,
    l_Lean_Syntax_node2, l_Lean_Syntax_node3, l_Lean_Syntax_node4, l_Lean_Syntax_node5,
    l_Lean_Syntax_node7, l_Lean_Syntax_node8, l_Lean_mkAtom,
};
use crate::r#gen::Init::Tactics::{
    initialize_Init_Tactics, l_Lean_Parser_Tactic_simpPost, l_Lean_Parser_Tactic_simpPre,
    runtime_initialize_Init_Tactics,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_size, lean_array_uget_borrowed};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_dec_lt};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_push, lean_mk_empty_array_with_capacity, lean_name_eq,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_set,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent,
    lean_obj_once, lean_obj_tag, lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value
) as *mut LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value
) as *mut LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__2_value: LeanStringObject<29> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 29, m_capacity: 29, m_length: 28, m_data: [99, 111, 109, 109, 97, 110, 100, 95, 95, 83, 105, 109, 112, 114, 111, 99, 95, 95, 91, 95, 93, 95, 40, 95, 41, 58, 61, 95, 0]};
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__2_value
) as *mut LeanObject;
static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__2_value) as *mut LeanObject,667243668184828663 as *mut LeanObject] };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__3_value
) as *mut LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__4_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [97, 110, 100, 116, 104, 101, 110, 0]};
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__4_value
) as *mut LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__4_value) as *mut LeanObject,12571085391447129896 as *mut LeanObject] };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value
) as *mut LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__6_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [111, 112, 116, 105, 111, 110, 97, 108, 0]};
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__6_value
) as *mut LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__6_value) as *mut LeanObject,18170484695678750185 as *mut LeanObject] };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__7_value
) as *mut LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__8_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [100, 111, 99, 67, 111, 109, 109, 101, 110, 116, 0]};
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__8_value
) as *mut LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__9_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__8_value) as *mut LeanObject,3961966953292576997 as *mut LeanObject] };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__9:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__9_value
) as *mut LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__10_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__9_value) as *mut LeanObject] };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__10:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__10_value
) as *mut LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__7_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__10_value) as *mut LeanObject] };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11_value
) as *mut LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__12_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [97, 116, 116, 114, 75, 105, 110, 100, 0]};
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__12:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__12_value
) as *mut LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__13_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__12_value) as *mut LeanObject,16084902538479694224 as *mut LeanObject] };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__13:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__13_value
) as *mut LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__14_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__13_value) as *mut LeanObject] };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__14:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__14_value
) as *mut LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__15_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__14_value) as *mut LeanObject] };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__15:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__15_value
) as *mut LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__16_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [115, 105, 109, 112, 114, 111, 99, 32, 0]};
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__16:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__16_value
) as *mut LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__17_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__16_value) as *mut LeanObject] };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__17:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__17_value
) as *mut LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__18_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__15_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__17_value) as *mut LeanObject] };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__18:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__18_value
) as *mut LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__19_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [111, 114, 101, 108, 115, 101, 0]};
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__19:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__19_value
) as *mut LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__20_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__19_value) as *mut LeanObject,393173242845875278 as *mut LeanObject] };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__20:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__20_value
) as *mut LeanObject;
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__21_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__21:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__23_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__23:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__24_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [91, 0]};
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__24:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__24_value
) as *mut LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__25_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__24_value) as *mut LeanObject] };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__25:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__25_value
) as *mut LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__26_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__26:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__26_value
) as *mut LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__27_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__26_value) as *mut LeanObject,5117844058249666356 as *mut LeanObject] };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__27:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__27_value
) as *mut LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__28_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__27_value) as *mut LeanObject] };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__28:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__28_value
) as *mut LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__29_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [44, 0]};
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__29:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__29_value
) as *mut LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__30_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [44, 32, 0]};
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__30:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__30_value
) as *mut LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__31_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__30_value) as *mut LeanObject] };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__31:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__31_value
) as *mut LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__32_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 8) as u16, other: 3, tag: 10 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__28_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__29_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__31_value) as *mut LeanObject,0 as *mut LeanObject] };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__32:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__32_value
) as *mut LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__33_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__25_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__32_value) as *mut LeanObject] };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__33:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__33_value
) as *mut LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__34_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__34:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__34_value
) as *mut LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__35_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__34_value) as *mut LeanObject] };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__35:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__35_value
) as *mut LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__36_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__33_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__35_value) as *mut LeanObject] };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__36:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__36_value
) as *mut LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__37_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__7_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__36_value) as *mut LeanObject] };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__37:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__37_value
) as *mut LeanObject;
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__38_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__38:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__39_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__39:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__40_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [32, 40, 0]};
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__40:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__40_value
) as *mut LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__41_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__40_value) as *mut LeanObject] };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__41:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__41_value
) as *mut LeanObject;
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__42_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__42:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__43_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 101, 114, 109, 0]};
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__43:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__43_value
) as *mut LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__44_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__43_value) as *mut LeanObject,8609355255726335675 as *mut LeanObject] };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__44:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__44_value
) as *mut LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__45_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 7 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__44_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__45:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__45_value
) as *mut LeanObject;
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__46_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__46:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__47_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__47:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__47_value
) as *mut LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__48_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__47_value) as *mut LeanObject] };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__48:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__48_value
) as *mut LeanObject;
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__49_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__49:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__50_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [32, 58, 61, 32, 0]};
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__50:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__50_value
) as *mut LeanObject;
pub static l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__51_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__50_value) as *mut LeanObject] };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__51:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__51_value
) as *mut LeanObject;
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__52_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__52:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__53_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__53:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__54_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__54:
    *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d__:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value: LeanStringObject<30> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 30, m_capacity: 30, m_length: 29, m_data: [99, 111, 109, 109, 97, 110, 100, 95, 95, 68, 115, 105, 109, 112, 114, 111, 99, 95, 95, 91, 95, 93, 95, 40, 95, 41, 58, 61, 95, 0]};
static mut l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value
) as *mut LeanObject;
static l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value) as *mut LeanObject,7150602757519970396 as *mut LeanObject] };
static mut l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value
) as *mut LeanObject;
pub static l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__2_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [100, 115, 105, 109, 112, 114, 111, 99, 32, 0]};
static mut l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__2_value
) as *mut LeanObject;
pub static l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__3_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__2_value) as *mut LeanObject] };
static mut l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__3_value
) as *mut LeanObject;
pub static l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__15_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__3_value) as *mut LeanObject] };
static mut l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__4_value
) as *mut LeanObject;
static mut l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__6:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__7:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__8_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__8:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__9:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__10_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__10:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__12_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__12:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__13:
    *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d__:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__0_value:
    LeanStringObject<28> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__0_value
) as *mut LeanObject;
static l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__1_value:
    LeanCtorObject<3> = LeanCtorObject {
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
            l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__1_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__0_value
        ) as *mut LeanObject,
        18031830130498964246 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__1_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__2_value:
    LeanStringObject<14> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__2_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__3_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__2_value
    ) as *mut LeanObject],
};
static mut l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__3_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__3_value) as *mut LeanObject] };
static mut l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__4_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__4_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__28_value) as *mut LeanObject] };
static mut l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__5_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__5_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__41_value) as *mut LeanObject] };
static mut l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__6_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__6_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__45_value) as *mut LeanObject] };
static mut l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__7_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__7_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__48_value) as *mut LeanObject] };
static mut l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__8_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__9_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__8_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__51_value) as *mut LeanObject] };
static mut l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__9:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__9_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__10_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__9_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__45_value) as *mut LeanObject] };
static mut l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__10:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__10_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__11_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__1_value
        ) as *mut LeanObject,
        (((1022 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__10_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__11:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__11_value
) as *mut LeanObject;
pub static mut l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d__: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__11_value
)
    as *mut LeanObject;
pub static l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__0_value:
    LeanStringObject<29> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__0_value
) as *mut LeanObject;
static l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__1_value:
    LeanCtorObject<3> = LeanCtorObject {
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
            l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__1_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__0_value
        ) as *mut LeanObject,
        5776010155899880851 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__1_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__2_value:
    LeanStringObject<15> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__2_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__3_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__2_value
    ) as *mut LeanObject],
};
static mut l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__3_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__3_value) as *mut LeanObject] };
static mut l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__4_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__4_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__28_value) as *mut LeanObject] };
static mut l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__5_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__5_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__41_value) as *mut LeanObject] };
static mut l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__6_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__6_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__45_value) as *mut LeanObject] };
static mut l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__7_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__7_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__48_value) as *mut LeanObject] };
static mut l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__8_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__9_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__8_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__51_value) as *mut LeanObject] };
static mut l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__9:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__9_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__10_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__9_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__45_value) as *mut LeanObject] };
static mut l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__10:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__10_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__11_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__1_value
        ) as *mut LeanObject,
        (((1022 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__10_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__11:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__11_value
) as *mut LeanObject;
pub static mut l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d__: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__11_value
)
    as *mut LeanObject;
pub static l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value: LeanStringObject<37> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [99, 111, 109, 109, 97, 110, 100, 95, 95, 66, 117, 105, 108, 116, 105, 110, 95, 115, 105, 109, 112, 114, 111, 99, 95, 95, 91, 95, 93, 95, 40, 95, 41, 58, 61, 95, 0]};
static mut l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value) as *mut LeanObject;
static l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value) as *mut LeanObject,12128620401598718473 as *mut LeanObject] };
static mut l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__2_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [98, 117, 105, 108, 116, 105, 110, 95, 115, 105, 109, 112, 114, 111, 99, 32, 0]};
static mut l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__3_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__2_value) as *mut LeanObject] };
static mut l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__15_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__3_value) as *mut LeanObject] };
static mut l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__4_value) as *mut LeanObject;
static mut l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__7: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__8_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__8: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__9: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__10_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__10: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__12_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__12: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__13: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d__:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value: LeanStringObject<38> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 38, m_capacity: 38, m_length: 37, m_data: [99, 111, 109, 109, 97, 110, 100, 95, 95, 66, 117, 105, 108, 116, 105, 110, 95, 100, 115, 105, 109, 112, 114, 111, 99, 95, 95, 91, 95, 93, 95, 40, 95, 41, 58, 61, 95, 0]};
static mut l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value) as *mut LeanObject;
static l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value) as *mut LeanObject,2656510369972815120 as *mut LeanObject] };
static mut l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__2_value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [98, 117, 105, 108, 116, 105, 110, 95, 100, 115, 105, 109, 112, 114, 111, 99, 32, 0]};
static mut l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__3_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__2_value) as *mut LeanObject] };
static mut l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__15_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__3_value) as *mut LeanObject] };
static mut l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__4_value) as *mut LeanObject;
static mut l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__7: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__8_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__8: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__9: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__10_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__10: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__12_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__12: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__13: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d__:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__0_value: LeanStringObject<36> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 36, m_capacity: 36, m_length: 35, m_data: [99, 111, 109, 109, 97, 110, 100, 95, 66, 117, 105, 108, 116, 105, 110, 95, 115, 105, 109, 112, 114, 111, 99, 95, 100, 101, 99, 108, 95, 40, 95, 41, 58, 61, 95, 0]};
static mut l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__0_value
) as *mut LeanObject;
static l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__0_value) as *mut LeanObject,14561357251485234313 as *mut LeanObject] };
static mut l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__1_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__2_value: LeanStringObject<22> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [98, 117, 105, 108, 116, 105, 110, 95, 115, 105, 109, 112, 114, 111, 99, 95, 100, 101, 99, 108, 32, 0]};
static mut l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__2_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__3_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__2_value) as *mut LeanObject] };
static mut l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__3_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__3_value) as *mut LeanObject] };
static mut l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__4_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__4_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__28_value) as *mut LeanObject] };
static mut l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__5_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__5_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__41_value) as *mut LeanObject] };
static mut l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__6_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__6_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__45_value) as *mut LeanObject] };
static mut l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__7_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__7_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__48_value) as *mut LeanObject] };
static mut l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__8_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__9_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__8_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__51_value) as *mut LeanObject] };
static mut l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__9:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__9_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__10_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__9_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__45_value) as *mut LeanObject] };
static mut l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__10:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__10_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__11_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__1_value) as *mut LeanObject,((( 1022 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__10_value) as *mut LeanObject] };
static mut l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__11:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__11_value
) as *mut LeanObject;
pub static mut l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d__:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__11_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__0_value: LeanStringObject<37> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [99, 111, 109, 109, 97, 110, 100, 95, 66, 117, 105, 108, 116, 105, 110, 95, 100, 115, 105, 109, 112, 114, 111, 99, 95, 100, 101, 99, 108, 95, 40, 95, 41, 58, 61, 95, 0]};
static mut l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__0_value
) as *mut LeanObject;
static l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__0_value) as *mut LeanObject,8930413136233488908 as *mut LeanObject] };
static mut l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__1_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__2_value: LeanStringObject<23> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [98, 117, 105, 108, 116, 105, 110, 95, 100, 115, 105, 109, 112, 114, 111, 99, 95, 100, 101, 99, 108, 32, 0]};
static mut l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__2_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__3_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__2_value) as *mut LeanObject] };
static mut l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__3_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__3_value) as *mut LeanObject] };
static mut l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__4_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__4_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__28_value) as *mut LeanObject] };
static mut l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__5_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__5_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__41_value) as *mut LeanObject] };
static mut l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__6_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__6_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__45_value) as *mut LeanObject] };
static mut l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__7_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__7_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__48_value) as *mut LeanObject] };
static mut l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__8_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__9_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__8_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__51_value) as *mut LeanObject] };
static mut l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__9:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__9_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__10_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__9_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__45_value) as *mut LeanObject] };
static mut l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__10:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__10_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__11_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__1_value) as *mut LeanObject,((( 1022 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__10_value) as *mut LeanObject] };
static mut l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__11:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__11_value
) as *mut LeanObject;
pub static mut l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d__:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__11_value
) as *mut LeanObject;
pub static l_Lean_Parser_simprocPattern___closed__0_value: LeanStringObject<15> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Parser_simprocPattern___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_simprocPattern___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_simprocPattern___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser_simprocPattern___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_simprocPattern___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l_Lean_Parser_simprocPattern___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_simprocPattern___closed__1_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_simprocPattern___closed__0_value) as *mut LeanObject,
        18201466311632407230 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_simprocPattern___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_simprocPattern___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_simprocPattern___closed__2_value: LeanStringObject<18> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Parser_simprocPattern___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_simprocPattern___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_simprocPattern___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_simprocPattern___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_simprocPattern___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_simprocPattern___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_simprocPattern___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_simprocPattern___closed__3_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__45_value) as *mut LeanObject] };
static mut l_Lean_Parser_simprocPattern___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_simprocPattern___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_simprocPattern___closed__5_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Parser_simprocPattern___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_simprocPattern___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_simprocPattern___closed__6_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_simprocPattern___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_simprocPattern___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_simprocPattern___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_simprocPattern___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_simprocPattern___closed__4_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_simprocPattern___closed__6_value) as *mut LeanObject] };
static mut l_Lean_Parser_simprocPattern___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_simprocPattern___closed__7_value) as *mut LeanObject;
pub static l_Lean_Parser_simprocPattern___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_simprocPattern___closed__7_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__28_value) as *mut LeanObject] };
static mut l_Lean_Parser_simprocPattern___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_simprocPattern___closed__8_value) as *mut LeanObject;
pub static l_Lean_Parser_simprocPattern___closed__9_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_simprocPattern___closed__1_value) as *mut LeanObject,
        (((1022 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_simprocPattern___closed__8_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_simprocPattern___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_simprocPattern___closed__9_value) as *mut LeanObject;
pub static mut l_Lean_Parser_simprocPattern: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_simprocPattern___closed__9_value) as *mut LeanObject;
pub static l_Lean_Parser_simprocPatternBuiltin___closed__0_value: LeanStringObject<22> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 22,
        m_capacity: 22,
        m_length: 21,
        m_data: [
            115, 105, 109, 112, 114, 111, 99, 80, 97, 116, 116, 101, 114, 110, 66, 117, 105, 108,
            116, 105, 110, 0,
        ],
    };
static mut l_Lean_Parser_simprocPatternBuiltin___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_simprocPatternBuiltin___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_simprocPatternBuiltin___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser_simprocPatternBuiltin___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_simprocPatternBuiltin___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l_Lean_Parser_simprocPatternBuiltin___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_simprocPatternBuiltin___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_simprocPatternBuiltin___closed__0_value)
                as *mut LeanObject,
            10608001774515379730 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_simprocPatternBuiltin___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_simprocPatternBuiltin___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_simprocPatternBuiltin___closed__2_value: LeanStringObject<26> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 26,
        m_capacity: 26,
        m_length: 25,
        m_data: [
            98, 117, 105, 108, 116, 105, 110, 95, 115, 105, 109, 112, 114, 111, 99, 95, 112, 97,
            116, 116, 101, 114, 110, 37, 32, 0,
        ],
    };
static mut l_Lean_Parser_simprocPatternBuiltin___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_simprocPatternBuiltin___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_simprocPatternBuiltin___closed__3_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_simprocPatternBuiltin___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_simprocPatternBuiltin___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_simprocPatternBuiltin___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_simprocPatternBuiltin___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_simprocPatternBuiltin___closed__3_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__45_value) as *mut LeanObject] };
static mut l_Lean_Parser_simprocPatternBuiltin___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_simprocPatternBuiltin___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_simprocPatternBuiltin___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_simprocPatternBuiltin___closed__4_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_simprocPattern___closed__6_value) as *mut LeanObject] };
static mut l_Lean_Parser_simprocPatternBuiltin___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_simprocPatternBuiltin___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_simprocPatternBuiltin___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_simprocPatternBuiltin___closed__5_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__28_value) as *mut LeanObject] };
static mut l_Lean_Parser_simprocPatternBuiltin___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_simprocPatternBuiltin___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_simprocPatternBuiltin___closed__7_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_simprocPatternBuiltin___closed__1_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_simprocPatternBuiltin___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_simprocPatternBuiltin___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_simprocPatternBuiltin___closed__7_value) as *mut LeanObject;
pub static mut l_Lean_Parser_simprocPatternBuiltin: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_simprocPatternBuiltin___closed__7_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_simprocAttr___closed__0_value: LeanStringObject<5> =
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
        m_data: [65, 116, 116, 114, 0],
    };
static mut l_Lean_Parser_Attr_simprocAttr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_simprocAttr___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_simprocAttr___closed__1_value: LeanStringObject<12> =
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
        m_data: [115, 105, 109, 112, 114, 111, 99, 65, 116, 116, 114, 0],
    };
static mut l_Lean_Parser_Attr_simprocAttr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_simprocAttr___closed__1_value) as *mut LeanObject;
static l_Lean_Parser_Attr_simprocAttr___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser_Attr_simprocAttr___closed__2_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Attr_simprocAttr___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Parser_Attr_simprocAttr___closed__2_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_simprocAttr___closed__2_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_simprocAttr___closed__0_value) as *mut LeanObject,
        4584992172905639687 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Attr_simprocAttr___closed__2_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_simprocAttr___closed__2_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_simprocAttr___closed__1_value) as *mut LeanObject,
        11850131029335478859 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_simprocAttr___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_simprocAttr___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_simprocAttr___closed__3_value: LeanStringObject<8> =
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
        m_data: [115, 105, 109, 112, 114, 111, 99, 0],
    };
static mut l_Lean_Parser_Attr_simprocAttr___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_simprocAttr___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_simprocAttr___closed__4_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_simprocAttr___closed__3_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_simprocAttr___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_simprocAttr___closed__4_value) as *mut LeanObject;
static mut l_Lean_Parser_Attr_simprocAttr___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_simprocAttr___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_simprocAttr___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_simprocAttr___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_Attr_simprocAttr: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Attr_sevalprocAttr___closed__0_value: LeanStringObject<14> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Parser_Attr_sevalprocAttr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_sevalprocAttr___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Attr_sevalprocAttr___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser_Attr_sevalprocAttr___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Attr_sevalprocAttr___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Parser_Attr_sevalprocAttr___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_sevalprocAttr___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_simprocAttr___closed__0_value)
                as *mut LeanObject,
            4584992172905639687 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Attr_sevalprocAttr___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_sevalprocAttr___closed__1_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_sevalprocAttr___closed__0_value) as *mut LeanObject,
        14768295711661951876 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_sevalprocAttr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_sevalprocAttr___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_sevalprocAttr___closed__2_value: LeanStringObject<10> =
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
        m_data: [115, 101, 118, 97, 108, 112, 114, 111, 99, 0],
    };
static mut l_Lean_Parser_Attr_sevalprocAttr___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_sevalprocAttr___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_sevalprocAttr___closed__3_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_sevalprocAttr___closed__2_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_sevalprocAttr___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_sevalprocAttr___closed__3_value) as *mut LeanObject;
static mut l_Lean_Parser_Attr_sevalprocAttr___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_sevalprocAttr___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_sevalprocAttr___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_sevalprocAttr___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_Attr_sevalprocAttr: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Attr_simprocBuiltinAttr___closed__0_value: LeanStringObject<19> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 19,
        m_capacity: 19,
        m_length: 18,
        m_data: [
            115, 105, 109, 112, 114, 111, 99, 66, 117, 105, 108, 116, 105, 110, 65, 116, 116, 114,
            0,
        ],
    };
static mut l_Lean_Parser_Attr_simprocBuiltinAttr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_simprocBuiltinAttr___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Attr_simprocBuiltinAttr___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser_Attr_simprocBuiltinAttr___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Attr_simprocBuiltinAttr___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Parser_Attr_simprocBuiltinAttr___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_simprocBuiltinAttr___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_simprocAttr___closed__0_value)
                as *mut LeanObject,
            4584992172905639687 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Attr_simprocBuiltinAttr___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_simprocBuiltinAttr___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_simprocBuiltinAttr___closed__0_value)
                as *mut LeanObject,
            18242174535284492835 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_simprocBuiltinAttr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_simprocBuiltinAttr___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_simprocBuiltinAttr___closed__2_value: LeanStringObject<16> =
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
            98, 117, 105, 108, 116, 105, 110, 95, 115, 105, 109, 112, 114, 111, 99, 0,
        ],
    };
static mut l_Lean_Parser_Attr_simprocBuiltinAttr___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_simprocBuiltinAttr___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_simprocBuiltinAttr___closed__3_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_simprocBuiltinAttr___closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_simprocBuiltinAttr___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_simprocBuiltinAttr___closed__3_value) as *mut LeanObject;
static mut l_Lean_Parser_Attr_simprocBuiltinAttr___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_simprocBuiltinAttr___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_simprocBuiltinAttr___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_simprocBuiltinAttr___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Attr_simprocBuiltinAttr: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__0_value: LeanStringObject<21> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            115, 101, 118, 97, 108, 112, 114, 111, 99, 66, 117, 105, 108, 116, 105, 110, 65, 116,
            116, 114, 0,
        ],
    };
static mut l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__0_value)
        as *mut LeanObject;
static l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_simprocAttr___closed__0_value)
                as *mut LeanObject,
            4584992172905639687 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__0_value)
                as *mut LeanObject,
            14943976816696743720 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__2_value: LeanStringObject<18> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__3_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__3_value)
        as *mut LeanObject;
static mut l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Attr_sevalprocBuiltinAttr: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [109, 101, 116, 97, 0]};
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__1_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 0]};
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__2_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [100, 101, 102, 0]};
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__3_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [100, 101, 99, 108, 73, 100, 0]};
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__4_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [111, 112, 116, 68, 101, 99, 108, 83, 105, 103, 0]};
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__5_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__6_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [116, 121, 112, 101, 83, 112, 101, 99, 0]};
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__6_value) as *mut LeanObject;
static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__7_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__7_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__7_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__7_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__7_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__5_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__7_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__6_value) as *mut LeanObject,4498178684837002829 as *mut LeanObject] };
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__7: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__7_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__8_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [58, 0]};
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__8_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__9_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [100, 101, 99, 108, 86, 97, 108, 83, 105, 109, 112, 108, 101, 0]};
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__9: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__9_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__10_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [58, 61, 0]};
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__10_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__11_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [84, 101, 114, 109, 105, 110, 97, 116, 105, 111, 110, 0]};
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__11: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__11_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__12_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 117, 102, 102, 105, 120, 0]};
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__12_value) as *mut LeanObject;
static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__13_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__13_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__13_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__13_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__13_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__11_value) as *mut LeanObject,7625897890118033792 as *mut LeanObject] };
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__13_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__13_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__12_value) as *mut LeanObject,8715860392475343861 as *mut LeanObject] };
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__13: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__13_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__14_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 105, 109, 112, 114, 111, 99, 95, 112, 97, 116, 116, 101, 114, 110, 37, 0]};
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__14: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__14_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__15_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [61, 62, 0]};
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__15: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__15_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__16_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__16: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__16_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__17_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [83, 105, 109, 112, 0]};
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__17: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__17_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__18_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [83, 105, 109, 112, 114, 111, 99, 0]};
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__18: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__18_value) as *mut LeanObject;
static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__19_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__19_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__19_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__16_value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__19_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__19_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__17_value) as *mut LeanObject,492087047182689846 as *mut LeanObject] };
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__19_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__19_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__18_value) as *mut LeanObject,18418687298610896914 as *mut LeanObject] };
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__19: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__19_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__20_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__20: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__20_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__21_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__20_value) as *mut LeanObject,9855511589286918680 as *mut LeanObject] };
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__21: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__21_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__22_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [67, 111, 109, 109, 97, 110, 100, 0]};
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__22: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__22_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__23_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 0]};
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__23: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__23_value) as *mut LeanObject;
static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__24_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__24_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__24_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__24_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__24_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__22_value) as *mut LeanObject,17342580262104060118 as *mut LeanObject] };
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__24_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__24_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__23_value) as *mut LeanObject,8497769072906204829 as *mut LeanObject] };
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__24: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__24_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__25_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [100, 101, 99, 108, 77, 111, 100, 105, 102, 105, 101, 114, 115, 0]};
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__25: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__25_value) as *mut LeanObject;
static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__26_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__26_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__26_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__26_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__26_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__22_value) as *mut LeanObject,17342580262104060118 as *mut LeanObject] };
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__26_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__26_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__25_value) as *mut LeanObject,14557702332550915328 as *mut LeanObject] };
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__26: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__26_value) as *mut LeanObject;
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__28_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__28: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__28_value) as *mut LeanObject;
static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__29_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__29_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__29_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__29_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__29_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__22_value) as *mut LeanObject,17342580262104060118 as *mut LeanObject] };
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__29_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__29_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__8_value) as *mut LeanObject,9063780239635860524 as *mut LeanObject] };
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__29: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__29_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Dsimproc__decl___x28___x29_x3a_x3d____1___closed__0_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [68, 83, 105, 109, 112, 114, 111, 99, 0]};
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Dsimproc__decl___x28___x29_x3a_x3d____1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Dsimproc__decl___x28___x29_x3a_x3d____1___closed__0_value) as *mut LeanObject;
static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Dsimproc__decl___x28___x29_x3a_x3d____1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Dsimproc__decl___x28___x29_x3a_x3d____1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Dsimproc__decl___x28___x29_x3a_x3d____1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__16_value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Dsimproc__decl___x28___x29_x3a_x3d____1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Dsimproc__decl___x28___x29_x3a_x3d____1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__17_value) as *mut LeanObject,492087047182689846 as *mut LeanObject] };
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Dsimproc__decl___x28___x29_x3a_x3d____1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Dsimproc__decl___x28___x29_x3a_x3d____1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Dsimproc__decl___x28___x29_x3a_x3d____1___closed__0_value) as *mut LeanObject,11597777601497588599 as *mut LeanObject] };
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Dsimproc__decl___x28___x29_x3a_x3d____1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Dsimproc__decl___x28___x29_x3a_x3d____1___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Builtin__simproc__decl___x28___x29_x3a_x3d____1___closed__0_value: LeanStringObject<25> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [98, 117, 105, 108, 116, 105, 110, 95, 115, 105, 109, 112, 114, 111, 99, 95, 112, 97, 116, 116, 101, 114, 110, 37, 0]};
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Builtin__simproc__decl___x28___x29_x3a_x3d____1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Builtin__simproc__decl___x28___x29_x3a_x3d____1___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__0_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [97, 116, 116, 114, 105, 98, 117, 116, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__0_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__22_value) as *mut LeanObject,17342580262104060118 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__0_value) as *mut LeanObject,11509420844586769999 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__2_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [97, 116, 116, 114, 73, 110, 115, 116, 97, 110, 99, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__2_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__5_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__2_value) as *mut LeanObject,7499624980761693169 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__3_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__4_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 105, 109, 112, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__4_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__4_value) as *mut LeanObject,13994041031692860867 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__5_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__6_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [115, 101, 118, 97, 108, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__6_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__6_value) as *mut LeanObject,10924716299523037131 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__7_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__8_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [95, 112, 114, 111, 99, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__8_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__9_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value) as *mut LeanObject,6907480769838958894 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__9_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__9_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Attr_simprocAttr___closed__0_value) as *mut LeanObject,16282038225239345418 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__9_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__10_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Attr_sevalprocAttr___closed__0_value) as *mut LeanObject,12361625276289109352 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__10_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__11_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Attr_simprocAttr___closed__1_value) as *mut LeanObject,18056956514849972255 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__11_value) as *mut LeanObject;
pub static l___private_Init_Simproc_0__Lean_Parser_mkAttributeCmds___closed__0_value:
    LeanArrayObject<0> = LeanArrayObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l___private_Init_Simproc_0__Lean_Parser_mkAttributeCmds___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___private_Init_Simproc_0__Lean_Parser_mkAttributeCmds___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [115, 105, 109, 112, 114, 111, 99, 95, 100, 101, 99, 108, 0]};
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__1_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__1_value) as *mut LeanObject;
static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__2_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__2_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__2_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__5_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__2_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__12_value) as *mut LeanObject,7983999284776576032 as *mut LeanObject] };
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [100, 115, 105, 109, 112, 114, 111, 99, 95, 100, 101, 99, 108, 0]};
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0_value: LeanStringObject<21> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [98, 117, 105, 108, 116, 105, 110, 95, 115, 105, 109, 112, 114, 111, 99, 95, 100, 101, 99, 108, 0]};
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0_value: LeanStringObject<22> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [98, 117, 105, 108, 116, 105, 110, 95, 100, 115, 105, 109, 112, 114, 111, 99, 95, 100, 101, 99, 108, 0]};
static mut l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0_value) as *mut LeanObject;
pub unsafe fn _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__21()
-> *mut LeanObject {
    let mut v___x_2232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut LeanObject = core::ptr::null_mut();
    v___x_2232_ = l_Lean_Parser_Tactic_simpPost;
    v___x_2233_ = l_Lean_Parser_Tactic_simpPre;
    v___x_2234_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__20;
    v___x_2235_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_2235_, 0, v___x_2234_);
    lean_ctor_set(v___x_2235_, 1, v___x_2233_);
    lean_ctor_set(v___x_2235_, 2, v___x_2232_);
    return v___x_2235_;
}
pub unsafe fn _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22()
-> *mut LeanObject {
    let mut v___x_2236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut LeanObject = core::ptr::null_mut();
    v___x_2236_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__21), core::ptr::addr_of_mut!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__21_once), _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__21);
    v___x_2237_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__7;
    v___x_2238_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_2238_, 0, v___x_2237_);
    lean_ctor_set(v___x_2238_, 1, v___x_2236_);
    return v___x_2238_;
}
pub unsafe fn _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__23()
-> *mut LeanObject {
    let mut v___x_2239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut LeanObject = core::ptr::null_mut();
    v___x_2239_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22), core::ptr::addr_of_mut!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22_once), _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22);
    v___x_2240_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__18;
    v___x_2241_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
    v___x_2242_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_2242_, 0, v___x_2241_);
    lean_ctor_set(v___x_2242_, 1, v___x_2240_);
    lean_ctor_set(v___x_2242_, 2, v___x_2239_);
    return v___x_2242_;
}
pub unsafe fn _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__38()
-> *mut LeanObject {
    let mut v___x_2274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut LeanObject = core::ptr::null_mut();
    v___x_2274_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__37;
    v___x_2275_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__23), core::ptr::addr_of_mut!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__23_once), _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__23);
    v___x_2276_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
    v___x_2277_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_2277_, 0, v___x_2276_);
    lean_ctor_set(v___x_2277_, 1, v___x_2275_);
    lean_ctor_set(v___x_2277_, 2, v___x_2274_);
    return v___x_2277_;
}
pub unsafe fn _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__39()
-> *mut LeanObject {
    let mut v___x_2278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut LeanObject = core::ptr::null_mut();
    v___x_2278_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__28;
    v___x_2279_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__38), core::ptr::addr_of_mut!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__38_once), _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__38);
    v___x_2280_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
    v___x_2281_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_2281_, 0, v___x_2280_);
    lean_ctor_set(v___x_2281_, 1, v___x_2279_);
    lean_ctor_set(v___x_2281_, 2, v___x_2278_);
    return v___x_2281_;
}
pub unsafe fn _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__42()
-> *mut LeanObject {
    let mut v___x_2285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut LeanObject = core::ptr::null_mut();
    v___x_2285_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__41;
    v___x_2286_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__39), core::ptr::addr_of_mut!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__39_once), _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__39);
    v___x_2287_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
    v___x_2288_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_2288_, 0, v___x_2287_);
    lean_ctor_set(v___x_2288_, 1, v___x_2286_);
    lean_ctor_set(v___x_2288_, 2, v___x_2285_);
    return v___x_2288_;
}
pub unsafe fn _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__46()
-> *mut LeanObject {
    let mut v___x_2295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: *mut LeanObject = core::ptr::null_mut();
    v___x_2295_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__45;
    v___x_2296_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__42), core::ptr::addr_of_mut!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__42_once), _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__42);
    v___x_2297_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
    v___x_2298_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_2298_, 0, v___x_2297_);
    lean_ctor_set(v___x_2298_, 1, v___x_2296_);
    lean_ctor_set(v___x_2298_, 2, v___x_2295_);
    return v___x_2298_;
}
pub unsafe fn _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__49()
-> *mut LeanObject {
    let mut v___x_2302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut LeanObject = core::ptr::null_mut();
    v___x_2302_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__48;
    v___x_2303_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__46), core::ptr::addr_of_mut!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__46_once), _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__46);
    v___x_2304_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
    v___x_2305_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_2305_, 0, v___x_2304_);
    lean_ctor_set(v___x_2305_, 1, v___x_2303_);
    lean_ctor_set(v___x_2305_, 2, v___x_2302_);
    return v___x_2305_;
}
pub unsafe fn _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__52()
-> *mut LeanObject {
    let mut v___x_2309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut LeanObject = core::ptr::null_mut();
    v___x_2309_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__51;
    v___x_2310_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__49), core::ptr::addr_of_mut!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__49_once), _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__49);
    v___x_2311_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
    v___x_2312_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_2312_, 0, v___x_2311_);
    lean_ctor_set(v___x_2312_, 1, v___x_2310_);
    lean_ctor_set(v___x_2312_, 2, v___x_2309_);
    return v___x_2312_;
}
pub unsafe fn _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__53()
-> *mut LeanObject {
    let mut v___x_2313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut LeanObject = core::ptr::null_mut();
    v___x_2313_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__45;
    v___x_2314_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__52), core::ptr::addr_of_mut!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__52_once), _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__52);
    v___x_2315_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
    v___x_2316_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_2316_, 0, v___x_2315_);
    lean_ctor_set(v___x_2316_, 1, v___x_2314_);
    lean_ctor_set(v___x_2316_, 2, v___x_2313_);
    return v___x_2316_;
}
pub unsafe fn _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__54()
-> *mut LeanObject {
    let mut v___x_2317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut LeanObject = core::ptr::null_mut();
    v___x_2317_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__53), core::ptr::addr_of_mut!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__53_once), _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__53);
    v___x_2318_ = lean_unsigned_to_nat(1022);
    v___x_2319_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__3;
    v___x_2320_ = lean_alloc_ctor(3, 3, (0) as u32);
    lean_ctor_set(v___x_2320_, 0, v___x_2319_);
    lean_ctor_set(v___x_2320_, 1, v___x_2318_);
    lean_ctor_set(v___x_2320_, 2, v___x_2317_);
    return v___x_2320_;
}
pub unsafe fn _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d__()
-> *mut LeanObject {
    let mut v___x_2321_: *mut LeanObject = core::ptr::null_mut();
    v___x_2321_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__54), core::ptr::addr_of_mut!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__54_once), _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__54);
    return v___x_2321_;
}
pub unsafe fn _init_l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5()
-> *mut LeanObject {
    let mut v___x_2334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut LeanObject = core::ptr::null_mut();
    v___x_2334_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22), core::ptr::addr_of_mut!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22_once), _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22);
    v___x_2335_ =
        l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__4;
    v___x_2336_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
    v___x_2337_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_2337_, 0, v___x_2336_);
    lean_ctor_set(v___x_2337_, 1, v___x_2335_);
    lean_ctor_set(v___x_2337_, 2, v___x_2334_);
    return v___x_2337_;
}
pub unsafe fn _init_l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__6()
-> *mut LeanObject {
    let mut v___x_2338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut LeanObject = core::ptr::null_mut();
    v___x_2338_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__37;
    v___x_2339_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5), core::ptr::addr_of_mut!(l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_once), _init_l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5);
    v___x_2340_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
    v___x_2341_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_2341_, 0, v___x_2340_);
    lean_ctor_set(v___x_2341_, 1, v___x_2339_);
    lean_ctor_set(v___x_2341_, 2, v___x_2338_);
    return v___x_2341_;
}
pub unsafe fn _init_l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__7()
-> *mut LeanObject {
    let mut v___x_2342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: *mut LeanObject = core::ptr::null_mut();
    v___x_2342_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__28;
    v___x_2343_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__6), core::ptr::addr_of_mut!(l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__6_once), _init_l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__6);
    v___x_2344_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
    v___x_2345_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_2345_, 0, v___x_2344_);
    lean_ctor_set(v___x_2345_, 1, v___x_2343_);
    lean_ctor_set(v___x_2345_, 2, v___x_2342_);
    return v___x_2345_;
}
pub unsafe fn _init_l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__8()
-> *mut LeanObject {
    let mut v___x_2346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2349_: *mut LeanObject = core::ptr::null_mut();
    v___x_2346_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__41;
    v___x_2347_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__7), core::ptr::addr_of_mut!(l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__7_once), _init_l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__7);
    v___x_2348_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
    v___x_2349_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_2349_, 0, v___x_2348_);
    lean_ctor_set(v___x_2349_, 1, v___x_2347_);
    lean_ctor_set(v___x_2349_, 2, v___x_2346_);
    return v___x_2349_;
}
pub unsafe fn _init_l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__9()
-> *mut LeanObject {
    let mut v___x_2350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: *mut LeanObject = core::ptr::null_mut();
    v___x_2350_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__45;
    v___x_2351_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__8), core::ptr::addr_of_mut!(l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__8_once), _init_l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__8);
    v___x_2352_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
    v___x_2353_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_2353_, 0, v___x_2352_);
    lean_ctor_set(v___x_2353_, 1, v___x_2351_);
    lean_ctor_set(v___x_2353_, 2, v___x_2350_);
    return v___x_2353_;
}
pub unsafe fn _init_l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__10()
-> *mut LeanObject {
    let mut v___x_2354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: *mut LeanObject = core::ptr::null_mut();
    v___x_2354_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__48;
    v___x_2355_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__9), core::ptr::addr_of_mut!(l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__9_once), _init_l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__9);
    v___x_2356_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
    v___x_2357_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_2357_, 0, v___x_2356_);
    lean_ctor_set(v___x_2357_, 1, v___x_2355_);
    lean_ctor_set(v___x_2357_, 2, v___x_2354_);
    return v___x_2357_;
}
pub unsafe fn _init_l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11()
-> *mut LeanObject {
    let mut v___x_2358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut LeanObject = core::ptr::null_mut();
    v___x_2358_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__51;
    v___x_2359_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__10), core::ptr::addr_of_mut!(l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__10_once), _init_l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__10);
    v___x_2360_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
    v___x_2361_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_2361_, 0, v___x_2360_);
    lean_ctor_set(v___x_2361_, 1, v___x_2359_);
    lean_ctor_set(v___x_2361_, 2, v___x_2358_);
    return v___x_2361_;
}
pub unsafe fn _init_l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__12()
-> *mut LeanObject {
    let mut v___x_2362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut LeanObject = core::ptr::null_mut();
    v___x_2362_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__45;
    v___x_2363_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11), core::ptr::addr_of_mut!(l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11_once), _init_l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11);
    v___x_2364_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
    v___x_2365_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_2365_, 0, v___x_2364_);
    lean_ctor_set(v___x_2365_, 1, v___x_2363_);
    lean_ctor_set(v___x_2365_, 2, v___x_2362_);
    return v___x_2365_;
}
pub unsafe fn _init_l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__13()
-> *mut LeanObject {
    let mut v___x_2366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut LeanObject = core::ptr::null_mut();
    v___x_2366_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__12), core::ptr::addr_of_mut!(l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__12_once), _init_l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__12);
    v___x_2367_ = lean_unsigned_to_nat(1022);
    v___x_2368_ =
        l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1;
    v___x_2369_ = lean_alloc_ctor(3, 3, (0) as u32);
    lean_ctor_set(v___x_2369_, 0, v___x_2368_);
    lean_ctor_set(v___x_2369_, 1, v___x_2367_);
    lean_ctor_set(v___x_2369_, 2, v___x_2366_);
    return v___x_2369_;
}
pub unsafe fn _init_l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d__()
-> *mut LeanObject {
    let mut v___x_2370_: *mut LeanObject = core::ptr::null_mut();
    v___x_2370_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__13), core::ptr::addr_of_mut!(l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__13_once), _init_l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__13);
    return v___x_2370_;
}
pub unsafe fn _init_l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5()
-> *mut LeanObject {
    let mut v___x_2465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut LeanObject = core::ptr::null_mut();
    v___x_2465_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22), core::ptr::addr_of_mut!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22_once), _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22);
    v___x_2466_ =
        l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__4;
    v___x_2467_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
    v___x_2468_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_2468_, 0, v___x_2467_);
    lean_ctor_set(v___x_2468_, 1, v___x_2466_);
    lean_ctor_set(v___x_2468_, 2, v___x_2465_);
    return v___x_2468_;
}
pub unsafe fn _init_l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__6()
-> *mut LeanObject {
    let mut v___x_2469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut LeanObject = core::ptr::null_mut();
    v___x_2469_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__37;
    v___x_2470_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5), core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_once), _init_l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5);
    v___x_2471_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
    v___x_2472_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_2472_, 0, v___x_2471_);
    lean_ctor_set(v___x_2472_, 1, v___x_2470_);
    lean_ctor_set(v___x_2472_, 2, v___x_2469_);
    return v___x_2472_;
}
pub unsafe fn _init_l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__7()
-> *mut LeanObject {
    let mut v___x_2473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: *mut LeanObject = core::ptr::null_mut();
    v___x_2473_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__28;
    v___x_2474_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__6), core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__6_once), _init_l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__6);
    v___x_2475_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
    v___x_2476_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_2476_, 0, v___x_2475_);
    lean_ctor_set(v___x_2476_, 1, v___x_2474_);
    lean_ctor_set(v___x_2476_, 2, v___x_2473_);
    return v___x_2476_;
}
pub unsafe fn _init_l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__8()
-> *mut LeanObject {
    let mut v___x_2477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut LeanObject = core::ptr::null_mut();
    v___x_2477_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__41;
    v___x_2478_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__7), core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__7_once), _init_l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__7);
    v___x_2479_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
    v___x_2480_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_2480_, 0, v___x_2479_);
    lean_ctor_set(v___x_2480_, 1, v___x_2478_);
    lean_ctor_set(v___x_2480_, 2, v___x_2477_);
    return v___x_2480_;
}
pub unsafe fn _init_l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__9()
-> *mut LeanObject {
    let mut v___x_2481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut LeanObject = core::ptr::null_mut();
    v___x_2481_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__45;
    v___x_2482_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__8), core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__8_once), _init_l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__8);
    v___x_2483_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
    v___x_2484_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_2484_, 0, v___x_2483_);
    lean_ctor_set(v___x_2484_, 1, v___x_2482_);
    lean_ctor_set(v___x_2484_, 2, v___x_2481_);
    return v___x_2484_;
}
pub unsafe fn _init_l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__10()
-> *mut LeanObject {
    let mut v___x_2485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut LeanObject = core::ptr::null_mut();
    v___x_2485_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__48;
    v___x_2486_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__9), core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__9_once), _init_l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__9);
    v___x_2487_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
    v___x_2488_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_2488_, 0, v___x_2487_);
    lean_ctor_set(v___x_2488_, 1, v___x_2486_);
    lean_ctor_set(v___x_2488_, 2, v___x_2485_);
    return v___x_2488_;
}
pub unsafe fn _init_l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11()
-> *mut LeanObject {
    let mut v___x_2489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut LeanObject = core::ptr::null_mut();
    v___x_2489_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__51;
    v___x_2490_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__10), core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__10_once), _init_l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__10);
    v___x_2491_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
    v___x_2492_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_2492_, 0, v___x_2491_);
    lean_ctor_set(v___x_2492_, 1, v___x_2490_);
    lean_ctor_set(v___x_2492_, 2, v___x_2489_);
    return v___x_2492_;
}
pub unsafe fn _init_l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__12()
-> *mut LeanObject {
    let mut v___x_2493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: *mut LeanObject = core::ptr::null_mut();
    v___x_2493_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__45;
    v___x_2494_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11), core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11_once), _init_l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11);
    v___x_2495_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
    v___x_2496_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_2496_, 0, v___x_2495_);
    lean_ctor_set(v___x_2496_, 1, v___x_2494_);
    lean_ctor_set(v___x_2496_, 2, v___x_2493_);
    return v___x_2496_;
}
pub unsafe fn _init_l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__13()
-> *mut LeanObject {
    let mut v___x_2497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2500_: *mut LeanObject = core::ptr::null_mut();
    v___x_2497_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__12), core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__12_once), _init_l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__12);
    v___x_2498_ = lean_unsigned_to_nat(1022);
    v___x_2499_ =
        l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1;
    v___x_2500_ = lean_alloc_ctor(3, 3, (0) as u32);
    lean_ctor_set(v___x_2500_, 0, v___x_2499_);
    lean_ctor_set(v___x_2500_, 1, v___x_2498_);
    lean_ctor_set(v___x_2500_, 2, v___x_2497_);
    return v___x_2500_;
}
pub unsafe fn _init_l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d__()
-> *mut LeanObject {
    let mut v___x_2501_: *mut LeanObject = core::ptr::null_mut();
    v___x_2501_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__13), core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__13_once), _init_l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__13);
    return v___x_2501_;
}
pub unsafe fn _init_l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5()
-> *mut LeanObject {
    let mut v___x_2514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut LeanObject = core::ptr::null_mut();
    v___x_2514_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22), core::ptr::addr_of_mut!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22_once), _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22);
    v___x_2515_ = l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__4;
    v___x_2516_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
    v___x_2517_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_2517_, 0, v___x_2516_);
    lean_ctor_set(v___x_2517_, 1, v___x_2515_);
    lean_ctor_set(v___x_2517_, 2, v___x_2514_);
    return v___x_2517_;
}
pub unsafe fn _init_l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__6()
-> *mut LeanObject {
    let mut v___x_2518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: *mut LeanObject = core::ptr::null_mut();
    v___x_2518_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__37;
    v___x_2519_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5), core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_once), _init_l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5);
    v___x_2520_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
    v___x_2521_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_2521_, 0, v___x_2520_);
    lean_ctor_set(v___x_2521_, 1, v___x_2519_);
    lean_ctor_set(v___x_2521_, 2, v___x_2518_);
    return v___x_2521_;
}
pub unsafe fn _init_l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__7()
-> *mut LeanObject {
    let mut v___x_2522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: *mut LeanObject = core::ptr::null_mut();
    v___x_2522_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__28;
    v___x_2523_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__6), core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__6_once), _init_l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__6);
    v___x_2524_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
    v___x_2525_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_2525_, 0, v___x_2524_);
    lean_ctor_set(v___x_2525_, 1, v___x_2523_);
    lean_ctor_set(v___x_2525_, 2, v___x_2522_);
    return v___x_2525_;
}
pub unsafe fn _init_l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__8()
-> *mut LeanObject {
    let mut v___x_2526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: *mut LeanObject = core::ptr::null_mut();
    v___x_2526_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__41;
    v___x_2527_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__7), core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__7_once), _init_l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__7);
    v___x_2528_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
    v___x_2529_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_2529_, 0, v___x_2528_);
    lean_ctor_set(v___x_2529_, 1, v___x_2527_);
    lean_ctor_set(v___x_2529_, 2, v___x_2526_);
    return v___x_2529_;
}
pub unsafe fn _init_l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__9()
-> *mut LeanObject {
    let mut v___x_2530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut LeanObject = core::ptr::null_mut();
    v___x_2530_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__45;
    v___x_2531_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__8), core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__8_once), _init_l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__8);
    v___x_2532_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
    v___x_2533_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_2533_, 0, v___x_2532_);
    lean_ctor_set(v___x_2533_, 1, v___x_2531_);
    lean_ctor_set(v___x_2533_, 2, v___x_2530_);
    return v___x_2533_;
}
pub unsafe fn _init_l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__10()
-> *mut LeanObject {
    let mut v___x_2534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: *mut LeanObject = core::ptr::null_mut();
    v___x_2534_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__48;
    v___x_2535_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__9), core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__9_once), _init_l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__9);
    v___x_2536_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
    v___x_2537_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_2537_, 0, v___x_2536_);
    lean_ctor_set(v___x_2537_, 1, v___x_2535_);
    lean_ctor_set(v___x_2537_, 2, v___x_2534_);
    return v___x_2537_;
}
pub unsafe fn _init_l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11()
-> *mut LeanObject {
    let mut v___x_2538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut LeanObject = core::ptr::null_mut();
    v___x_2538_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__51;
    v___x_2539_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__10), core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__10_once), _init_l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__10);
    v___x_2540_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
    v___x_2541_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_2541_, 0, v___x_2540_);
    lean_ctor_set(v___x_2541_, 1, v___x_2539_);
    lean_ctor_set(v___x_2541_, 2, v___x_2538_);
    return v___x_2541_;
}
pub unsafe fn _init_l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__12()
-> *mut LeanObject {
    let mut v___x_2542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut LeanObject = core::ptr::null_mut();
    v___x_2542_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__45;
    v___x_2543_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11), core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11_once), _init_l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11);
    v___x_2544_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
    v___x_2545_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_2545_, 0, v___x_2544_);
    lean_ctor_set(v___x_2545_, 1, v___x_2543_);
    lean_ctor_set(v___x_2545_, 2, v___x_2542_);
    return v___x_2545_;
}
pub unsafe fn _init_l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__13()
-> *mut LeanObject {
    let mut v___x_2546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut LeanObject = core::ptr::null_mut();
    v___x_2546_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__12), core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__12_once), _init_l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__12);
    v___x_2547_ = lean_unsigned_to_nat(1022);
    v___x_2548_ = l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1;
    v___x_2549_ = lean_alloc_ctor(3, 3, (0) as u32);
    lean_ctor_set(v___x_2549_, 0, v___x_2548_);
    lean_ctor_set(v___x_2549_, 1, v___x_2547_);
    lean_ctor_set(v___x_2549_, 2, v___x_2546_);
    return v___x_2549_;
}
pub unsafe fn _init_l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d__()
-> *mut LeanObject {
    let mut v___x_2550_: *mut LeanObject = core::ptr::null_mut();
    v___x_2550_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__13), core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__13_once), _init_l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__13);
    return v___x_2550_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_simprocAttr___closed__5() -> *mut LeanObject {
    let mut v___x_2697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut LeanObject = core::ptr::null_mut();
    v___x_2697_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22), core::ptr::addr_of_mut!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22_once), _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22);
    v___x_2698_ = l_Lean_Parser_Attr_simprocAttr___closed__4;
    v___x_2699_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
    v___x_2700_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_2700_, 0, v___x_2699_);
    lean_ctor_set(v___x_2700_, 1, v___x_2698_);
    lean_ctor_set(v___x_2700_, 2, v___x_2697_);
    return v___x_2700_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_simprocAttr___closed__6() -> *mut LeanObject {
    let mut v___x_2701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: *mut LeanObject = core::ptr::null_mut();
    v___x_2701_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_simprocAttr___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_simprocAttr___closed__5_once),
        _init_l_Lean_Parser_Attr_simprocAttr___closed__5,
    );
    v___x_2702_ = lean_unsigned_to_nat(1022);
    v___x_2703_ = l_Lean_Parser_Attr_simprocAttr___closed__2;
    v___x_2704_ = lean_alloc_ctor(3, 3, (0) as u32);
    lean_ctor_set(v___x_2704_, 0, v___x_2703_);
    lean_ctor_set(v___x_2704_, 1, v___x_2702_);
    lean_ctor_set(v___x_2704_, 2, v___x_2701_);
    return v___x_2704_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_simprocAttr() -> *mut LeanObject {
    let mut v___x_2705_: *mut LeanObject = core::ptr::null_mut();
    v___x_2705_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_simprocAttr___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_simprocAttr___closed__6_once),
        _init_l_Lean_Parser_Attr_simprocAttr___closed__6,
    );
    return v___x_2705_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_sevalprocAttr___closed__4() -> *mut LeanObject {
    let mut v___x_2716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut LeanObject = core::ptr::null_mut();
    v___x_2716_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22), core::ptr::addr_of_mut!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22_once), _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22);
    v___x_2717_ = l_Lean_Parser_Attr_sevalprocAttr___closed__3;
    v___x_2718_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
    v___x_2719_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_2719_, 0, v___x_2718_);
    lean_ctor_set(v___x_2719_, 1, v___x_2717_);
    lean_ctor_set(v___x_2719_, 2, v___x_2716_);
    return v___x_2719_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_sevalprocAttr___closed__5() -> *mut LeanObject {
    let mut v___x_2720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2723_: *mut LeanObject = core::ptr::null_mut();
    v___x_2720_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_sevalprocAttr___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_sevalprocAttr___closed__4_once),
        _init_l_Lean_Parser_Attr_sevalprocAttr___closed__4,
    );
    v___x_2721_ = lean_unsigned_to_nat(1022);
    v___x_2722_ = l_Lean_Parser_Attr_sevalprocAttr___closed__1;
    v___x_2723_ = lean_alloc_ctor(3, 3, (0) as u32);
    lean_ctor_set(v___x_2723_, 0, v___x_2722_);
    lean_ctor_set(v___x_2723_, 1, v___x_2721_);
    lean_ctor_set(v___x_2723_, 2, v___x_2720_);
    return v___x_2723_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_sevalprocAttr() -> *mut LeanObject {
    let mut v___x_2724_: *mut LeanObject = core::ptr::null_mut();
    v___x_2724_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_sevalprocAttr___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_sevalprocAttr___closed__5_once),
        _init_l_Lean_Parser_Attr_sevalprocAttr___closed__5,
    );
    return v___x_2724_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_simprocBuiltinAttr___closed__4() -> *mut LeanObject {
    let mut v___x_2735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2738_: *mut LeanObject = core::ptr::null_mut();
    v___x_2735_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22), core::ptr::addr_of_mut!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22_once), _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22);
    v___x_2736_ = l_Lean_Parser_Attr_simprocBuiltinAttr___closed__3;
    v___x_2737_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
    v___x_2738_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_2738_, 0, v___x_2737_);
    lean_ctor_set(v___x_2738_, 1, v___x_2736_);
    lean_ctor_set(v___x_2738_, 2, v___x_2735_);
    return v___x_2738_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_simprocBuiltinAttr___closed__5() -> *mut LeanObject {
    let mut v___x_2739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut LeanObject = core::ptr::null_mut();
    v___x_2739_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_simprocBuiltinAttr___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_simprocBuiltinAttr___closed__4_once),
        _init_l_Lean_Parser_Attr_simprocBuiltinAttr___closed__4,
    );
    v___x_2740_ = lean_unsigned_to_nat(1022);
    v___x_2741_ = l_Lean_Parser_Attr_simprocBuiltinAttr___closed__1;
    v___x_2742_ = lean_alloc_ctor(3, 3, (0) as u32);
    lean_ctor_set(v___x_2742_, 0, v___x_2741_);
    lean_ctor_set(v___x_2742_, 1, v___x_2740_);
    lean_ctor_set(v___x_2742_, 2, v___x_2739_);
    return v___x_2742_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_simprocBuiltinAttr() -> *mut LeanObject {
    let mut v___x_2743_: *mut LeanObject = core::ptr::null_mut();
    v___x_2743_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_simprocBuiltinAttr___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_simprocBuiltinAttr___closed__5_once),
        _init_l_Lean_Parser_Attr_simprocBuiltinAttr___closed__5,
    );
    return v___x_2743_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__4() -> *mut LeanObject {
    let mut v___x_2754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: *mut LeanObject = core::ptr::null_mut();
    v___x_2754_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22), core::ptr::addr_of_mut!(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22_once), _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22);
    v___x_2755_ = l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__3;
    v___x_2756_ =
        l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
    v___x_2757_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_2757_, 0, v___x_2756_);
    lean_ctor_set(v___x_2757_, 1, v___x_2755_);
    lean_ctor_set(v___x_2757_, 2, v___x_2754_);
    return v___x_2757_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__5() -> *mut LeanObject {
    let mut v___x_2758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: *mut LeanObject = core::ptr::null_mut();
    v___x_2758_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__4_once),
        _init_l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__4,
    );
    v___x_2759_ = lean_unsigned_to_nat(1022);
    v___x_2760_ = l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__1;
    v___x_2761_ = lean_alloc_ctor(3, 3, (0) as u32);
    lean_ctor_set(v___x_2761_, 0, v___x_2760_);
    lean_ctor_set(v___x_2761_, 1, v___x_2759_);
    lean_ctor_set(v___x_2761_, 2, v___x_2758_);
    return v___x_2761_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_sevalprocBuiltinAttr() -> *mut LeanObject {
    let mut v___x_2762_: *mut LeanObject = core::ptr::null_mut();
    v___x_2762_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__5_once),
        _init_l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__5,
    );
    return v___x_2762_;
}
pub unsafe fn _init_l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27()
-> *mut LeanObject {
    let mut v___x_2811_: *mut LeanObject = core::ptr::null_mut();
    v___x_2811_ = l_Array_mkArray0(lean_box(0));
    return v___x_2811_;
}
pub unsafe fn l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1(
    mut v_x_2819_: *mut LeanObject,
    mut v_a_2820_: *mut LeanObject,
    mut v_a_2821_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_2880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: u8 = 0;
    let mut v___x_2887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_simprocType_2894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: u8 = 0;
    let mut v___x_2896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2906_: u8 = 0;
    let mut v___x_2907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2911_: u8 = 0;
    let mut v___x_2912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2913_: u8 = 0;
    let mut v___x_2914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_2916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: u8 = 0;
    let mut v___x_2919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2922_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2822_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0;
                v___x_2823_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1;
                v___x_2905_ =
                    l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__1;
                lean_inc(v_x_2819_);
                v___x_2906_ = l_Lean_Syntax_isOfKind(v_x_2819_, v___x_2905_);
                if v___x_2906_ == 0 {
                    lean_dec(v_x_2819_);
                    v___x_2907_ = lean_box(1);
                    v___x_2908_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_2908_, 0, v___x_2907_);
                    lean_ctor_set(v___x_2908_, 1, v_a_2821_);
                    return v___x_2908_;
                } else {
                    v___x_2909_ = lean_unsigned_to_nat(0);
                    v___x_2910_ = l_Lean_Syntax_getArg(v_x_2819_, v___x_2909_);
                    v___x_2911_ = l_Lean_Syntax_isNone(v___x_2910_);
                    if v___x_2911_ == 0 {
                        v___x_2912_ = lean_unsigned_to_nat(1);
                        lean_inc(v___x_2910_);
                        v___x_2913_ = l_Lean_Syntax_matchesNull(v___x_2910_, v___x_2912_);
                        if v___x_2913_ == 0 {
                            lean_dec(v___x_2910_);
                            lean_dec(v_x_2819_);
                            v___x_2914_ = lean_box(1);
                            v___x_2915_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v___x_2915_, 0, v___x_2914_);
                            lean_ctor_set(v___x_2915_, 1, v_a_2821_);
                            return v___x_2915_;
                        } else {
                            v_doc_x3f_2916_ = l_Lean_Syntax_getArg(v___x_2910_, v___x_2909_);
                            lean_dec(v___x_2910_);
                            v___x_2917_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__29;
                            lean_inc(v_doc_x3f_2916_);
                            v___x_2918_ = l_Lean_Syntax_isOfKind(v_doc_x3f_2916_, v___x_2917_);
                            if v___x_2918_ == 0 {
                                lean_dec(v_doc_x3f_2916_);
                                lean_dec(v_x_2819_);
                                v___x_2919_ = lean_box(1);
                                v___x_2920_ = lean_alloc_ctor(1, 2, (0) as u32);
                                lean_ctor_set(v___x_2920_, 0, v___x_2919_);
                                lean_ctor_set(v___x_2920_, 1, v_a_2821_);
                                return v___x_2920_;
                            } else {
                                v___x_2921_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_2921_, 0, v_doc_x3f_2916_);
                                v_doc_x3f_2880_ = v___x_2921_;
                                v___y_2881_ = v_a_2820_;
                                v___y_2882_ = v_a_2821_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___x_2910_);
                        v___x_2922_ = lean_box(0);
                        v_doc_x3f_2880_ = v___x_2922_;
                        v___y_2881_ = v_a_2820_;
                        v___y_2882_ = v_a_2821_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc_ref_n(v___y_2829_, 2);
                v___x_2837_ = l_Array_append___redArg(v___y_2829_, v___y_2836_);
                lean_dec_ref(v___y_2836_);
                lean_inc_n(v___y_2834_, 5);
                lean_inc_n(v___y_2827_, 20);
                v___x_2838_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2838_, 0, v___y_2827_);
                lean_ctor_set(v___x_2838_, 1, v___y_2834_);
                lean_ctor_set(v___x_2838_, 2, v___x_2837_);
                v___x_2839_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2839_, 0, v___y_2827_);
                lean_ctor_set(v___x_2839_, 1, v___y_2834_);
                lean_ctor_set(v___x_2839_, 2, v___y_2829_);
                v___x_2840_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__0;
                lean_inc_ref_n(v___y_2825_, 5);
                v___x_2841_ =
                    l_Lean_Name_mkStr4(v___x_2822_, v___x_2823_, v___y_2825_, v___x_2840_);
                v___x_2842_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2842_, 0, v___y_2827_);
                lean_ctor_set(v___x_2842_, 1, v___x_2840_);
                v___x_2843_ = l_Lean_Syntax_node1(v___y_2827_, v___x_2841_, v___x_2842_);
                v___x_2844_ = l_Lean_Syntax_node1(v___y_2827_, v___y_2834_, v___x_2843_);
                lean_inc_ref_n(v___x_2839_, 10);
                lean_inc(v___y_2833_);
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
                v___x_2849_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2849_, 0, v___y_2827_);
                lean_ctor_set(v___x_2849_, 1, v___x_2848_);
                v___x_2850_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__3;
                v___x_2851_ =
                    l_Lean_Name_mkStr4(v___x_2822_, v___x_2823_, v___y_2825_, v___x_2850_);
                lean_inc(v___y_2835_);
                v___x_2852_ =
                    l_Lean_Syntax_node2(v___y_2827_, v___x_2851_, v___y_2835_, v___x_2839_);
                v___x_2853_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__4;
                v___x_2854_ =
                    l_Lean_Name_mkStr4(v___x_2822_, v___x_2823_, v___y_2825_, v___x_2853_);
                v___x_2855_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__7;
                v___x_2856_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__8;
                v___x_2857_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2857_, 0, v___y_2827_);
                lean_ctor_set(v___x_2857_, 1, v___x_2856_);
                lean_inc(v___y_2832_);
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
                v___x_2865_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2865_, 0, v___y_2827_);
                lean_ctor_set(v___x_2865_, 1, v___x_2864_);
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
                lean_inc(v___y_2831_);
                v___x_2870_ =
                    l_Lean_Syntax_node2(v___y_2827_, v___y_2831_, v___x_2845_, v___x_2869_);
                v___x_2871_ = l_Lean_Parser_simprocPattern___closed__1;
                v___x_2872_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__14;
                v___x_2873_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2873_, 0, v___y_2827_);
                lean_ctor_set(v___x_2873_, 1, v___x_2872_);
                v___x_2874_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__15;
                v___x_2875_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2875_, 0, v___y_2827_);
                lean_ctor_set(v___x_2875_, 1, v___x_2874_);
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
                v___x_2878_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2878_, 0, v___x_2877_);
                lean_ctor_set(v___x_2878_, 1, v___y_2828_);
                return v___x_2878_;
            }
            2 => {
                v___x_2883_ = lean_unsigned_to_nat(2);
                v___x_2884_ = l_Lean_Syntax_getArg(v_x_2819_, v___x_2883_);
                v___x_2885_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__27;
                lean_inc(v___x_2884_);
                v___x_2886_ = l_Lean_Syntax_isOfKind(v___x_2884_, v___x_2885_);
                if v___x_2886_ == 0 {
                    lean_dec(v___x_2884_);
                    lean_dec(v_doc_x3f_2880_);
                    lean_dec(v_x_2819_);
                    v___x_2887_ = lean_box(1);
                    v___x_2888_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_2888_, 0, v___x_2887_);
                    lean_ctor_set(v___x_2888_, 1, v___y_2882_);
                    return v___x_2888_;
                } else {
                    v_ref_2889_ = lean_ctor_get(v___y_2881_, 5);
                    v___x_2890_ = lean_unsigned_to_nat(4);
                    v___x_2891_ = l_Lean_Syntax_getArg(v_x_2819_, v___x_2890_);
                    v___x_2892_ = lean_unsigned_to_nat(7);
                    v___x_2893_ = l_Lean_Syntax_getArg(v_x_2819_, v___x_2892_);
                    lean_dec(v_x_2819_);
                    v_simprocType_2894_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__19;
                    v___x_2895_ = 0;
                    v___x_2896_ = l_Lean_SourceInfo_fromRef(v_ref_2889_, v___x_2895_);
                    v___x_2897_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__21;
                    v___x_2898_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__22;
                    v___x_2899_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__24;
                    v___x_2900_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__26;
                    v___x_2901_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27), core::ptr::addr_of_mut!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27_once), _init_l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27);
                    if lean_obj_tag(v_doc_x3f_2880_) == 1 {
                        v_val_2902_ = lean_ctor_get(v_doc_x3f_2880_, 0);
                        lean_inc(v_val_2902_);
                        lean_dec_ref_known(v_doc_x3f_2880_, 1);
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
                        lean_dec(v_doc_x3f_2880_);
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
    mut v_x_2923_: *mut LeanObject,
    mut v_a_2924_: *mut LeanObject,
    mut v_a_2925_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2926_: *mut LeanObject = core::ptr::null_mut();
    v_res_2926_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1(v_x_2923_, v_a_2924_, v_a_2925_);
    lean_dec_ref(v_a_2924_);
    return v_res_2926_;
}
pub unsafe fn l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Dsimproc__decl___x28___x29_x3a_x3d____1(
    mut v_x_2933_: *mut LeanObject,
    mut v_a_2934_: *mut LeanObject,
    mut v_a_2935_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_2994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: u8 = 0;
    let mut v___x_3001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_simprocType_3008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: u8 = 0;
    let mut v___x_3010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3020_: u8 = 0;
    let mut v___x_3021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: u8 = 0;
    let mut v___x_3026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: u8 = 0;
    let mut v___x_3028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_3030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: u8 = 0;
    let mut v___x_3033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2936_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0;
                v___x_2937_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1;
                v___x_3019_ =
                    l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__1;
                lean_inc(v_x_2933_);
                v___x_3020_ = l_Lean_Syntax_isOfKind(v_x_2933_, v___x_3019_);
                if v___x_3020_ == 0 {
                    lean_dec(v_x_2933_);
                    v___x_3021_ = lean_box(1);
                    v___x_3022_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_3022_, 0, v___x_3021_);
                    lean_ctor_set(v___x_3022_, 1, v_a_2935_);
                    return v___x_3022_;
                } else {
                    v___x_3023_ = lean_unsigned_to_nat(0);
                    v___x_3024_ = l_Lean_Syntax_getArg(v_x_2933_, v___x_3023_);
                    v___x_3025_ = l_Lean_Syntax_isNone(v___x_3024_);
                    if v___x_3025_ == 0 {
                        v___x_3026_ = lean_unsigned_to_nat(1);
                        lean_inc(v___x_3024_);
                        v___x_3027_ = l_Lean_Syntax_matchesNull(v___x_3024_, v___x_3026_);
                        if v___x_3027_ == 0 {
                            lean_dec(v___x_3024_);
                            lean_dec(v_x_2933_);
                            v___x_3028_ = lean_box(1);
                            v___x_3029_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v___x_3029_, 0, v___x_3028_);
                            lean_ctor_set(v___x_3029_, 1, v_a_2935_);
                            return v___x_3029_;
                        } else {
                            v_doc_x3f_3030_ = l_Lean_Syntax_getArg(v___x_3024_, v___x_3023_);
                            lean_dec(v___x_3024_);
                            v___x_3031_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__29;
                            lean_inc(v_doc_x3f_3030_);
                            v___x_3032_ = l_Lean_Syntax_isOfKind(v_doc_x3f_3030_, v___x_3031_);
                            if v___x_3032_ == 0 {
                                lean_dec(v_doc_x3f_3030_);
                                lean_dec(v_x_2933_);
                                v___x_3033_ = lean_box(1);
                                v___x_3034_ = lean_alloc_ctor(1, 2, (0) as u32);
                                lean_ctor_set(v___x_3034_, 0, v___x_3033_);
                                lean_ctor_set(v___x_3034_, 1, v_a_2935_);
                                return v___x_3034_;
                            } else {
                                v___x_3035_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_3035_, 0, v_doc_x3f_3030_);
                                v_doc_x3f_2994_ = v___x_3035_;
                                v___y_2995_ = v_a_2934_;
                                v___y_2996_ = v_a_2935_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___x_3024_);
                        v___x_3036_ = lean_box(0);
                        v_doc_x3f_2994_ = v___x_3036_;
                        v___y_2995_ = v_a_2934_;
                        v___y_2996_ = v_a_2935_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc_ref_n(v___y_2947_, 2);
                v___x_2951_ = l_Array_append___redArg(v___y_2947_, v___y_2950_);
                lean_dec_ref(v___y_2950_);
                lean_inc_n(v___y_2940_, 5);
                lean_inc_n(v___y_2942_, 20);
                v___x_2952_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2952_, 0, v___y_2942_);
                lean_ctor_set(v___x_2952_, 1, v___y_2940_);
                lean_ctor_set(v___x_2952_, 2, v___x_2951_);
                v___x_2953_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2953_, 0, v___y_2942_);
                lean_ctor_set(v___x_2953_, 1, v___y_2940_);
                lean_ctor_set(v___x_2953_, 2, v___y_2947_);
                v___x_2954_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__0;
                lean_inc_ref_n(v___y_2946_, 5);
                v___x_2955_ =
                    l_Lean_Name_mkStr4(v___x_2936_, v___x_2937_, v___y_2946_, v___x_2954_);
                v___x_2956_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2956_, 0, v___y_2942_);
                lean_ctor_set(v___x_2956_, 1, v___x_2954_);
                v___x_2957_ = l_Lean_Syntax_node1(v___y_2942_, v___x_2955_, v___x_2956_);
                v___x_2958_ = l_Lean_Syntax_node1(v___y_2942_, v___y_2940_, v___x_2957_);
                lean_inc_ref_n(v___x_2953_, 10);
                lean_inc(v___y_2944_);
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
                v___x_2963_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2963_, 0, v___y_2942_);
                lean_ctor_set(v___x_2963_, 1, v___x_2962_);
                v___x_2964_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__3;
                v___x_2965_ =
                    l_Lean_Name_mkStr4(v___x_2936_, v___x_2937_, v___y_2946_, v___x_2964_);
                lean_inc(v___y_2941_);
                v___x_2966_ =
                    l_Lean_Syntax_node2(v___y_2942_, v___x_2965_, v___y_2941_, v___x_2953_);
                v___x_2967_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__4;
                v___x_2968_ =
                    l_Lean_Name_mkStr4(v___x_2936_, v___x_2937_, v___y_2946_, v___x_2967_);
                v___x_2969_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__7;
                v___x_2970_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__8;
                v___x_2971_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2971_, 0, v___y_2942_);
                lean_ctor_set(v___x_2971_, 1, v___x_2970_);
                lean_inc(v___y_2949_);
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
                v___x_2979_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2979_, 0, v___y_2942_);
                lean_ctor_set(v___x_2979_, 1, v___x_2978_);
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
                lean_inc(v___y_2945_);
                v___x_2984_ =
                    l_Lean_Syntax_node2(v___y_2942_, v___y_2945_, v___x_2959_, v___x_2983_);
                v___x_2985_ = l_Lean_Parser_simprocPattern___closed__1;
                v___x_2986_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__14;
                v___x_2987_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2987_, 0, v___y_2942_);
                lean_ctor_set(v___x_2987_, 1, v___x_2986_);
                v___x_2988_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__15;
                v___x_2989_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2989_, 0, v___y_2942_);
                lean_ctor_set(v___x_2989_, 1, v___x_2988_);
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
                v___x_2992_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2992_, 0, v___x_2991_);
                lean_ctor_set(v___x_2992_, 1, v___y_2939_);
                return v___x_2992_;
            }
            2 => {
                v___x_2997_ = lean_unsigned_to_nat(2);
                v___x_2998_ = l_Lean_Syntax_getArg(v_x_2933_, v___x_2997_);
                v___x_2999_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__27;
                lean_inc(v___x_2998_);
                v___x_3000_ = l_Lean_Syntax_isOfKind(v___x_2998_, v___x_2999_);
                if v___x_3000_ == 0 {
                    lean_dec(v___x_2998_);
                    lean_dec(v_doc_x3f_2994_);
                    lean_dec(v_x_2933_);
                    v___x_3001_ = lean_box(1);
                    v___x_3002_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_3002_, 0, v___x_3001_);
                    lean_ctor_set(v___x_3002_, 1, v___y_2996_);
                    return v___x_3002_;
                } else {
                    v_ref_3003_ = lean_ctor_get(v___y_2995_, 5);
                    v___x_3004_ = lean_unsigned_to_nat(4);
                    v___x_3005_ = l_Lean_Syntax_getArg(v_x_2933_, v___x_3004_);
                    v___x_3006_ = lean_unsigned_to_nat(7);
                    v___x_3007_ = l_Lean_Syntax_getArg(v_x_2933_, v___x_3006_);
                    lean_dec(v_x_2933_);
                    v_simprocType_3008_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Dsimproc__decl___x28___x29_x3a_x3d____1___closed__1;
                    v___x_3009_ = 0;
                    v___x_3010_ = l_Lean_SourceInfo_fromRef(v_ref_3003_, v___x_3009_);
                    v___x_3011_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__21;
                    v___x_3012_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__22;
                    v___x_3013_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__24;
                    v___x_3014_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__26;
                    v___x_3015_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27), core::ptr::addr_of_mut!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27_once), _init_l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27);
                    if lean_obj_tag(v_doc_x3f_2994_) == 1 {
                        v_val_3016_ = lean_ctor_get(v_doc_x3f_2994_, 0);
                        lean_inc(v_val_3016_);
                        lean_dec_ref_known(v_doc_x3f_2994_, 1);
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
                        lean_dec(v_doc_x3f_2994_);
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
    mut v_x_3037_: *mut LeanObject,
    mut v_a_3038_: *mut LeanObject,
    mut v_a_3039_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3040_: *mut LeanObject = core::ptr::null_mut();
    v_res_3040_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Dsimproc__decl___x28___x29_x3a_x3d____1(v_x_3037_, v_a_3038_, v_a_3039_);
    lean_dec_ref(v_a_3038_);
    return v_res_3040_;
}
pub unsafe fn l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Builtin__simproc__decl___x28___x29_x3a_x3d____1(
    mut v_x_3042_: *mut LeanObject,
    mut v_a_3043_: *mut LeanObject,
    mut v_a_3044_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_3098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: u8 = 0;
    let mut v___x_3105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_simprocType_3112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3113_: u8 = 0;
    let mut v___x_3114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: u8 = 0;
    let mut v___x_3125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3129_: u8 = 0;
    let mut v___x_3130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: u8 = 0;
    let mut v___x_3132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_3134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3136_: u8 = 0;
    let mut v___x_3137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3045_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0;
                v___x_3046_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1;
                v___x_3123_ = l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__1;
                lean_inc(v_x_3042_);
                v___x_3124_ = l_Lean_Syntax_isOfKind(v_x_3042_, v___x_3123_);
                if v___x_3124_ == 0 {
                    lean_dec(v_x_3042_);
                    v___x_3125_ = lean_box(1);
                    v___x_3126_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_3126_, 0, v___x_3125_);
                    lean_ctor_set(v___x_3126_, 1, v_a_3044_);
                    return v___x_3126_;
                } else {
                    v___x_3127_ = lean_unsigned_to_nat(0);
                    v___x_3128_ = l_Lean_Syntax_getArg(v_x_3042_, v___x_3127_);
                    v___x_3129_ = l_Lean_Syntax_isNone(v___x_3128_);
                    if v___x_3129_ == 0 {
                        v___x_3130_ = lean_unsigned_to_nat(1);
                        lean_inc(v___x_3128_);
                        v___x_3131_ = l_Lean_Syntax_matchesNull(v___x_3128_, v___x_3130_);
                        if v___x_3131_ == 0 {
                            lean_dec(v___x_3128_);
                            lean_dec(v_x_3042_);
                            v___x_3132_ = lean_box(1);
                            v___x_3133_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v___x_3133_, 0, v___x_3132_);
                            lean_ctor_set(v___x_3133_, 1, v_a_3044_);
                            return v___x_3133_;
                        } else {
                            v_doc_x3f_3134_ = l_Lean_Syntax_getArg(v___x_3128_, v___x_3127_);
                            lean_dec(v___x_3128_);
                            v___x_3135_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__29;
                            lean_inc(v_doc_x3f_3134_);
                            v___x_3136_ = l_Lean_Syntax_isOfKind(v_doc_x3f_3134_, v___x_3135_);
                            if v___x_3136_ == 0 {
                                lean_dec(v_doc_x3f_3134_);
                                lean_dec(v_x_3042_);
                                v___x_3137_ = lean_box(1);
                                v___x_3138_ = lean_alloc_ctor(1, 2, (0) as u32);
                                lean_ctor_set(v___x_3138_, 0, v___x_3137_);
                                lean_ctor_set(v___x_3138_, 1, v_a_3044_);
                                return v___x_3138_;
                            } else {
                                v___x_3139_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_3139_, 0, v_doc_x3f_3134_);
                                v_doc_x3f_3098_ = v___x_3139_;
                                v___y_3099_ = v_a_3043_;
                                v___y_3100_ = v_a_3044_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___x_3128_);
                        v___x_3140_ = lean_box(0);
                        v_doc_x3f_3098_ = v___x_3140_;
                        v___y_3099_ = v_a_3043_;
                        v___y_3100_ = v_a_3044_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc_ref_n(v___y_3051_, 2);
                v___x_3060_ = l_Array_append___redArg(v___y_3051_, v___y_3059_);
                lean_dec_ref(v___y_3059_);
                lean_inc_n(v___y_3056_, 4);
                lean_inc_n(v___y_3048_, 17);
                v___x_3061_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_3061_, 0, v___y_3048_);
                lean_ctor_set(v___x_3061_, 1, v___y_3056_);
                lean_ctor_set(v___x_3061_, 2, v___x_3060_);
                v___x_3062_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_3062_, 0, v___y_3048_);
                lean_ctor_set(v___x_3062_, 1, v___y_3056_);
                lean_ctor_set(v___x_3062_, 2, v___y_3051_);
                lean_inc_ref_n(v___x_3062_, 11);
                lean_inc(v___y_3050_);
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
                lean_inc_ref_n(v___y_3049_, 4);
                v___x_3065_ =
                    l_Lean_Name_mkStr4(v___x_3045_, v___x_3046_, v___y_3049_, v___x_3064_);
                v___x_3066_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__2;
                v___x_3067_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3067_, 0, v___y_3048_);
                lean_ctor_set(v___x_3067_, 1, v___x_3066_);
                v___x_3068_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__3;
                v___x_3069_ =
                    l_Lean_Name_mkStr4(v___x_3045_, v___x_3046_, v___y_3049_, v___x_3068_);
                lean_inc(v___y_3055_);
                v___x_3070_ =
                    l_Lean_Syntax_node2(v___y_3048_, v___x_3069_, v___y_3055_, v___x_3062_);
                v___x_3071_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__4;
                v___x_3072_ =
                    l_Lean_Name_mkStr4(v___x_3045_, v___x_3046_, v___y_3049_, v___x_3071_);
                v___x_3073_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__7;
                v___x_3074_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__8;
                v___x_3075_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3075_, 0, v___y_3048_);
                lean_ctor_set(v___x_3075_, 1, v___x_3074_);
                lean_inc(v___y_3054_);
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
                v___x_3083_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3083_, 0, v___y_3048_);
                lean_ctor_set(v___x_3083_, 1, v___x_3082_);
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
                lean_inc(v___y_3057_);
                v___x_3088_ =
                    l_Lean_Syntax_node2(v___y_3048_, v___y_3057_, v___x_3063_, v___x_3087_);
                v___x_3089_ = l_Lean_Parser_simprocPatternBuiltin___closed__1;
                v___x_3090_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Builtin__simproc__decl___x28___x29_x3a_x3d____1___closed__0;
                v___x_3091_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3091_, 0, v___y_3048_);
                lean_ctor_set(v___x_3091_, 1, v___x_3090_);
                v___x_3092_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__15;
                v___x_3093_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3093_, 0, v___y_3048_);
                lean_ctor_set(v___x_3093_, 1, v___x_3092_);
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
                v___x_3096_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3096_, 0, v___x_3095_);
                lean_ctor_set(v___x_3096_, 1, v___y_3053_);
                return v___x_3096_;
            }
            2 => {
                v___x_3101_ = lean_unsigned_to_nat(2);
                v___x_3102_ = l_Lean_Syntax_getArg(v_x_3042_, v___x_3101_);
                v___x_3103_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__27;
                lean_inc(v___x_3102_);
                v___x_3104_ = l_Lean_Syntax_isOfKind(v___x_3102_, v___x_3103_);
                if v___x_3104_ == 0 {
                    lean_dec(v___x_3102_);
                    lean_dec(v_doc_x3f_3098_);
                    lean_dec(v_x_3042_);
                    v___x_3105_ = lean_box(1);
                    v___x_3106_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_3106_, 0, v___x_3105_);
                    lean_ctor_set(v___x_3106_, 1, v___y_3100_);
                    return v___x_3106_;
                } else {
                    v_ref_3107_ = lean_ctor_get(v___y_3099_, 5);
                    v___x_3108_ = lean_unsigned_to_nat(4);
                    v___x_3109_ = l_Lean_Syntax_getArg(v_x_3042_, v___x_3108_);
                    v___x_3110_ = lean_unsigned_to_nat(7);
                    v___x_3111_ = l_Lean_Syntax_getArg(v_x_3042_, v___x_3110_);
                    lean_dec(v_x_3042_);
                    v_simprocType_3112_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__19;
                    v___x_3113_ = 0;
                    v___x_3114_ = l_Lean_SourceInfo_fromRef(v_ref_3107_, v___x_3113_);
                    v___x_3115_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__21;
                    v___x_3116_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__22;
                    v___x_3117_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__24;
                    v___x_3118_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__26;
                    v___x_3119_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27), core::ptr::addr_of_mut!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27_once), _init_l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27);
                    if lean_obj_tag(v_doc_x3f_3098_) == 1 {
                        v_val_3120_ = lean_ctor_get(v_doc_x3f_3098_, 0);
                        lean_inc(v_val_3120_);
                        lean_dec_ref_known(v_doc_x3f_3098_, 1);
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
                        lean_dec(v_doc_x3f_3098_);
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
    mut v_x_3141_: *mut LeanObject,
    mut v_a_3142_: *mut LeanObject,
    mut v_a_3143_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3144_: *mut LeanObject = core::ptr::null_mut();
    v_res_3144_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Builtin__simproc__decl___x28___x29_x3a_x3d____1(v_x_3141_, v_a_3142_, v_a_3143_);
    lean_dec_ref(v_a_3142_);
    return v_res_3144_;
}
pub unsafe fn l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Builtin__dsimproc__decl___x28___x29_x3a_x3d____1(
    mut v_x_3145_: *mut LeanObject,
    mut v_a_3146_: *mut LeanObject,
    mut v_a_3147_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_3201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: u8 = 0;
    let mut v___x_3208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_simprocType_3215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3216_: u8 = 0;
    let mut v___x_3217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: u8 = 0;
    let mut v___x_3228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: u8 = 0;
    let mut v___x_3233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3234_: u8 = 0;
    let mut v___x_3235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_3237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: u8 = 0;
    let mut v___x_3240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3148_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0;
                v___x_3149_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1;
                v___x_3226_ = l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__1;
                lean_inc(v_x_3145_);
                v___x_3227_ = l_Lean_Syntax_isOfKind(v_x_3145_, v___x_3226_);
                if v___x_3227_ == 0 {
                    lean_dec(v_x_3145_);
                    v___x_3228_ = lean_box(1);
                    v___x_3229_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_3229_, 0, v___x_3228_);
                    lean_ctor_set(v___x_3229_, 1, v_a_3147_);
                    return v___x_3229_;
                } else {
                    v___x_3230_ = lean_unsigned_to_nat(0);
                    v___x_3231_ = l_Lean_Syntax_getArg(v_x_3145_, v___x_3230_);
                    v___x_3232_ = l_Lean_Syntax_isNone(v___x_3231_);
                    if v___x_3232_ == 0 {
                        v___x_3233_ = lean_unsigned_to_nat(1);
                        lean_inc(v___x_3231_);
                        v___x_3234_ = l_Lean_Syntax_matchesNull(v___x_3231_, v___x_3233_);
                        if v___x_3234_ == 0 {
                            lean_dec(v___x_3231_);
                            lean_dec(v_x_3145_);
                            v___x_3235_ = lean_box(1);
                            v___x_3236_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v___x_3236_, 0, v___x_3235_);
                            lean_ctor_set(v___x_3236_, 1, v_a_3147_);
                            return v___x_3236_;
                        } else {
                            v_doc_x3f_3237_ = l_Lean_Syntax_getArg(v___x_3231_, v___x_3230_);
                            lean_dec(v___x_3231_);
                            v___x_3238_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__29;
                            lean_inc(v_doc_x3f_3237_);
                            v___x_3239_ = l_Lean_Syntax_isOfKind(v_doc_x3f_3237_, v___x_3238_);
                            if v___x_3239_ == 0 {
                                lean_dec(v_doc_x3f_3237_);
                                lean_dec(v_x_3145_);
                                v___x_3240_ = lean_box(1);
                                v___x_3241_ = lean_alloc_ctor(1, 2, (0) as u32);
                                lean_ctor_set(v___x_3241_, 0, v___x_3240_);
                                lean_ctor_set(v___x_3241_, 1, v_a_3147_);
                                return v___x_3241_;
                            } else {
                                v___x_3242_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_3242_, 0, v_doc_x3f_3237_);
                                v_doc_x3f_3201_ = v___x_3242_;
                                v___y_3202_ = v_a_3146_;
                                v___y_3203_ = v_a_3147_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___x_3231_);
                        v___x_3243_ = lean_box(0);
                        v_doc_x3f_3201_ = v___x_3243_;
                        v___y_3202_ = v_a_3146_;
                        v___y_3203_ = v_a_3147_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc_ref_n(v___y_3157_, 2);
                v___x_3163_ = l_Array_append___redArg(v___y_3157_, v___y_3162_);
                lean_dec_ref(v___y_3162_);
                lean_inc_n(v___y_3159_, 4);
                lean_inc_n(v___y_3153_, 17);
                v___x_3164_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_3164_, 0, v___y_3153_);
                lean_ctor_set(v___x_3164_, 1, v___y_3159_);
                lean_ctor_set(v___x_3164_, 2, v___x_3163_);
                v___x_3165_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_3165_, 0, v___y_3153_);
                lean_ctor_set(v___x_3165_, 1, v___y_3159_);
                lean_ctor_set(v___x_3165_, 2, v___y_3157_);
                lean_inc_ref_n(v___x_3165_, 11);
                lean_inc(v___y_3161_);
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
                lean_inc_ref_n(v___y_3155_, 4);
                v___x_3168_ =
                    l_Lean_Name_mkStr4(v___x_3148_, v___x_3149_, v___y_3155_, v___x_3167_);
                v___x_3169_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__2;
                v___x_3170_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3170_, 0, v___y_3153_);
                lean_ctor_set(v___x_3170_, 1, v___x_3169_);
                v___x_3171_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__3;
                v___x_3172_ =
                    l_Lean_Name_mkStr4(v___x_3148_, v___x_3149_, v___y_3155_, v___x_3171_);
                lean_inc(v___y_3151_);
                v___x_3173_ =
                    l_Lean_Syntax_node2(v___y_3153_, v___x_3172_, v___y_3151_, v___x_3165_);
                v___x_3174_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__4;
                v___x_3175_ =
                    l_Lean_Name_mkStr4(v___x_3148_, v___x_3149_, v___y_3155_, v___x_3174_);
                v___x_3176_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__7;
                v___x_3177_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__8;
                v___x_3178_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3178_, 0, v___y_3153_);
                lean_ctor_set(v___x_3178_, 1, v___x_3177_);
                lean_inc(v___y_3160_);
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
                v___x_3186_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3186_, 0, v___y_3153_);
                lean_ctor_set(v___x_3186_, 1, v___x_3185_);
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
                lean_inc(v___y_3154_);
                v___x_3191_ =
                    l_Lean_Syntax_node2(v___y_3153_, v___y_3154_, v___x_3166_, v___x_3190_);
                v___x_3192_ = l_Lean_Parser_simprocPatternBuiltin___closed__1;
                v___x_3193_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Builtin__simproc__decl___x28___x29_x3a_x3d____1___closed__0;
                v___x_3194_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3194_, 0, v___y_3153_);
                lean_ctor_set(v___x_3194_, 1, v___x_3193_);
                v___x_3195_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__15;
                v___x_3196_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3196_, 0, v___y_3153_);
                lean_ctor_set(v___x_3196_, 1, v___x_3195_);
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
                v___x_3199_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3199_, 0, v___x_3198_);
                lean_ctor_set(v___x_3199_, 1, v___y_3156_);
                return v___x_3199_;
            }
            2 => {
                v___x_3204_ = lean_unsigned_to_nat(2);
                v___x_3205_ = l_Lean_Syntax_getArg(v_x_3145_, v___x_3204_);
                v___x_3206_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__27;
                lean_inc(v___x_3205_);
                v___x_3207_ = l_Lean_Syntax_isOfKind(v___x_3205_, v___x_3206_);
                if v___x_3207_ == 0 {
                    lean_dec(v___x_3205_);
                    lean_dec(v_doc_x3f_3201_);
                    lean_dec(v_x_3145_);
                    v___x_3208_ = lean_box(1);
                    v___x_3209_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_3209_, 0, v___x_3208_);
                    lean_ctor_set(v___x_3209_, 1, v___y_3203_);
                    return v___x_3209_;
                } else {
                    v_ref_3210_ = lean_ctor_get(v___y_3202_, 5);
                    v___x_3211_ = lean_unsigned_to_nat(4);
                    v___x_3212_ = l_Lean_Syntax_getArg(v_x_3145_, v___x_3211_);
                    v___x_3213_ = lean_unsigned_to_nat(7);
                    v___x_3214_ = l_Lean_Syntax_getArg(v_x_3145_, v___x_3213_);
                    lean_dec(v_x_3145_);
                    v_simprocType_3215_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Dsimproc__decl___x28___x29_x3a_x3d____1___closed__1;
                    v___x_3216_ = 0;
                    v___x_3217_ = l_Lean_SourceInfo_fromRef(v_ref_3210_, v___x_3216_);
                    v___x_3218_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__21;
                    v___x_3219_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__22;
                    v___x_3220_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__24;
                    v___x_3221_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__26;
                    v___x_3222_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27), core::ptr::addr_of_mut!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27_once), _init_l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27);
                    if lean_obj_tag(v_doc_x3f_3201_) == 1 {
                        v_val_3223_ = lean_ctor_get(v_doc_x3f_3201_, 0);
                        lean_inc(v_val_3223_);
                        lean_dec_ref_known(v_doc_x3f_3201_, 1);
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
                        lean_dec(v_doc_x3f_3201_);
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
    mut v_x_3244_: *mut LeanObject,
    mut v_a_3245_: *mut LeanObject,
    mut v_a_3246_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3247_: *mut LeanObject = core::ptr::null_mut();
    v_res_3247_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Builtin__dsimproc__decl___x28___x29_x3a_x3d____1(v_x_3244_, v_a_3245_, v_a_3246_);
    lean_dec_ref(v_a_3245_);
    return v_res_3247_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0(
    mut v_kind_3274_: *mut LeanObject,
    mut v_n_3275_: *mut LeanObject,
    mut v_pre_x3f_3276_: *mut LeanObject,
    mut v_as_3277_: *mut LeanObject,
    mut v_sz_3278_: usize,
    mut v_i_3279_: usize,
    mut v_b_3280_: *mut LeanObject,
    mut v___y_3281_: *mut LeanObject,
    mut v___y_3282_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: u8 = 0;
    let mut v___x_3296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3311_: usize = 0;
    let mut v___x_3312_: usize = 0;
    let mut v_fst_3315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: u8 = 0;
    let mut v___x_3322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: u8 = 0;
    let mut v___x_3327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: u8 = 0;
    let mut v___x_3329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3337_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3321_ = lean_usize_dec_lt(v_i_3279_, v_sz_3278_);
                if v___x_3321_ == 0 {
                    lean_dec(v_n_3275_);
                    lean_dec(v_kind_3274_);
                    v___x_3322_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3322_, 0, v_b_3280_);
                    lean_ctor_set(v___x_3322_, 1, v___y_3282_);
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
                            lean_inc(v___x_3330_);
                            v___x_3332_ = l_Lean_Name_append(v___x_3331_, v___x_3330_);
                            v___x_3333_ = l_Lean_Name_toString(v___x_3330_, v___x_3321_);
                            v_fst_3315_ = v___x_3332_;
                            v_snd_3316_ = v___x_3333_;
                            state = 2;
                            continue;
                        } else {
                            lean_dec(v___x_3324_);
                            v___x_3334_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__10;
                            v___x_3335_ = l_Lean_Parser_Attr_sevalprocAttr___closed__2;
                            v_fst_3315_ = v___x_3334_;
                            v_snd_3316_ = v___x_3335_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_3324_);
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
                v_ref_3287_ = lean_ctor_get(v___y_3281_, 5);
                v___x_3288_ = l_Lean_mkOptionalNode(v___y_3286_);
                v___x_3289_ = lean_unsigned_to_nat(2);
                v___x_3290_ = lean_mk_empty_array_with_capacity(v___x_3289_);
                v___x_3291_ = lean_array_push(v___x_3290_, v___y_3285_);
                v___x_3292_ = lean_array_push(v___x_3291_, v___x_3288_);
                v___x_3293_ = lean_box(2);
                v___x_3294_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_3294_, 0, v___x_3293_);
                lean_ctor_set(v___x_3294_, 1, v___y_3284_);
                lean_ctor_set(v___x_3294_, 2, v___x_3292_);
                v___x_3295_ = 0;
                v___x_3296_ = l_Lean_SourceInfo_fromRef(v_ref_3287_, v___x_3295_);
                v___x_3297_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__0;
                v___x_3298_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__1;
                lean_inc_n(v___x_3296_, 6);
                v___x_3299_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3299_, 0, v___x_3296_);
                lean_ctor_set(v___x_3299_, 1, v___x_3297_);
                v___x_3300_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__24;
                v___x_3301_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3301_, 0, v___x_3296_);
                lean_ctor_set(v___x_3301_, 1, v___x_3300_);
                v___x_3302_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__21;
                v___x_3303_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__3;
                lean_inc(v_kind_3274_);
                v___x_3304_ =
                    l_Lean_Syntax_node2(v___x_3296_, v___x_3303_, v_kind_3274_, v___x_3294_);
                v___x_3305_ = l_Lean_Syntax_node1(v___x_3296_, v___x_3302_, v___x_3304_);
                v___x_3306_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__34;
                v___x_3307_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3307_, 0, v___x_3296_);
                lean_ctor_set(v___x_3307_, 1, v___x_3306_);
                lean_inc(v_n_3275_);
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
                if lean_obj_tag(v_pre_x3f_3276_) == 0 {
                    v___x_3318_ = lean_box(0);
                    v___y_3284_ = v_fst_3315_;
                    v___y_3285_ = v___x_3317_;
                    v___y_3286_ = v___x_3318_;
                    state = 1;
                    continue;
                } else {
                    v_val_3319_ = lean_ctor_get(v_pre_x3f_3276_, 0);
                    lean_inc(v_val_3319_);
                    v___x_3320_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3320_, 0, v_val_3319_);
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
    mut v_kind_3338_: *mut LeanObject,
    mut v_n_3339_: *mut LeanObject,
    mut v_pre_x3f_3340_: *mut LeanObject,
    mut v_as_3341_: *mut LeanObject,
    mut v_sz_3342_: *mut LeanObject,
    mut v_i_3343_: *mut LeanObject,
    mut v_b_3344_: *mut LeanObject,
    mut v___y_3345_: *mut LeanObject,
    mut v___y_3346_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3347_: usize = 0;
    let mut v_i_boxed_3348_: usize = 0;
    let mut v_res_3349_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3347_ = lean_unbox_usize(v_sz_3342_);
    lean_dec(v_sz_3342_);
    v_i_boxed_3348_ = lean_unbox_usize(v_i_3343_);
    lean_dec(v_i_3343_);
    v_res_3349_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0(v_kind_3338_, v_n_3339_, v_pre_x3f_3340_, v_as_3341_, v_sz_boxed_3347_, v_i_boxed_3348_, v_b_3344_, v___y_3345_, v___y_3346_);
    lean_dec_ref(v___y_3345_);
    lean_dec_ref(v_as_3341_);
    lean_dec(v_pre_x3f_3340_);
    return v_res_3349_;
}
pub unsafe fn l___private_Init_Simproc_0__Lean_Parser_mkAttributeCmds(
    mut v_kind_3352_: *mut LeanObject,
    mut v_pre_x3f_3353_: *mut LeanObject,
    mut v_ids_x3f_3354_: *mut LeanObject,
    mut v_n_3355_: *mut LeanObject,
    mut v_a_3356_: *mut LeanObject,
    mut v_a_3357_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cmds_3358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3361_: usize = 0;
    let mut v___x_3362_: usize = 0;
    let mut v___x_3363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3368_: u8 = 0;
    let mut v___x_3370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3372_: u8 = 0;
    let mut v_a_3373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3377_: u8 = 0;
    let mut v___x_3379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3381_: u8 = 0;
    let mut v_ref_3382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3383_: u8 = 0;
    let mut v___x_3384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3411_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_cmds_3358_ = l___private_Init_Simproc_0__Lean_Parser_mkAttributeCmds___closed__0;
                if lean_obj_tag(v_ids_x3f_3354_) == 1 {
                    v_val_3359_ = lean_ctor_get(v_ids_x3f_3354_, 0);
                    v___x_3360_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_3359_);
                    v_sz_3361_ = lean_array_size(v___x_3360_);
                    v___x_3362_ = 0usize;
                    v___x_3363_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0(v_kind_3352_, v_n_3355_, v_pre_x3f_3353_, v___x_3360_, v_sz_3361_, v___x_3362_, v_cmds_3358_, v_a_3356_, v_a_3357_);
                    lean_dec_ref(v___x_3360_);
                    lean_dec(v_pre_x3f_3353_);
                    if lean_obj_tag(v___x_3363_) == 0 {
                        v_a_3364_ = lean_ctor_get(v___x_3363_, 0);
                        v_a_3365_ = lean_ctor_get(v___x_3363_, 1);
                        v_isSharedCheck_3372_ = (!lean_is_exclusive(v___x_3363_)) as u8;
                        if v_isSharedCheck_3372_ == 0 {
                            v___x_3367_ = v___x_3363_;
                            v_isShared_3368_ = v_isSharedCheck_3372_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3365_);
                            lean_inc(v_a_3364_);
                            lean_dec(v___x_3363_);
                            v___x_3367_ = lean_box(0);
                            v_isShared_3368_ = v_isSharedCheck_3372_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3373_ = lean_ctor_get(v___x_3363_, 0);
                        v_a_3374_ = lean_ctor_get(v___x_3363_, 1);
                        v_isSharedCheck_3381_ = (!lean_is_exclusive(v___x_3363_)) as u8;
                        if v_isSharedCheck_3381_ == 0 {
                            v___x_3376_ = v___x_3363_;
                            v_isShared_3377_ = v_isSharedCheck_3381_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_3374_);
                            lean_inc(v_a_3373_);
                            lean_dec(v___x_3363_);
                            v___x_3376_ = lean_box(0);
                            v_isShared_3377_ = v_isSharedCheck_3381_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_ref_3382_ = lean_ctor_get(v_a_3356_, 5);
                    v___x_3383_ = 0;
                    v___x_3384_ = l_Lean_SourceInfo_fromRef(v_ref_3382_, v___x_3383_);
                    v___x_3385_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__0;
                    v___x_3386_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__1;
                    lean_inc_n(v___x_3384_, 3);
                    v___x_3387_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_3387_, 0, v___x_3384_);
                    lean_ctor_set(v___x_3387_, 1, v___x_3385_);
                    v___x_3388_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__24;
                    v___x_3389_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_3389_, 0, v___x_3384_);
                    lean_ctor_set(v___x_3389_, 1, v___x_3388_);
                    v___x_3390_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__21;
                    v___x_3391_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__3;
                    v___x_3392_ = l_Lean_Parser_Attr_simprocAttr___closed__2;
                    v___x_3393_ = l_Lean_Parser_Attr_simprocAttr___closed__3;
                    v___x_3394_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_3394_, 0, v___x_3384_);
                    lean_ctor_set(v___x_3394_, 1, v___x_3393_);
                    v___x_3395_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27), core::ptr::addr_of_mut!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27_once), _init_l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27);
                    if lean_obj_tag(v_pre_x3f_3353_) == 1 {
                        v_val_3409_ = lean_ctor_get(v_pre_x3f_3353_, 0);
                        lean_inc(v_val_3409_);
                        lean_dec_ref_known(v_pre_x3f_3353_, 1);
                        v___x_3410_ = l_Array_mkArray1___redArg(v_val_3409_);
                        v___y_3397_ = v___x_3410_;
                        state = 5;
                        continue;
                    } else {
                        lean_dec(v_pre_x3f_3353_);
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
                    v_reuseFailAlloc_3371_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3371_, 0, v_a_3364_);
                    lean_ctor_set(v_reuseFailAlloc_3371_, 1, v_a_3365_);
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
                    v_reuseFailAlloc_3380_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3380_, 0, v_a_3373_);
                    lean_ctor_set(v_reuseFailAlloc_3380_, 1, v_a_3374_);
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
                lean_dec_ref(v___y_3397_);
                lean_inc_n(v___x_3384_, 6);
                v___x_3399_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_3399_, 0, v___x_3384_);
                lean_ctor_set(v___x_3399_, 1, v___x_3390_);
                lean_ctor_set(v___x_3399_, 2, v___x_3398_);
                v___x_3400_ =
                    l_Lean_Syntax_node2(v___x_3384_, v___x_3392_, v___x_3394_, v___x_3399_);
                v___x_3401_ =
                    l_Lean_Syntax_node2(v___x_3384_, v___x_3391_, v_kind_3352_, v___x_3400_);
                v___x_3402_ = l_Lean_Syntax_node1(v___x_3384_, v___x_3390_, v___x_3401_);
                v___x_3403_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__34;
                v___x_3404_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3404_, 0, v___x_3384_);
                lean_ctor_set(v___x_3404_, 1, v___x_3403_);
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
                v___x_3408_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3408_, 0, v___x_3407_);
                lean_ctor_set(v___x_3408_, 1, v_a_3357_);
                return v___x_3408_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Simproc_0__Lean_Parser_mkAttributeCmds___boxed(
    mut v_kind_3412_: *mut LeanObject,
    mut v_pre_x3f_3413_: *mut LeanObject,
    mut v_ids_x3f_3414_: *mut LeanObject,
    mut v_n_3415_: *mut LeanObject,
    mut v_a_3416_: *mut LeanObject,
    mut v_a_3417_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3418_: *mut LeanObject = core::ptr::null_mut();
    v_res_3418_ = l___private_Init_Simproc_0__Lean_Parser_mkAttributeCmds(
        v_kind_3412_,
        v_pre_x3f_3413_,
        v_ids_x3f_3414_,
        v_n_3415_,
        v_a_3416_,
        v_a_3417_,
    );
    lean_dec_ref(v_a_3416_);
    lean_dec(v_ids_x3f_3414_);
    return v_res_3418_;
}
pub unsafe fn l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1(
    mut v_x_3426_: *mut LeanObject,
    mut v_a_3427_: *mut LeanObject,
    mut v_a_3428_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3453_: u8 = 0;
    let mut v___x_3454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3469_: u8 = 0;
    let mut v_a_3470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3474_: u8 = 0;
    let mut v___x_3476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3478_: u8 = 0;
    let mut v___x_3479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: u8 = 0;
    let mut v___x_3481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ids_x3f_3489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_3493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3495_: u8 = 0;
    let mut v___x_3496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3503_: u8 = 0;
    let mut v___x_3504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_x3f_3516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3521_: u8 = 0;
    let mut v___x_3522_: u8 = 0;
    let mut v___x_3523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ids_x3f_3526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_3530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_3534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: u8 = 0;
    let mut v___x_3537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: u8 = 0;
    let mut v___x_3542_: u8 = 0;
    let mut v___x_3543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_x3f_3545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: u8 = 0;
    let mut v___x_3550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3551_: u8 = 0;
    let mut v___x_3552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_3554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3556_: u8 = 0;
    let mut v___x_3557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3560_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3479_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__3;
                lean_inc(v_x_3426_);
                v___x_3480_ = l_Lean_Syntax_isOfKind(v_x_3426_, v___x_3479_);
                if v___x_3480_ == 0 {
                    lean_dec(v_x_3426_);
                    v___x_3481_ = lean_box(1);
                    v___x_3482_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_3482_, 0, v___x_3481_);
                    lean_ctor_set(v___x_3482_, 1, v_a_3428_);
                    return v___x_3482_;
                } else {
                    v___x_3483_ = lean_unsigned_to_nat(0);
                    v___x_3548_ = l_Lean_Syntax_getArg(v_x_3426_, v___x_3483_);
                    v___x_3549_ = l_Lean_Syntax_isNone(v___x_3548_);
                    if v___x_3549_ == 0 {
                        v___x_3550_ = lean_unsigned_to_nat(1);
                        lean_inc(v___x_3548_);
                        v___x_3551_ = l_Lean_Syntax_matchesNull(v___x_3548_, v___x_3550_);
                        if v___x_3551_ == 0 {
                            lean_dec(v___x_3548_);
                            lean_dec(v_x_3426_);
                            v___x_3552_ = lean_box(1);
                            v___x_3553_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v___x_3553_, 0, v___x_3552_);
                            lean_ctor_set(v___x_3553_, 1, v_a_3428_);
                            return v___x_3553_;
                        } else {
                            v_doc_x3f_3554_ = l_Lean_Syntax_getArg(v___x_3548_, v___x_3483_);
                            lean_dec(v___x_3548_);
                            v___x_3555_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__29;
                            lean_inc(v_doc_x3f_3554_);
                            v___x_3556_ = l_Lean_Syntax_isOfKind(v_doc_x3f_3554_, v___x_3555_);
                            if v___x_3556_ == 0 {
                                lean_dec(v_doc_x3f_3554_);
                                lean_dec(v_x_3426_);
                                v___x_3557_ = lean_box(1);
                                v___x_3558_ = lean_alloc_ctor(1, 2, (0) as u32);
                                lean_ctor_set(v___x_3558_, 0, v___x_3557_);
                                lean_ctor_set(v___x_3558_, 1, v_a_3428_);
                                return v___x_3558_;
                            } else {
                                v___x_3559_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_3559_, 0, v_doc_x3f_3554_);
                                v_doc_x3f_3530_ = v___x_3559_;
                                v___y_3531_ = v_a_3427_;
                                v___y_3532_ = v_a_3428_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___x_3548_);
                        v___x_3560_ = lean_box(0);
                        v_doc_x3f_3530_ = v___x_3560_;
                        v___y_3531_ = v_a_3427_;
                        v___y_3532_ = v_a_3428_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc_ref(v___y_3434_);
                v___x_3444_ = l_Array_append___redArg(v___y_3434_, v___y_3443_);
                lean_dec_ref(v___y_3443_);
                lean_inc(v___y_3439_);
                lean_inc_n(v___y_3441_, 2);
                v___x_3445_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_3445_, 0, v___y_3441_);
                lean_ctor_set(v___x_3445_, 1, v___y_3439_);
                lean_ctor_set(v___x_3445_, 2, v___x_3444_);
                v___x_3446_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0;
                v___x_3447_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3447_, 0, v___y_3441_);
                lean_ctor_set(v___x_3447_, 1, v___x_3446_);
                lean_inc(v___y_3435_);
                v___x_3448_ = l___private_Init_Simproc_0__Lean_Parser_mkAttributeCmds(
                    v___y_3438_,
                    v___y_3437_,
                    v___y_3433_,
                    v___y_3435_,
                    v___y_3436_,
                    v___y_3430_,
                );
                lean_dec(v___y_3433_);
                if lean_obj_tag(v___x_3448_) == 0 {
                    v_a_3449_ = lean_ctor_get(v___x_3448_, 0);
                    v_a_3450_ = lean_ctor_get(v___x_3448_, 1);
                    v_isSharedCheck_3469_ = (!lean_is_exclusive(v___x_3448_)) as u8;
                    if v_isSharedCheck_3469_ == 0 {
                        v___x_3452_ = v___x_3448_;
                        v_isShared_3453_ = v_isSharedCheck_3469_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_3450_);
                        lean_inc(v_a_3449_);
                        lean_dec(v___x_3448_);
                        v___x_3452_ = lean_box(0);
                        v_isShared_3453_ = v_isSharedCheck_3469_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v___x_3447_, 2);
                    lean_dec_ref_known(v___x_3445_, 3);
                    lean_dec(v___y_3442_);
                    lean_dec(v___y_3441_);
                    lean_dec(v___y_3435_);
                    lean_dec(v___y_3431_);
                    v_a_3470_ = lean_ctor_get(v___x_3448_, 0);
                    v_a_3471_ = lean_ctor_get(v___x_3448_, 1);
                    v_isSharedCheck_3478_ = (!lean_is_exclusive(v___x_3448_)) as u8;
                    if v_isSharedCheck_3478_ == 0 {
                        v___x_3473_ = v___x_3448_;
                        v_isShared_3474_ = v_isSharedCheck_3478_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_3471_);
                        lean_inc(v_a_3470_);
                        lean_dec(v___x_3448_);
                        v___x_3473_ = lean_box(0);
                        v_isShared_3474_ = v_isSharedCheck_3478_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3454_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__1;
                lean_inc_n(v___y_3441_, 3);
                v___x_3455_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3455_, 0, v___y_3441_);
                lean_ctor_set(v___x_3455_, 1, v___x_3454_);
                v___x_3456_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__47;
                v___x_3457_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3457_, 0, v___y_3441_);
                lean_ctor_set(v___x_3457_, 1, v___x_3456_);
                v___x_3458_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__10;
                v___x_3459_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3459_, 0, v___y_3441_);
                lean_ctor_set(v___x_3459_, 1, v___x_3458_);
                lean_inc(v___y_3432_);
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
                lean_dec(v_a_3449_);
                v___x_3464_ = lean_box(2);
                lean_inc(v___y_3439_);
                v___x_3465_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_3465_, 0, v___x_3464_);
                lean_ctor_set(v___x_3465_, 1, v___y_3439_);
                lean_ctor_set(v___x_3465_, 2, v___x_3463_);
                if v_isShared_3453_ == 0 {
                    lean_ctor_set(v___x_3452_, 0, v___x_3465_);
                    v___x_3467_ = v___x_3452_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3468_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3468_, 0, v___x_3465_);
                    lean_ctor_set(v_reuseFailAlloc_3468_, 1, v_a_3450_);
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
                    v_reuseFailAlloc_3477_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3477_, 0, v_a_3470_);
                    lean_ctor_set(v_reuseFailAlloc_3477_, 1, v_a_3471_);
                    v___x_3476_ = v_reuseFailAlloc_3477_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3476_;
            }
            6 => {
                v___x_3492_ = lean_unsigned_to_nat(5);
                v_n_3493_ = l_Lean_Syntax_getArg(v_x_3426_, v___x_3492_);
                v___x_3494_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__27;
                lean_inc(v_n_3493_);
                v___x_3495_ = l_Lean_Syntax_isOfKind(v_n_3493_, v___x_3494_);
                if v___x_3495_ == 0 {
                    lean_dec(v_n_3493_);
                    lean_dec(v_ids_x3f_3489_);
                    lean_dec(v___y_3487_);
                    lean_dec(v___y_3486_);
                    lean_dec(v___y_3485_);
                    lean_dec(v_x_3426_);
                    v___x_3496_ = lean_box(1);
                    v___x_3497_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_3497_, 0, v___x_3496_);
                    lean_ctor_set(v___x_3497_, 1, v___y_3491_);
                    return v___x_3497_;
                } else {
                    v_ref_3498_ = lean_ctor_get(v___y_3490_, 5);
                    v___x_3499_ = lean_unsigned_to_nat(7);
                    v___x_3500_ = l_Lean_Syntax_getArg(v_x_3426_, v___x_3499_);
                    v___x_3501_ = lean_unsigned_to_nat(10);
                    v___x_3502_ = l_Lean_Syntax_getArg(v_x_3426_, v___x_3501_);
                    lean_dec(v_x_3426_);
                    v___x_3503_ = 0;
                    v___x_3504_ = l_Lean_SourceInfo_fromRef(v_ref_3498_, v___x_3503_);
                    v___x_3505_ =
                        l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__1;
                    v___x_3506_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__21;
                    v___x_3507_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27), core::ptr::addr_of_mut!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27_once), _init_l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27);
                    if lean_obj_tag(v___y_3487_) == 1 {
                        v_val_3508_ = lean_ctor_get(v___y_3487_, 0);
                        lean_inc(v_val_3508_);
                        lean_dec_ref_known(v___y_3487_, 1);
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
                        lean_dec(v___y_3487_);
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
                v___x_3519_ = lean_unsigned_to_nat(4);
                v___x_3520_ = l_Lean_Syntax_getArg(v_x_3426_, v___x_3519_);
                v___x_3521_ = l_Lean_Syntax_isNone(v___x_3520_);
                if v___x_3521_ == 0 {
                    lean_inc(v___x_3520_);
                    v___x_3522_ = l_Lean_Syntax_matchesNull(v___x_3520_, v___y_3514_);
                    if v___x_3522_ == 0 {
                        lean_dec(v___x_3520_);
                        lean_dec(v_pre_x3f_3516_);
                        lean_dec(v___y_3513_);
                        lean_dec(v___y_3512_);
                        lean_dec(v_x_3426_);
                        v___x_3523_ = lean_box(1);
                        v___x_3524_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_3524_, 0, v___x_3523_);
                        lean_ctor_set(v___x_3524_, 1, v___y_3518_);
                        return v___x_3524_;
                    } else {
                        v___x_3525_ = l_Lean_Syntax_getArg(v___x_3520_, v___y_3515_);
                        lean_dec(v___x_3520_);
                        v_ids_x3f_3526_ = l_Lean_Syntax_getArgs(v___x_3525_);
                        lean_dec(v___x_3525_);
                        v___x_3527_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_3527_, 0, v_ids_x3f_3526_);
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
                    lean_dec(v___x_3520_);
                    v___x_3528_ = lean_box(0);
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
                v___x_3533_ = lean_unsigned_to_nat(1);
                v_kind_3534_ = l_Lean_Syntax_getArg(v_x_3426_, v___x_3533_);
                v___x_3535_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__2;
                lean_inc(v_kind_3534_);
                v___x_3536_ = l_Lean_Syntax_isOfKind(v_kind_3534_, v___x_3535_);
                if v___x_3536_ == 0 {
                    lean_dec(v_kind_3534_);
                    lean_dec(v_doc_x3f_3530_);
                    lean_dec(v_x_3426_);
                    v___x_3537_ = lean_box(1);
                    v___x_3538_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_3538_, 0, v___x_3537_);
                    lean_ctor_set(v___x_3538_, 1, v___y_3532_);
                    return v___x_3538_;
                } else {
                    v___x_3539_ = lean_unsigned_to_nat(3);
                    v___x_3540_ = l_Lean_Syntax_getArg(v_x_3426_, v___x_3539_);
                    v___x_3541_ = l_Lean_Syntax_isNone(v___x_3540_);
                    if v___x_3541_ == 0 {
                        lean_inc(v___x_3540_);
                        v___x_3542_ = l_Lean_Syntax_matchesNull(v___x_3540_, v___x_3533_);
                        if v___x_3542_ == 0 {
                            lean_dec(v___x_3540_);
                            lean_dec(v_kind_3534_);
                            lean_dec(v_doc_x3f_3530_);
                            lean_dec(v_x_3426_);
                            v___x_3543_ = lean_box(1);
                            v___x_3544_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v___x_3544_, 0, v___x_3543_);
                            lean_ctor_set(v___x_3544_, 1, v___y_3532_);
                            return v___x_3544_;
                        } else {
                            v_pre_x3f_3545_ = l_Lean_Syntax_getArg(v___x_3540_, v___x_3483_);
                            lean_dec(v___x_3540_);
                            v___x_3546_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_3546_, 0, v_pre_x3f_3545_);
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
                        lean_dec(v___x_3540_);
                        v___x_3547_ = lean_box(0);
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
    mut v_x_3561_: *mut LeanObject,
    mut v_a_3562_: *mut LeanObject,
    mut v_a_3563_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3564_: *mut LeanObject = core::ptr::null_mut();
    v_res_3564_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1(v_x_3561_, v_a_3562_, v_a_3563_);
    lean_dec_ref(v_a_3562_);
    return v_res_3564_;
}
pub unsafe fn l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d____1(
    mut v_x_3566_: *mut LeanObject,
    mut v_a_3567_: *mut LeanObject,
    mut v_a_3568_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3593_: u8 = 0;
    let mut v___x_3594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3609_: u8 = 0;
    let mut v_a_3610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3614_: u8 = 0;
    let mut v___x_3616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3618_: u8 = 0;
    let mut v___x_3619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3620_: u8 = 0;
    let mut v___x_3621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ids_x3f_3629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_3633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: u8 = 0;
    let mut v___x_3636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: u8 = 0;
    let mut v___x_3644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_x3f_3656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3661_: u8 = 0;
    let mut v___x_3662_: u8 = 0;
    let mut v___x_3663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ids_x3f_3666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_3670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_3674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3676_: u8 = 0;
    let mut v___x_3677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: u8 = 0;
    let mut v___x_3682_: u8 = 0;
    let mut v___x_3683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_x3f_3685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: u8 = 0;
    let mut v___x_3690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3691_: u8 = 0;
    let mut v___x_3692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_3694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3696_: u8 = 0;
    let mut v___x_3697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3700_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3619_ = l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1;
                lean_inc(v_x_3566_);
                v___x_3620_ = l_Lean_Syntax_isOfKind(v_x_3566_, v___x_3619_);
                if v___x_3620_ == 0 {
                    lean_dec(v_x_3566_);
                    v___x_3621_ = lean_box(1);
                    v___x_3622_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_3622_, 0, v___x_3621_);
                    lean_ctor_set(v___x_3622_, 1, v_a_3568_);
                    return v___x_3622_;
                } else {
                    v___x_3623_ = lean_unsigned_to_nat(0);
                    v___x_3688_ = l_Lean_Syntax_getArg(v_x_3566_, v___x_3623_);
                    v___x_3689_ = l_Lean_Syntax_isNone(v___x_3688_);
                    if v___x_3689_ == 0 {
                        v___x_3690_ = lean_unsigned_to_nat(1);
                        lean_inc(v___x_3688_);
                        v___x_3691_ = l_Lean_Syntax_matchesNull(v___x_3688_, v___x_3690_);
                        if v___x_3691_ == 0 {
                            lean_dec(v___x_3688_);
                            lean_dec(v_x_3566_);
                            v___x_3692_ = lean_box(1);
                            v___x_3693_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v___x_3693_, 0, v___x_3692_);
                            lean_ctor_set(v___x_3693_, 1, v_a_3568_);
                            return v___x_3693_;
                        } else {
                            v_doc_x3f_3694_ = l_Lean_Syntax_getArg(v___x_3688_, v___x_3623_);
                            lean_dec(v___x_3688_);
                            v___x_3695_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__29;
                            lean_inc(v_doc_x3f_3694_);
                            v___x_3696_ = l_Lean_Syntax_isOfKind(v_doc_x3f_3694_, v___x_3695_);
                            if v___x_3696_ == 0 {
                                lean_dec(v_doc_x3f_3694_);
                                lean_dec(v_x_3566_);
                                v___x_3697_ = lean_box(1);
                                v___x_3698_ = lean_alloc_ctor(1, 2, (0) as u32);
                                lean_ctor_set(v___x_3698_, 0, v___x_3697_);
                                lean_ctor_set(v___x_3698_, 1, v_a_3568_);
                                return v___x_3698_;
                            } else {
                                v___x_3699_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_3699_, 0, v_doc_x3f_3694_);
                                v_doc_x3f_3670_ = v___x_3699_;
                                v___y_3671_ = v_a_3567_;
                                v___y_3672_ = v_a_3568_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___x_3688_);
                        v___x_3700_ = lean_box(0);
                        v_doc_x3f_3670_ = v___x_3700_;
                        v___y_3671_ = v_a_3567_;
                        v___y_3672_ = v_a_3568_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc_ref(v___y_3572_);
                v___x_3584_ = l_Array_append___redArg(v___y_3572_, v___y_3583_);
                lean_dec_ref(v___y_3583_);
                lean_inc(v___y_3574_);
                lean_inc_n(v___y_3573_, 2);
                v___x_3585_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_3585_, 0, v___y_3573_);
                lean_ctor_set(v___x_3585_, 1, v___y_3574_);
                lean_ctor_set(v___x_3585_, 2, v___x_3584_);
                v___x_3586_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0;
                v___x_3587_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3587_, 0, v___y_3573_);
                lean_ctor_set(v___x_3587_, 1, v___x_3586_);
                lean_inc(v___y_3577_);
                v___x_3588_ = l___private_Init_Simproc_0__Lean_Parser_mkAttributeCmds(
                    v___y_3576_,
                    v___y_3571_,
                    v___y_3581_,
                    v___y_3577_,
                    v___y_3582_,
                    v___y_3578_,
                );
                lean_dec(v___y_3581_);
                if lean_obj_tag(v___x_3588_) == 0 {
                    v_a_3589_ = lean_ctor_get(v___x_3588_, 0);
                    v_a_3590_ = lean_ctor_get(v___x_3588_, 1);
                    v_isSharedCheck_3609_ = (!lean_is_exclusive(v___x_3588_)) as u8;
                    if v_isSharedCheck_3609_ == 0 {
                        v___x_3592_ = v___x_3588_;
                        v_isShared_3593_ = v_isSharedCheck_3609_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_3590_);
                        lean_inc(v_a_3589_);
                        lean_dec(v___x_3588_);
                        v___x_3592_ = lean_box(0);
                        v_isShared_3593_ = v_isSharedCheck_3609_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v___x_3587_, 2);
                    lean_dec_ref_known(v___x_3585_, 3);
                    lean_dec(v___y_3577_);
                    lean_dec(v___y_3575_);
                    lean_dec(v___y_3573_);
                    lean_dec(v___y_3570_);
                    v_a_3610_ = lean_ctor_get(v___x_3588_, 0);
                    v_a_3611_ = lean_ctor_get(v___x_3588_, 1);
                    v_isSharedCheck_3618_ = (!lean_is_exclusive(v___x_3588_)) as u8;
                    if v_isSharedCheck_3618_ == 0 {
                        v___x_3613_ = v___x_3588_;
                        v_isShared_3614_ = v_isSharedCheck_3618_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_3611_);
                        lean_inc(v_a_3610_);
                        lean_dec(v___x_3588_);
                        v___x_3613_ = lean_box(0);
                        v_isShared_3614_ = v_isSharedCheck_3618_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3594_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__1;
                lean_inc_n(v___y_3573_, 3);
                v___x_3595_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3595_, 0, v___y_3573_);
                lean_ctor_set(v___x_3595_, 1, v___x_3594_);
                v___x_3596_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__47;
                v___x_3597_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3597_, 0, v___y_3573_);
                lean_ctor_set(v___x_3597_, 1, v___x_3596_);
                v___x_3598_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__10;
                v___x_3599_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3599_, 0, v___y_3573_);
                lean_ctor_set(v___x_3599_, 1, v___x_3598_);
                lean_inc(v___y_3579_);
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
                lean_dec(v_a_3589_);
                v___x_3604_ = lean_box(2);
                lean_inc(v___y_3574_);
                v___x_3605_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_3605_, 0, v___x_3604_);
                lean_ctor_set(v___x_3605_, 1, v___y_3574_);
                lean_ctor_set(v___x_3605_, 2, v___x_3603_);
                if v_isShared_3593_ == 0 {
                    lean_ctor_set(v___x_3592_, 0, v___x_3605_);
                    v___x_3607_ = v___x_3592_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3608_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3608_, 0, v___x_3605_);
                    lean_ctor_set(v_reuseFailAlloc_3608_, 1, v_a_3590_);
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
                    v_reuseFailAlloc_3617_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3617_, 0, v_a_3610_);
                    lean_ctor_set(v_reuseFailAlloc_3617_, 1, v_a_3611_);
                    v___x_3616_ = v_reuseFailAlloc_3617_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3616_;
            }
            6 => {
                v___x_3632_ = lean_unsigned_to_nat(5);
                v_n_3633_ = l_Lean_Syntax_getArg(v_x_3566_, v___x_3632_);
                v___x_3634_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__27;
                lean_inc(v_n_3633_);
                v___x_3635_ = l_Lean_Syntax_isOfKind(v_n_3633_, v___x_3634_);
                if v___x_3635_ == 0 {
                    lean_dec(v_n_3633_);
                    lean_dec(v_ids_x3f_3629_);
                    lean_dec(v___y_3628_);
                    lean_dec(v___y_3626_);
                    lean_dec(v___y_3625_);
                    lean_dec(v_x_3566_);
                    v___x_3636_ = lean_box(1);
                    v___x_3637_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_3637_, 0, v___x_3636_);
                    lean_ctor_set(v___x_3637_, 1, v___y_3631_);
                    return v___x_3637_;
                } else {
                    v_ref_3638_ = lean_ctor_get(v___y_3630_, 5);
                    v___x_3639_ = lean_unsigned_to_nat(7);
                    v___x_3640_ = l_Lean_Syntax_getArg(v_x_3566_, v___x_3639_);
                    v___x_3641_ = lean_unsigned_to_nat(10);
                    v___x_3642_ = l_Lean_Syntax_getArg(v_x_3566_, v___x_3641_);
                    lean_dec(v_x_3566_);
                    v___x_3643_ = 0;
                    v___x_3644_ = l_Lean_SourceInfo_fromRef(v_ref_3638_, v___x_3643_);
                    v___x_3645_ =
                        l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__1;
                    v___x_3646_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__21;
                    v___x_3647_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27), core::ptr::addr_of_mut!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27_once), _init_l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27);
                    if lean_obj_tag(v___y_3628_) == 1 {
                        v_val_3648_ = lean_ctor_get(v___y_3628_, 0);
                        lean_inc(v_val_3648_);
                        lean_dec_ref_known(v___y_3628_, 1);
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
                        lean_dec(v___y_3628_);
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
                v___x_3659_ = lean_unsigned_to_nat(4);
                v___x_3660_ = l_Lean_Syntax_getArg(v_x_3566_, v___x_3659_);
                v___x_3661_ = l_Lean_Syntax_isNone(v___x_3660_);
                if v___x_3661_ == 0 {
                    lean_inc(v___x_3660_);
                    v___x_3662_ = l_Lean_Syntax_matchesNull(v___x_3660_, v___y_3654_);
                    if v___x_3662_ == 0 {
                        lean_dec(v___x_3660_);
                        lean_dec(v_pre_x3f_3656_);
                        lean_dec(v___y_3655_);
                        lean_dec(v___y_3652_);
                        lean_dec(v_x_3566_);
                        v___x_3663_ = lean_box(1);
                        v___x_3664_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_3664_, 0, v___x_3663_);
                        lean_ctor_set(v___x_3664_, 1, v___y_3658_);
                        return v___x_3664_;
                    } else {
                        v___x_3665_ = l_Lean_Syntax_getArg(v___x_3660_, v___y_3653_);
                        lean_dec(v___x_3660_);
                        v_ids_x3f_3666_ = l_Lean_Syntax_getArgs(v___x_3665_);
                        lean_dec(v___x_3665_);
                        v___x_3667_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_3667_, 0, v_ids_x3f_3666_);
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
                    lean_dec(v___x_3660_);
                    v___x_3668_ = lean_box(0);
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
                v___x_3673_ = lean_unsigned_to_nat(1);
                v_kind_3674_ = l_Lean_Syntax_getArg(v_x_3566_, v___x_3673_);
                v___x_3675_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__2;
                lean_inc(v_kind_3674_);
                v___x_3676_ = l_Lean_Syntax_isOfKind(v_kind_3674_, v___x_3675_);
                if v___x_3676_ == 0 {
                    lean_dec(v_kind_3674_);
                    lean_dec(v_doc_x3f_3670_);
                    lean_dec(v_x_3566_);
                    v___x_3677_ = lean_box(1);
                    v___x_3678_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_3678_, 0, v___x_3677_);
                    lean_ctor_set(v___x_3678_, 1, v___y_3672_);
                    return v___x_3678_;
                } else {
                    v___x_3679_ = lean_unsigned_to_nat(3);
                    v___x_3680_ = l_Lean_Syntax_getArg(v_x_3566_, v___x_3679_);
                    v___x_3681_ = l_Lean_Syntax_isNone(v___x_3680_);
                    if v___x_3681_ == 0 {
                        lean_inc(v___x_3680_);
                        v___x_3682_ = l_Lean_Syntax_matchesNull(v___x_3680_, v___x_3673_);
                        if v___x_3682_ == 0 {
                            lean_dec(v___x_3680_);
                            lean_dec(v_kind_3674_);
                            lean_dec(v_doc_x3f_3670_);
                            lean_dec(v_x_3566_);
                            v___x_3683_ = lean_box(1);
                            v___x_3684_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v___x_3684_, 0, v___x_3683_);
                            lean_ctor_set(v___x_3684_, 1, v___y_3672_);
                            return v___x_3684_;
                        } else {
                            v_pre_x3f_3685_ = l_Lean_Syntax_getArg(v___x_3680_, v___x_3623_);
                            lean_dec(v___x_3680_);
                            v___x_3686_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_3686_, 0, v_pre_x3f_3685_);
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
                        lean_dec(v___x_3680_);
                        v___x_3687_ = lean_box(0);
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
    mut v_x_3701_: *mut LeanObject,
    mut v_a_3702_: *mut LeanObject,
    mut v_a_3703_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3704_: *mut LeanObject = core::ptr::null_mut();
    v_res_3704_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d____1(v_x_3701_, v_a_3702_, v_a_3703_);
    lean_dec_ref(v_a_3702_);
    return v_res_3704_;
}
pub unsafe fn l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1(
    mut v_x_3706_: *mut LeanObject,
    mut v_a_3707_: *mut LeanObject,
    mut v_a_3708_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3799_: u8 = 0;
    let mut v___x_3800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_x3f_3922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: u8 = 0;
    let mut v___x_3928_: u8 = 0;
    let mut v___x_3929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3932_: u8 = 0;
    let mut v___x_3933_: u8 = 0;
    let mut v___x_3934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3938_: u8 = 0;
    let mut v___x_3939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3943_: u8 = 0;
    let mut v___x_3944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: u8 = 0;
    let mut v___x_3950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3966_: u8 = 0;
    let mut v___x_3967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3972_: u8 = 0;
    let mut v___x_3973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3990_: u8 = 0;
    let mut v___x_3991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: u8 = 0;
    let mut v___x_3999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_4007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4014_: u8 = 0;
    let mut v___x_4015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4020_: u8 = 0;
    let mut v___x_4021_: u8 = 0;
    let mut v___x_4022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_x3f_4024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4028_: u8 = 0;
    let mut v___x_4029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: u8 = 0;
    let mut v___x_4031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_4033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4035_: u8 = 0;
    let mut v___x_4036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4039_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3761_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0;
                v___x_3762_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1;
                v___x_3798_ = l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1;
                lean_inc(v_x_3706_);
                v___x_3799_ = l_Lean_Syntax_isOfKind(v_x_3706_, v___x_3798_);
                if v___x_3799_ == 0 {
                    lean_dec(v_x_3706_);
                    v___x_3800_ = lean_box(1);
                    v___x_3801_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_3801_, 0, v___x_3800_);
                    lean_ctor_set(v___x_3801_, 1, v_a_3708_);
                    return v___x_3801_;
                } else {
                    v___x_3802_ = lean_unsigned_to_nat(0);
                    v___x_4027_ = l_Lean_Syntax_getArg(v_x_3706_, v___x_3802_);
                    v___x_4028_ = l_Lean_Syntax_isNone(v___x_4027_);
                    if v___x_4028_ == 0 {
                        v___x_4029_ = lean_unsigned_to_nat(1);
                        lean_inc(v___x_4027_);
                        v___x_4030_ = l_Lean_Syntax_matchesNull(v___x_4027_, v___x_4029_);
                        if v___x_4030_ == 0 {
                            lean_dec(v___x_4027_);
                            lean_dec(v_x_3706_);
                            v___x_4031_ = lean_box(1);
                            v___x_4032_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v___x_4032_, 0, v___x_4031_);
                            lean_ctor_set(v___x_4032_, 1, v_a_3708_);
                            return v___x_4032_;
                        } else {
                            v_doc_x3f_4033_ = l_Lean_Syntax_getArg(v___x_4027_, v___x_3802_);
                            lean_dec(v___x_4027_);
                            v___x_4034_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__29;
                            lean_inc(v_doc_x3f_4033_);
                            v___x_4035_ = l_Lean_Syntax_isOfKind(v_doc_x3f_4033_, v___x_4034_);
                            if v___x_4035_ == 0 {
                                lean_dec(v_doc_x3f_4033_);
                                lean_dec(v_x_3706_);
                                v___x_4036_ = lean_box(1);
                                v___x_4037_ = lean_alloc_ctor(1, 2, (0) as u32);
                                lean_ctor_set(v___x_4037_, 0, v___x_4036_);
                                lean_ctor_set(v___x_4037_, 1, v_a_3708_);
                                return v___x_4037_;
                            } else {
                                v___x_4038_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_4038_, 0, v_doc_x3f_4033_);
                                v_doc_x3f_4007_ = v___x_4038_;
                                v___y_4008_ = v_a_3707_;
                                v___y_4009_ = v_a_3708_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___x_4027_);
                        v___x_4039_ = lean_box(0);
                        v_doc_x3f_4007_ = v___x_4039_;
                        v___y_4008_ = v_a_3707_;
                        v___y_4009_ = v_a_3708_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc_ref(v___y_3721_);
                v___x_3724_ = l_Array_append___redArg(v___y_3721_, v___y_3723_);
                lean_dec_ref(v___y_3723_);
                lean_inc_n(v___y_3712_, 4);
                lean_inc_n(v___y_3719_, 7);
                v___x_3725_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_3725_, 0, v___y_3719_);
                lean_ctor_set(v___x_3725_, 1, v___y_3712_);
                lean_ctor_set(v___x_3725_, 2, v___x_3724_);
                lean_inc(v___y_3715_);
                v___x_3726_ =
                    l_Lean_Syntax_node2(v___y_3719_, v___y_3715_, v___y_3718_, v___x_3725_);
                v___x_3727_ =
                    l_Lean_Syntax_node2(v___y_3719_, v___y_3713_, v___y_3710_, v___x_3726_);
                v___x_3728_ = l_Lean_Syntax_node1(v___y_3719_, v___y_3712_, v___x_3727_);
                v___x_3729_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__34;
                v___x_3730_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3730_, 0, v___y_3719_);
                lean_ctor_set(v___x_3730_, 1, v___x_3729_);
                v___x_3731_ = l_Lean_Syntax_node1(v___y_3719_, v___y_3712_, v___y_3717_);
                lean_inc(v___y_3711_);
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
                v___x_3734_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3734_, 0, v___x_3733_);
                lean_ctor_set(v___x_3734_, 1, v___y_3716_);
                return v___x_3734_;
            }
            2 => {
                lean_inc_ref(v___y_3748_);
                v___x_3750_ = l_Array_append___redArg(v___y_3748_, v___y_3749_);
                lean_dec_ref(v___y_3749_);
                lean_inc_n(v___y_3740_, 4);
                lean_inc_n(v___y_3744_, 7);
                v___x_3751_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_3751_, 0, v___y_3744_);
                lean_ctor_set(v___x_3751_, 1, v___y_3740_);
                lean_ctor_set(v___x_3751_, 2, v___x_3750_);
                lean_inc(v___y_3738_);
                v___x_3752_ =
                    l_Lean_Syntax_node2(v___y_3744_, v___y_3738_, v___y_3739_, v___x_3751_);
                v___x_3753_ =
                    l_Lean_Syntax_node2(v___y_3744_, v___y_3742_, v___y_3736_, v___x_3752_);
                v___x_3754_ = l_Lean_Syntax_node1(v___y_3744_, v___y_3740_, v___x_3753_);
                v___x_3755_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__34;
                v___x_3756_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3756_, 0, v___y_3744_);
                lean_ctor_set(v___x_3756_, 1, v___x_3755_);
                v___x_3757_ = l_Lean_Syntax_node1(v___y_3744_, v___y_3740_, v___y_3745_);
                lean_inc(v___y_3746_);
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
                v___x_3760_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3760_, 0, v___x_3759_);
                lean_ctor_set(v___x_3760_, 1, v___y_3741_);
                return v___x_3760_;
            }
            3 => {
                lean_inc_ref(v___y_3768_);
                v___x_3779_ = l_Array_append___redArg(v___y_3768_, v___y_3778_);
                lean_dec_ref(v___y_3778_);
                lean_inc_n(v___y_3767_, 5);
                lean_inc_n(v___y_3765_, 12);
                v___x_3780_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_3780_, 0, v___y_3765_);
                lean_ctor_set(v___x_3780_, 1, v___y_3767_);
                lean_ctor_set(v___x_3780_, 2, v___x_3779_);
                lean_inc_ref(v___x_3780_);
                lean_inc(v___y_3770_);
                v___x_3781_ =
                    l_Lean_Syntax_node2(v___y_3765_, v___y_3770_, v___y_3766_, v___x_3780_);
                lean_inc(v___y_3764_);
                lean_inc(v___y_3769_);
                v___x_3782_ =
                    l_Lean_Syntax_node2(v___y_3765_, v___y_3769_, v___y_3764_, v___x_3781_);
                v___x_3783_ = l_Lean_Syntax_node1(v___y_3765_, v___y_3767_, v___x_3782_);
                v___x_3784_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__34;
                v___x_3785_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3785_, 0, v___y_3765_);
                lean_ctor_set(v___x_3785_, 1, v___x_3784_);
                v___x_3786_ = l_Lean_Syntax_node1(v___y_3765_, v___y_3767_, v___y_3773_);
                lean_inc(v___x_3786_);
                lean_inc_ref(v___x_3785_);
                lean_inc(v___y_3776_);
                lean_inc(v___y_3777_);
                lean_inc_n(v___y_3775_, 2);
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
                lean_inc_ref(v___y_3771_);
                v___x_3789_ =
                    l_Lean_Name_mkStr4(v___x_3761_, v___x_3762_, v___y_3771_, v___x_3788_);
                v___x_3790_ = l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__2;
                v___x_3791_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3791_, 0, v___y_3765_);
                lean_ctor_set(v___x_3791_, 1, v___x_3790_);
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
                v___x_3797_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3797_, 0, v___x_3796_);
                lean_ctor_set(v___x_3797_, 1, v___y_3774_);
                return v___x_3797_;
            }
            4 => {
                lean_inc_ref(v___y_3812_);
                v___x_3816_ = l_Array_append___redArg(v___y_3812_, v___y_3815_);
                lean_dec_ref(v___y_3815_);
                lean_inc(v___y_3811_);
                lean_inc_n(v___y_3810_, 9);
                v___x_3817_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_3817_, 0, v___y_3810_);
                lean_ctor_set(v___x_3817_, 1, v___y_3811_);
                lean_ctor_set(v___x_3817_, 2, v___x_3816_);
                v___x_3818_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0;
                v___x_3819_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3819_, 0, v___y_3810_);
                lean_ctor_set(v___x_3819_, 1, v___x_3818_);
                v___x_3820_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__1;
                v___x_3821_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3821_, 0, v___y_3810_);
                lean_ctor_set(v___x_3821_, 1, v___x_3820_);
                v___x_3822_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__47;
                v___x_3823_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3823_, 0, v___y_3810_);
                lean_ctor_set(v___x_3823_, 1, v___x_3822_);
                v___x_3824_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__10;
                v___x_3825_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3825_, 0, v___y_3810_);
                lean_ctor_set(v___x_3825_, 1, v___x_3824_);
                lean_inc(v___y_3806_);
                lean_inc(v___y_3814_);
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
                v___x_3829_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3829_, 0, v___y_3810_);
                lean_ctor_set(v___x_3829_, 1, v___x_3827_);
                v___x_3830_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__24;
                v___x_3831_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3831_, 0, v___y_3810_);
                lean_ctor_set(v___x_3831_, 1, v___x_3830_);
                v___x_3832_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__2;
                lean_inc_ref(v___y_3808_);
                v___x_3833_ =
                    l_Lean_Name_mkStr4(v___x_3761_, v___x_3762_, v___y_3808_, v___x_3832_);
                v___x_3834_ = l_Lean_Parser_Attr_simprocAttr___closed__0;
                v___x_3835_ = l_Lean_Parser_Attr_simprocBuiltinAttr___closed__1;
                v___x_3836_ = l_Lean_Parser_Attr_simprocBuiltinAttr___closed__2;
                v___x_3837_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3837_, 0, v___y_3810_);
                lean_ctor_set(v___x_3837_, 1, v___x_3836_);
                if lean_obj_tag(v___y_3813_) == 1 {
                    v_val_3838_ = lean_ctor_get(v___y_3813_, 0);
                    lean_inc(v_val_3838_);
                    lean_dec_ref_known(v___y_3813_, 1);
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
                    lean_dec(v___y_3813_);
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
                lean_inc_ref(v___y_3849_);
                v___x_3854_ = l_Array_append___redArg(v___y_3849_, v___y_3853_);
                lean_dec_ref(v___y_3853_);
                lean_inc(v___y_3845_);
                lean_inc_n(v___y_3848_, 9);
                v___x_3855_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_3855_, 0, v___y_3848_);
                lean_ctor_set(v___x_3855_, 1, v___y_3845_);
                lean_ctor_set(v___x_3855_, 2, v___x_3854_);
                v___x_3856_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0;
                v___x_3857_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3857_, 0, v___y_3848_);
                lean_ctor_set(v___x_3857_, 1, v___x_3856_);
                v___x_3858_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__1;
                v___x_3859_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3859_, 0, v___y_3848_);
                lean_ctor_set(v___x_3859_, 1, v___x_3858_);
                v___x_3860_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__47;
                v___x_3861_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3861_, 0, v___y_3848_);
                lean_ctor_set(v___x_3861_, 1, v___x_3860_);
                v___x_3862_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__10;
                v___x_3863_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3863_, 0, v___y_3848_);
                lean_ctor_set(v___x_3863_, 1, v___x_3862_);
                lean_inc(v___y_3846_);
                lean_inc(v___y_3850_);
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
                v___x_3867_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3867_, 0, v___y_3848_);
                lean_ctor_set(v___x_3867_, 1, v___x_3865_);
                v___x_3868_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__24;
                v___x_3869_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3869_, 0, v___y_3848_);
                lean_ctor_set(v___x_3869_, 1, v___x_3868_);
                v___x_3870_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__2;
                lean_inc_ref(v___y_3844_);
                v___x_3871_ =
                    l_Lean_Name_mkStr4(v___x_3761_, v___x_3762_, v___y_3844_, v___x_3870_);
                v___x_3872_ = l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__1;
                v___x_3873_ = l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__2;
                v___x_3874_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3874_, 0, v___y_3848_);
                lean_ctor_set(v___x_3874_, 1, v___x_3873_);
                if lean_obj_tag(v___y_3852_) == 1 {
                    v_val_3875_ = lean_ctor_get(v___y_3852_, 0);
                    lean_inc(v_val_3875_);
                    lean_dec_ref_known(v___y_3852_, 1);
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
                    lean_dec(v___y_3852_);
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
                lean_inc_ref(v___y_3889_);
                v___x_3891_ = l_Array_append___redArg(v___y_3889_, v___y_3890_);
                lean_dec_ref(v___y_3890_);
                lean_inc(v___y_3882_);
                lean_inc_n(v___y_3883_, 9);
                v___x_3892_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_3892_, 0, v___y_3883_);
                lean_ctor_set(v___x_3892_, 1, v___y_3882_);
                lean_ctor_set(v___x_3892_, 2, v___x_3891_);
                v___x_3893_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0;
                v___x_3894_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3894_, 0, v___y_3883_);
                lean_ctor_set(v___x_3894_, 1, v___x_3893_);
                v___x_3895_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__1;
                v___x_3896_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3896_, 0, v___y_3883_);
                lean_ctor_set(v___x_3896_, 1, v___x_3895_);
                v___x_3897_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__47;
                v___x_3898_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3898_, 0, v___y_3883_);
                lean_ctor_set(v___x_3898_, 1, v___x_3897_);
                v___x_3899_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__10;
                v___x_3900_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3900_, 0, v___y_3883_);
                lean_ctor_set(v___x_3900_, 1, v___x_3899_);
                lean_inc(v___y_3884_);
                lean_inc(v___y_3885_);
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
                v___x_3904_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3904_, 0, v___y_3883_);
                lean_ctor_set(v___x_3904_, 1, v___x_3902_);
                v___x_3905_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__24;
                v___x_3906_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3906_, 0, v___y_3883_);
                lean_ctor_set(v___x_3906_, 1, v___x_3905_);
                v___x_3907_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__2;
                lean_inc_ref(v___y_3881_);
                v___x_3908_ =
                    l_Lean_Name_mkStr4(v___x_3761_, v___x_3762_, v___y_3881_, v___x_3907_);
                v___x_3909_ = l_Lean_Parser_Attr_simprocBuiltinAttr___closed__1;
                v___x_3910_ = l_Lean_Parser_Attr_simprocBuiltinAttr___closed__2;
                v___x_3911_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3911_, 0, v___y_3883_);
                lean_ctor_set(v___x_3911_, 1, v___x_3910_);
                if lean_obj_tag(v___y_3886_) == 1 {
                    v_val_3912_ = lean_ctor_get(v___y_3886_, 0);
                    lean_inc(v_val_3912_);
                    lean_dec_ref_known(v___y_3886_, 1);
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
                    lean_dec(v___y_3886_);
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
                v___x_3925_ = lean_unsigned_to_nat(4);
                v___x_3926_ = l_Lean_Syntax_getArg(v_x_3706_, v___x_3925_);
                lean_inc(v___x_3926_);
                v___x_3927_ = l_Lean_Syntax_matchesNull(v___x_3926_, v___x_3802_);
                if v___x_3927_ == 0 {
                    lean_inc(v___x_3926_);
                    v___x_3928_ = l_Lean_Syntax_matchesNull(v___x_3926_, v___y_3921_);
                    if v___x_3928_ == 0 {
                        lean_dec(v___x_3926_);
                        lean_dec(v_pre_x3f_3922_);
                        lean_dec(v___y_3920_);
                        lean_dec(v___y_3916_);
                        lean_dec(v_x_3706_);
                        v___x_3929_ = lean_box(1);
                        v___x_3930_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_3930_, 0, v___x_3929_);
                        lean_ctor_set(v___x_3930_, 1, v___y_3924_);
                        return v___x_3930_;
                    } else {
                        v___x_3931_ = l_Lean_Syntax_getArg(v___x_3926_, v___y_3919_);
                        lean_dec(v___x_3926_);
                        lean_inc(v___x_3931_);
                        v___x_3932_ = l_Lean_Syntax_matchesNull(v___x_3931_, v___y_3919_);
                        if v___x_3932_ == 0 {
                            lean_inc(v___x_3931_);
                            v___x_3933_ = l_Lean_Syntax_matchesNull(v___x_3931_, v___y_3921_);
                            if v___x_3933_ == 0 {
                                lean_dec(v___x_3931_);
                                lean_dec(v_pre_x3f_3922_);
                                lean_dec(v___y_3920_);
                                lean_dec(v___y_3916_);
                                lean_dec(v_x_3706_);
                                v___x_3934_ = lean_box(1);
                                v___x_3935_ = lean_alloc_ctor(1, 2, (0) as u32);
                                lean_ctor_set(v___x_3935_, 0, v___x_3934_);
                                lean_ctor_set(v___x_3935_, 1, v___y_3924_);
                                return v___x_3935_;
                            } else {
                                v___x_3936_ = l_Lean_Syntax_getArg(v___x_3931_, v___x_3802_);
                                v___x_3937_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__5;
                                v___x_3938_ = l_Lean_Syntax_matchesIdent(v___x_3936_, v___x_3937_);
                                lean_dec(v___x_3936_);
                                if v___x_3938_ == 0 {
                                    lean_dec(v___x_3931_);
                                    lean_dec(v_pre_x3f_3922_);
                                    lean_dec(v___y_3920_);
                                    lean_dec(v___y_3916_);
                                    lean_dec(v_x_3706_);
                                    v___x_3939_ = lean_box(1);
                                    v___x_3940_ = lean_alloc_ctor(1, 2, (0) as u32);
                                    lean_ctor_set(v___x_3940_, 0, v___x_3939_);
                                    lean_ctor_set(v___x_3940_, 1, v___y_3924_);
                                    return v___x_3940_;
                                } else {
                                    v___x_3941_ = l_Lean_Syntax_getArg(v___x_3931_, v___y_3917_);
                                    lean_dec(v___x_3931_);
                                    v___x_3942_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__7;
                                    v___x_3943_ =
                                        l_Lean_Syntax_matchesIdent(v___x_3941_, v___x_3942_);
                                    lean_dec(v___x_3941_);
                                    if v___x_3943_ == 0 {
                                        lean_dec(v_pre_x3f_3922_);
                                        lean_dec(v___y_3920_);
                                        lean_dec(v___y_3916_);
                                        lean_dec(v_x_3706_);
                                        v___x_3944_ = lean_box(1);
                                        v___x_3945_ = lean_alloc_ctor(1, 2, (0) as u32);
                                        lean_ctor_set(v___x_3945_, 0, v___x_3944_);
                                        lean_ctor_set(v___x_3945_, 1, v___y_3924_);
                                        return v___x_3945_;
                                    } else {
                                        v___x_3946_ = lean_unsigned_to_nat(5);
                                        v___x_3947_ = l_Lean_Syntax_getArg(v_x_3706_, v___x_3946_);
                                        v___x_3948_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__27;
                                        lean_inc(v___x_3947_);
                                        v___x_3949_ =
                                            l_Lean_Syntax_isOfKind(v___x_3947_, v___x_3948_);
                                        if v___x_3949_ == 0 {
                                            lean_dec(v___x_3947_);
                                            lean_dec(v_pre_x3f_3922_);
                                            lean_dec(v___y_3920_);
                                            lean_dec(v___y_3916_);
                                            lean_dec(v_x_3706_);
                                            v___x_3950_ = lean_box(1);
                                            v___x_3951_ = lean_alloc_ctor(1, 2, (0) as u32);
                                            lean_ctor_set(v___x_3951_, 0, v___x_3950_);
                                            lean_ctor_set(v___x_3951_, 1, v___y_3924_);
                                            return v___x_3951_;
                                        } else {
                                            v_ref_3952_ = lean_ctor_get(v___y_3923_, 5);
                                            v___x_3953_ = lean_unsigned_to_nat(7);
                                            v___x_3954_ =
                                                l_Lean_Syntax_getArg(v_x_3706_, v___x_3953_);
                                            v___x_3955_ = lean_unsigned_to_nat(10);
                                            v___x_3956_ =
                                                l_Lean_Syntax_getArg(v_x_3706_, v___x_3955_);
                                            lean_dec(v_x_3706_);
                                            v___x_3957_ =
                                                l_Lean_SourceInfo_fromRef(v_ref_3952_, v___x_3932_);
                                            v___x_3958_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__21;
                                            v___x_3959_ = l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__1;
                                            v___x_3960_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27), core::ptr::addr_of_mut!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27_once), _init_l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27);
                                            if lean_obj_tag(v___y_3920_) == 1 {
                                                v_val_3961_ = lean_ctor_get(v___y_3920_, 0);
                                                lean_inc(v_val_3961_);
                                                lean_dec_ref_known(v___y_3920_, 1);
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
                                                lean_dec(v___y_3920_);
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
                            lean_dec(v___x_3931_);
                            v___x_3965_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__7;
                            v___x_3966_ = l_Lean_Syntax_matchesIdent(v___x_3964_, v___x_3965_);
                            lean_dec(v___x_3964_);
                            if v___x_3966_ == 0 {
                                lean_dec(v_pre_x3f_3922_);
                                lean_dec(v___y_3920_);
                                lean_dec(v___y_3916_);
                                lean_dec(v_x_3706_);
                                v___x_3967_ = lean_box(1);
                                v___x_3968_ = lean_alloc_ctor(1, 2, (0) as u32);
                                lean_ctor_set(v___x_3968_, 0, v___x_3967_);
                                lean_ctor_set(v___x_3968_, 1, v___y_3924_);
                                return v___x_3968_;
                            } else {
                                v___x_3969_ = lean_unsigned_to_nat(5);
                                v___x_3970_ = l_Lean_Syntax_getArg(v_x_3706_, v___x_3969_);
                                v___x_3971_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__27;
                                lean_inc(v___x_3970_);
                                v___x_3972_ = l_Lean_Syntax_isOfKind(v___x_3970_, v___x_3971_);
                                if v___x_3972_ == 0 {
                                    lean_dec(v___x_3970_);
                                    lean_dec(v_pre_x3f_3922_);
                                    lean_dec(v___y_3920_);
                                    lean_dec(v___y_3916_);
                                    lean_dec(v_x_3706_);
                                    v___x_3973_ = lean_box(1);
                                    v___x_3974_ = lean_alloc_ctor(1, 2, (0) as u32);
                                    lean_ctor_set(v___x_3974_, 0, v___x_3973_);
                                    lean_ctor_set(v___x_3974_, 1, v___y_3924_);
                                    return v___x_3974_;
                                } else {
                                    v_ref_3975_ = lean_ctor_get(v___y_3923_, 5);
                                    v___x_3976_ = lean_unsigned_to_nat(7);
                                    v___x_3977_ = l_Lean_Syntax_getArg(v_x_3706_, v___x_3976_);
                                    v___x_3978_ = lean_unsigned_to_nat(10);
                                    v___x_3979_ = l_Lean_Syntax_getArg(v_x_3706_, v___x_3978_);
                                    lean_dec(v_x_3706_);
                                    v___x_3980_ =
                                        l_Lean_SourceInfo_fromRef(v_ref_3975_, v___x_3927_);
                                    v___x_3981_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__21;
                                    v___x_3982_ = l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__1;
                                    v___x_3983_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27), core::ptr::addr_of_mut!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27_once), _init_l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27);
                                    if lean_obj_tag(v___y_3920_) == 1 {
                                        v_val_3984_ = lean_ctor_get(v___y_3920_, 0);
                                        lean_inc(v_val_3984_);
                                        lean_dec_ref_known(v___y_3920_, 1);
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
                                        lean_dec(v___y_3920_);
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
                    lean_dec(v___x_3926_);
                    v___x_3987_ = lean_unsigned_to_nat(5);
                    v___x_3988_ = l_Lean_Syntax_getArg(v_x_3706_, v___x_3987_);
                    v___x_3989_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__27;
                    lean_inc(v___x_3988_);
                    v___x_3990_ = l_Lean_Syntax_isOfKind(v___x_3988_, v___x_3989_);
                    if v___x_3990_ == 0 {
                        lean_dec(v___x_3988_);
                        lean_dec(v_pre_x3f_3922_);
                        lean_dec(v___y_3920_);
                        lean_dec(v___y_3916_);
                        lean_dec(v_x_3706_);
                        v___x_3991_ = lean_box(1);
                        v___x_3992_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_3992_, 0, v___x_3991_);
                        lean_ctor_set(v___x_3992_, 1, v___y_3924_);
                        return v___x_3992_;
                    } else {
                        v_ref_3993_ = lean_ctor_get(v___y_3923_, 5);
                        v___x_3994_ = lean_unsigned_to_nat(7);
                        v___x_3995_ = l_Lean_Syntax_getArg(v_x_3706_, v___x_3994_);
                        v___x_3996_ = lean_unsigned_to_nat(10);
                        v___x_3997_ = l_Lean_Syntax_getArg(v_x_3706_, v___x_3996_);
                        lean_dec(v_x_3706_);
                        v___x_3998_ = 0;
                        v___x_3999_ = l_Lean_SourceInfo_fromRef(v_ref_3993_, v___x_3998_);
                        v___x_4000_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__21;
                        v___x_4001_ = l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__1;
                        v___x_4002_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27), core::ptr::addr_of_mut!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27_once), _init_l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27);
                        if lean_obj_tag(v___y_3920_) == 1 {
                            v_val_4003_ = lean_ctor_get(v___y_3920_, 0);
                            lean_inc(v_val_4003_);
                            lean_dec_ref_known(v___y_3920_, 1);
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
                            lean_dec(v___y_3920_);
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
                v___x_4010_ = lean_unsigned_to_nat(1);
                v___x_4011_ = l_Lean_Syntax_getArg(v_x_3706_, v___x_4010_);
                v___x_4012_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__5;
                v___x_4013_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__2;
                lean_inc(v___x_4011_);
                v___x_4014_ = l_Lean_Syntax_isOfKind(v___x_4011_, v___x_4013_);
                if v___x_4014_ == 0 {
                    lean_dec(v___x_4011_);
                    lean_dec(v_doc_x3f_4007_);
                    lean_dec(v_x_3706_);
                    v___x_4015_ = lean_box(1);
                    v___x_4016_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_4016_, 0, v___x_4015_);
                    lean_ctor_set(v___x_4016_, 1, v___y_4009_);
                    return v___x_4016_;
                } else {
                    v___x_4017_ = lean_unsigned_to_nat(2);
                    v___x_4018_ = lean_unsigned_to_nat(3);
                    v___x_4019_ = l_Lean_Syntax_getArg(v_x_3706_, v___x_4018_);
                    v___x_4020_ = l_Lean_Syntax_isNone(v___x_4019_);
                    if v___x_4020_ == 0 {
                        lean_inc(v___x_4019_);
                        v___x_4021_ = l_Lean_Syntax_matchesNull(v___x_4019_, v___x_4010_);
                        if v___x_4021_ == 0 {
                            lean_dec(v___x_4019_);
                            lean_dec(v___x_4011_);
                            lean_dec(v_doc_x3f_4007_);
                            lean_dec(v_x_3706_);
                            v___x_4022_ = lean_box(1);
                            v___x_4023_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v___x_4023_, 0, v___x_4022_);
                            lean_ctor_set(v___x_4023_, 1, v___y_4009_);
                            return v___x_4023_;
                        } else {
                            v_pre_x3f_4024_ = l_Lean_Syntax_getArg(v___x_4019_, v___x_3802_);
                            lean_dec(v___x_4019_);
                            v___x_4025_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_4025_, 0, v_pre_x3f_4024_);
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
                        lean_dec(v___x_4019_);
                        v___x_4026_ = lean_box(0);
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
    mut v_x_4040_: *mut LeanObject,
    mut v_a_4041_: *mut LeanObject,
    mut v_a_4042_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4043_: *mut LeanObject = core::ptr::null_mut();
    v_res_4043_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1(v_x_4040_, v_a_4041_, v_a_4042_);
    lean_dec_ref(v_a_4041_);
    return v_res_4043_;
}
pub unsafe fn l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d____1(
    mut v_x_4045_: *mut LeanObject,
    mut v_a_4046_: *mut LeanObject,
    mut v_a_4047_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4138_: u8 = 0;
    let mut v___x_4139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_x3f_4261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4266_: u8 = 0;
    let mut v___x_4267_: u8 = 0;
    let mut v___x_4268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4271_: u8 = 0;
    let mut v___x_4272_: u8 = 0;
    let mut v___x_4273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4277_: u8 = 0;
    let mut v___x_4278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4282_: u8 = 0;
    let mut v___x_4283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4288_: u8 = 0;
    let mut v___x_4289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4305_: u8 = 0;
    let mut v___x_4306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4311_: u8 = 0;
    let mut v___x_4312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: u8 = 0;
    let mut v___x_4330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4337_: u8 = 0;
    let mut v___x_4338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_4346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4353_: u8 = 0;
    let mut v___x_4354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4359_: u8 = 0;
    let mut v___x_4360_: u8 = 0;
    let mut v___x_4361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_x3f_4363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4367_: u8 = 0;
    let mut v___x_4368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4369_: u8 = 0;
    let mut v___x_4370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_4372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4374_: u8 = 0;
    let mut v___x_4375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4100_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0;
                v___x_4101_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1;
                v___x_4137_ = l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1;
                lean_inc(v_x_4045_);
                v___x_4138_ = l_Lean_Syntax_isOfKind(v_x_4045_, v___x_4137_);
                if v___x_4138_ == 0 {
                    lean_dec(v_x_4045_);
                    v___x_4139_ = lean_box(1);
                    v___x_4140_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_4140_, 0, v___x_4139_);
                    lean_ctor_set(v___x_4140_, 1, v_a_4047_);
                    return v___x_4140_;
                } else {
                    v___x_4141_ = lean_unsigned_to_nat(0);
                    v___x_4366_ = l_Lean_Syntax_getArg(v_x_4045_, v___x_4141_);
                    v___x_4367_ = l_Lean_Syntax_isNone(v___x_4366_);
                    if v___x_4367_ == 0 {
                        v___x_4368_ = lean_unsigned_to_nat(1);
                        lean_inc(v___x_4366_);
                        v___x_4369_ = l_Lean_Syntax_matchesNull(v___x_4366_, v___x_4368_);
                        if v___x_4369_ == 0 {
                            lean_dec(v___x_4366_);
                            lean_dec(v_x_4045_);
                            v___x_4370_ = lean_box(1);
                            v___x_4371_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v___x_4371_, 0, v___x_4370_);
                            lean_ctor_set(v___x_4371_, 1, v_a_4047_);
                            return v___x_4371_;
                        } else {
                            v_doc_x3f_4372_ = l_Lean_Syntax_getArg(v___x_4366_, v___x_4141_);
                            lean_dec(v___x_4366_);
                            v___x_4373_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__29;
                            lean_inc(v_doc_x3f_4372_);
                            v___x_4374_ = l_Lean_Syntax_isOfKind(v_doc_x3f_4372_, v___x_4373_);
                            if v___x_4374_ == 0 {
                                lean_dec(v_doc_x3f_4372_);
                                lean_dec(v_x_4045_);
                                v___x_4375_ = lean_box(1);
                                v___x_4376_ = lean_alloc_ctor(1, 2, (0) as u32);
                                lean_ctor_set(v___x_4376_, 0, v___x_4375_);
                                lean_ctor_set(v___x_4376_, 1, v_a_4047_);
                                return v___x_4376_;
                            } else {
                                v___x_4377_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_4377_, 0, v_doc_x3f_4372_);
                                v_doc_x3f_4346_ = v___x_4377_;
                                v___y_4347_ = v_a_4046_;
                                v___y_4348_ = v_a_4047_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___x_4366_);
                        v___x_4378_ = lean_box(0);
                        v_doc_x3f_4346_ = v___x_4378_;
                        v___y_4347_ = v_a_4046_;
                        v___y_4348_ = v_a_4047_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc_ref(v___y_4056_);
                v___x_4063_ = l_Array_append___redArg(v___y_4056_, v___y_4062_);
                lean_dec_ref(v___y_4062_);
                lean_inc_n(v___y_4054_, 4);
                lean_inc_n(v___y_4055_, 7);
                v___x_4064_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_4064_, 0, v___y_4055_);
                lean_ctor_set(v___x_4064_, 1, v___y_4054_);
                lean_ctor_set(v___x_4064_, 2, v___x_4063_);
                lean_inc(v___y_4061_);
                v___x_4065_ =
                    l_Lean_Syntax_node2(v___y_4055_, v___y_4061_, v___y_4053_, v___x_4064_);
                v___x_4066_ =
                    l_Lean_Syntax_node2(v___y_4055_, v___y_4050_, v___y_4058_, v___x_4065_);
                v___x_4067_ = l_Lean_Syntax_node1(v___y_4055_, v___y_4054_, v___x_4066_);
                v___x_4068_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__34;
                v___x_4069_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4069_, 0, v___y_4055_);
                lean_ctor_set(v___x_4069_, 1, v___x_4068_);
                v___x_4070_ = l_Lean_Syntax_node1(v___y_4055_, v___y_4054_, v___y_4059_);
                lean_inc(v___y_4051_);
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
                v___x_4073_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4073_, 0, v___x_4072_);
                lean_ctor_set(v___x_4073_, 1, v___y_4057_);
                return v___x_4073_;
            }
            2 => {
                lean_inc_ref(v___y_4081_);
                v___x_4089_ = l_Array_append___redArg(v___y_4081_, v___y_4088_);
                lean_dec_ref(v___y_4088_);
                lean_inc_n(v___y_4079_, 4);
                lean_inc_n(v___y_4082_, 7);
                v___x_4090_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_4090_, 0, v___y_4082_);
                lean_ctor_set(v___x_4090_, 1, v___y_4079_);
                lean_ctor_set(v___x_4090_, 2, v___x_4089_);
                lean_inc(v___y_4080_);
                v___x_4091_ =
                    l_Lean_Syntax_node2(v___y_4082_, v___y_4080_, v___y_4086_, v___x_4090_);
                v___x_4092_ =
                    l_Lean_Syntax_node2(v___y_4082_, v___y_4087_, v___y_4085_, v___x_4091_);
                v___x_4093_ = l_Lean_Syntax_node1(v___y_4082_, v___y_4079_, v___x_4092_);
                v___x_4094_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__34;
                v___x_4095_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4095_, 0, v___y_4082_);
                lean_ctor_set(v___x_4095_, 1, v___x_4094_);
                v___x_4096_ = l_Lean_Syntax_node1(v___y_4082_, v___y_4079_, v___y_4075_);
                lean_inc(v___y_4076_);
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
                v___x_4099_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4099_, 0, v___x_4098_);
                lean_ctor_set(v___x_4099_, 1, v___y_4083_);
                return v___x_4099_;
            }
            3 => {
                lean_inc_ref(v___y_4110_);
                v___x_4118_ = l_Array_append___redArg(v___y_4110_, v___y_4117_);
                lean_dec_ref(v___y_4117_);
                lean_inc_n(v___y_4104_, 5);
                lean_inc_n(v___y_4113_, 12);
                v___x_4119_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_4119_, 0, v___y_4113_);
                lean_ctor_set(v___x_4119_, 1, v___y_4104_);
                lean_ctor_set(v___x_4119_, 2, v___x_4118_);
                lean_inc_ref(v___x_4119_);
                lean_inc(v___y_4103_);
                v___x_4120_ =
                    l_Lean_Syntax_node2(v___y_4113_, v___y_4103_, v___y_4115_, v___x_4119_);
                lean_inc(v___y_4116_);
                lean_inc(v___y_4105_);
                v___x_4121_ =
                    l_Lean_Syntax_node2(v___y_4113_, v___y_4105_, v___y_4116_, v___x_4120_);
                v___x_4122_ = l_Lean_Syntax_node1(v___y_4113_, v___y_4104_, v___x_4121_);
                v___x_4123_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__34;
                v___x_4124_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4124_, 0, v___y_4113_);
                lean_ctor_set(v___x_4124_, 1, v___x_4123_);
                v___x_4125_ = l_Lean_Syntax_node1(v___y_4113_, v___y_4104_, v___y_4107_);
                lean_inc(v___x_4125_);
                lean_inc_ref(v___x_4124_);
                lean_inc(v___y_4106_);
                lean_inc(v___y_4109_);
                lean_inc_n(v___y_4111_, 2);
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
                lean_inc_ref(v___y_4108_);
                v___x_4128_ =
                    l_Lean_Name_mkStr4(v___x_4100_, v___x_4101_, v___y_4108_, v___x_4127_);
                v___x_4129_ = l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__2;
                v___x_4130_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4130_, 0, v___y_4113_);
                lean_ctor_set(v___x_4130_, 1, v___x_4129_);
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
                v___x_4136_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4136_, 0, v___x_4135_);
                lean_ctor_set(v___x_4136_, 1, v___y_4114_);
                return v___x_4136_;
            }
            4 => {
                lean_inc_ref(v___y_4152_);
                v___x_4155_ = l_Array_append___redArg(v___y_4152_, v___y_4154_);
                lean_dec_ref(v___y_4154_);
                lean_inc(v___y_4145_);
                lean_inc_n(v___y_4146_, 9);
                v___x_4156_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_4156_, 0, v___y_4146_);
                lean_ctor_set(v___x_4156_, 1, v___y_4145_);
                lean_ctor_set(v___x_4156_, 2, v___x_4155_);
                v___x_4157_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0;
                v___x_4158_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4158_, 0, v___y_4146_);
                lean_ctor_set(v___x_4158_, 1, v___x_4157_);
                v___x_4159_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__1;
                v___x_4160_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4160_, 0, v___y_4146_);
                lean_ctor_set(v___x_4160_, 1, v___x_4159_);
                v___x_4161_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__47;
                v___x_4162_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4162_, 0, v___y_4146_);
                lean_ctor_set(v___x_4162_, 1, v___x_4161_);
                v___x_4163_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__10;
                v___x_4164_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4164_, 0, v___y_4146_);
                lean_ctor_set(v___x_4164_, 1, v___x_4163_);
                lean_inc(v___y_4150_);
                lean_inc(v___y_4144_);
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
                v___x_4168_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4168_, 0, v___y_4146_);
                lean_ctor_set(v___x_4168_, 1, v___x_4166_);
                v___x_4169_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__24;
                v___x_4170_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4170_, 0, v___y_4146_);
                lean_ctor_set(v___x_4170_, 1, v___x_4169_);
                v___x_4171_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__2;
                lean_inc_ref(v___y_4143_);
                v___x_4172_ =
                    l_Lean_Name_mkStr4(v___x_4100_, v___x_4101_, v___y_4143_, v___x_4171_);
                v___x_4173_ = l_Lean_Parser_Attr_simprocAttr___closed__0;
                v___x_4174_ = l_Lean_Parser_Attr_simprocBuiltinAttr___closed__1;
                v___x_4175_ = l_Lean_Parser_Attr_simprocBuiltinAttr___closed__2;
                v___x_4176_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4176_, 0, v___y_4146_);
                lean_ctor_set(v___x_4176_, 1, v___x_4175_);
                if lean_obj_tag(v___y_4147_) == 1 {
                    v_val_4177_ = lean_ctor_get(v___y_4147_, 0);
                    lean_inc(v_val_4177_);
                    lean_dec_ref_known(v___y_4147_, 1);
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
                    lean_dec(v___y_4147_);
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
                lean_inc_ref(v___y_4187_);
                v___x_4193_ = l_Array_append___redArg(v___y_4187_, v___y_4192_);
                lean_dec_ref(v___y_4192_);
                lean_inc(v___y_4191_);
                lean_inc_n(v___y_4182_, 9);
                v___x_4194_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_4194_, 0, v___y_4182_);
                lean_ctor_set(v___x_4194_, 1, v___y_4191_);
                lean_ctor_set(v___x_4194_, 2, v___x_4193_);
                v___x_4195_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0;
                v___x_4196_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4196_, 0, v___y_4182_);
                lean_ctor_set(v___x_4196_, 1, v___x_4195_);
                v___x_4197_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__1;
                v___x_4198_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4198_, 0, v___y_4182_);
                lean_ctor_set(v___x_4198_, 1, v___x_4197_);
                v___x_4199_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__47;
                v___x_4200_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4200_, 0, v___y_4182_);
                lean_ctor_set(v___x_4200_, 1, v___x_4199_);
                v___x_4201_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__10;
                v___x_4202_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4202_, 0, v___y_4182_);
                lean_ctor_set(v___x_4202_, 1, v___x_4201_);
                lean_inc(v___y_4190_);
                lean_inc(v___y_4184_);
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
                v___x_4206_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4206_, 0, v___y_4182_);
                lean_ctor_set(v___x_4206_, 1, v___x_4204_);
                v___x_4207_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__24;
                v___x_4208_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4208_, 0, v___y_4182_);
                lean_ctor_set(v___x_4208_, 1, v___x_4207_);
                v___x_4209_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__2;
                lean_inc_ref(v___y_4181_);
                v___x_4210_ =
                    l_Lean_Name_mkStr4(v___x_4100_, v___x_4101_, v___y_4181_, v___x_4209_);
                v___x_4211_ = l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__1;
                v___x_4212_ = l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__2;
                v___x_4213_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4213_, 0, v___y_4182_);
                lean_ctor_set(v___x_4213_, 1, v___x_4212_);
                if lean_obj_tag(v___y_4183_) == 1 {
                    v_val_4214_ = lean_ctor_get(v___y_4183_, 0);
                    lean_inc(v_val_4214_);
                    lean_dec_ref_known(v___y_4183_, 1);
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
                    lean_dec(v___y_4183_);
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
                lean_inc_ref(v___y_4219_);
                v___x_4230_ = l_Array_append___redArg(v___y_4219_, v___y_4229_);
                lean_dec_ref(v___y_4229_);
                lean_inc(v___y_4227_);
                lean_inc_n(v___y_4221_, 9);
                v___x_4231_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_4231_, 0, v___y_4221_);
                lean_ctor_set(v___x_4231_, 1, v___y_4227_);
                lean_ctor_set(v___x_4231_, 2, v___x_4230_);
                v___x_4232_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0;
                v___x_4233_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4233_, 0, v___y_4221_);
                lean_ctor_set(v___x_4233_, 1, v___x_4232_);
                v___x_4234_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__1;
                v___x_4235_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4235_, 0, v___y_4221_);
                lean_ctor_set(v___x_4235_, 1, v___x_4234_);
                v___x_4236_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__47;
                v___x_4237_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4237_, 0, v___y_4221_);
                lean_ctor_set(v___x_4237_, 1, v___x_4236_);
                v___x_4238_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__10;
                v___x_4239_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4239_, 0, v___y_4221_);
                lean_ctor_set(v___x_4239_, 1, v___x_4238_);
                lean_inc(v___y_4220_);
                lean_inc(v___y_4228_);
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
                v___x_4243_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4243_, 0, v___y_4221_);
                lean_ctor_set(v___x_4243_, 1, v___x_4241_);
                v___x_4244_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__24;
                v___x_4245_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4245_, 0, v___y_4221_);
                lean_ctor_set(v___x_4245_, 1, v___x_4244_);
                v___x_4246_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__2;
                lean_inc_ref(v___y_4218_);
                v___x_4247_ =
                    l_Lean_Name_mkStr4(v___x_4100_, v___x_4101_, v___y_4218_, v___x_4246_);
                v___x_4248_ = l_Lean_Parser_Attr_simprocBuiltinAttr___closed__1;
                v___x_4249_ = l_Lean_Parser_Attr_simprocBuiltinAttr___closed__2;
                v___x_4250_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4250_, 0, v___y_4221_);
                lean_ctor_set(v___x_4250_, 1, v___x_4249_);
                if lean_obj_tag(v___y_4222_) == 1 {
                    v_val_4251_ = lean_ctor_get(v___y_4222_, 0);
                    lean_inc(v_val_4251_);
                    lean_dec_ref_known(v___y_4222_, 1);
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
                    lean_dec(v___y_4222_);
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
                v___x_4264_ = lean_unsigned_to_nat(4);
                v___x_4265_ = l_Lean_Syntax_getArg(v_x_4045_, v___x_4264_);
                lean_inc(v___x_4265_);
                v___x_4266_ = l_Lean_Syntax_matchesNull(v___x_4265_, v___x_4141_);
                if v___x_4266_ == 0 {
                    lean_inc(v___x_4265_);
                    v___x_4267_ = l_Lean_Syntax_matchesNull(v___x_4265_, v___y_4260_);
                    if v___x_4267_ == 0 {
                        lean_dec(v___x_4265_);
                        lean_dec(v_pre_x3f_4261_);
                        lean_dec(v___y_4259_);
                        lean_dec(v___y_4257_);
                        lean_dec(v_x_4045_);
                        v___x_4268_ = lean_box(1);
                        v___x_4269_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_4269_, 0, v___x_4268_);
                        lean_ctor_set(v___x_4269_, 1, v___y_4263_);
                        return v___x_4269_;
                    } else {
                        v___x_4270_ = l_Lean_Syntax_getArg(v___x_4265_, v___y_4256_);
                        lean_dec(v___x_4265_);
                        lean_inc(v___x_4270_);
                        v___x_4271_ = l_Lean_Syntax_matchesNull(v___x_4270_, v___y_4256_);
                        if v___x_4271_ == 0 {
                            lean_inc(v___x_4270_);
                            v___x_4272_ = l_Lean_Syntax_matchesNull(v___x_4270_, v___y_4260_);
                            if v___x_4272_ == 0 {
                                lean_dec(v___x_4270_);
                                lean_dec(v_pre_x3f_4261_);
                                lean_dec(v___y_4259_);
                                lean_dec(v___y_4257_);
                                lean_dec(v_x_4045_);
                                v___x_4273_ = lean_box(1);
                                v___x_4274_ = lean_alloc_ctor(1, 2, (0) as u32);
                                lean_ctor_set(v___x_4274_, 0, v___x_4273_);
                                lean_ctor_set(v___x_4274_, 1, v___y_4263_);
                                return v___x_4274_;
                            } else {
                                v___x_4275_ = l_Lean_Syntax_getArg(v___x_4270_, v___x_4141_);
                                v___x_4276_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__5;
                                v___x_4277_ = l_Lean_Syntax_matchesIdent(v___x_4275_, v___x_4276_);
                                lean_dec(v___x_4275_);
                                if v___x_4277_ == 0 {
                                    lean_dec(v___x_4270_);
                                    lean_dec(v_pre_x3f_4261_);
                                    lean_dec(v___y_4259_);
                                    lean_dec(v___y_4257_);
                                    lean_dec(v_x_4045_);
                                    v___x_4278_ = lean_box(1);
                                    v___x_4279_ = lean_alloc_ctor(1, 2, (0) as u32);
                                    lean_ctor_set(v___x_4279_, 0, v___x_4278_);
                                    lean_ctor_set(v___x_4279_, 1, v___y_4263_);
                                    return v___x_4279_;
                                } else {
                                    v___x_4280_ = l_Lean_Syntax_getArg(v___x_4270_, v___y_4258_);
                                    lean_dec(v___x_4270_);
                                    v___x_4281_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__7;
                                    v___x_4282_ =
                                        l_Lean_Syntax_matchesIdent(v___x_4280_, v___x_4281_);
                                    lean_dec(v___x_4280_);
                                    if v___x_4282_ == 0 {
                                        lean_dec(v_pre_x3f_4261_);
                                        lean_dec(v___y_4259_);
                                        lean_dec(v___y_4257_);
                                        lean_dec(v_x_4045_);
                                        v___x_4283_ = lean_box(1);
                                        v___x_4284_ = lean_alloc_ctor(1, 2, (0) as u32);
                                        lean_ctor_set(v___x_4284_, 0, v___x_4283_);
                                        lean_ctor_set(v___x_4284_, 1, v___y_4263_);
                                        return v___x_4284_;
                                    } else {
                                        v___x_4285_ = lean_unsigned_to_nat(5);
                                        v___x_4286_ = l_Lean_Syntax_getArg(v_x_4045_, v___x_4285_);
                                        v___x_4287_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__27;
                                        lean_inc(v___x_4286_);
                                        v___x_4288_ =
                                            l_Lean_Syntax_isOfKind(v___x_4286_, v___x_4287_);
                                        if v___x_4288_ == 0 {
                                            lean_dec(v___x_4286_);
                                            lean_dec(v_pre_x3f_4261_);
                                            lean_dec(v___y_4259_);
                                            lean_dec(v___y_4257_);
                                            lean_dec(v_x_4045_);
                                            v___x_4289_ = lean_box(1);
                                            v___x_4290_ = lean_alloc_ctor(1, 2, (0) as u32);
                                            lean_ctor_set(v___x_4290_, 0, v___x_4289_);
                                            lean_ctor_set(v___x_4290_, 1, v___y_4263_);
                                            return v___x_4290_;
                                        } else {
                                            v_ref_4291_ = lean_ctor_get(v___y_4262_, 5);
                                            v___x_4292_ = lean_unsigned_to_nat(7);
                                            v___x_4293_ =
                                                l_Lean_Syntax_getArg(v_x_4045_, v___x_4292_);
                                            v___x_4294_ = lean_unsigned_to_nat(10);
                                            v___x_4295_ =
                                                l_Lean_Syntax_getArg(v_x_4045_, v___x_4294_);
                                            lean_dec(v_x_4045_);
                                            v___x_4296_ =
                                                l_Lean_SourceInfo_fromRef(v_ref_4291_, v___x_4271_);
                                            v___x_4297_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__21;
                                            v___x_4298_ = l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__1;
                                            v___x_4299_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27), core::ptr::addr_of_mut!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27_once), _init_l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27);
                                            if lean_obj_tag(v___y_4259_) == 1 {
                                                v_val_4300_ = lean_ctor_get(v___y_4259_, 0);
                                                lean_inc(v_val_4300_);
                                                lean_dec_ref_known(v___y_4259_, 1);
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
                                                lean_dec(v___y_4259_);
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
                            lean_dec(v___x_4270_);
                            v___x_4304_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__7;
                            v___x_4305_ = l_Lean_Syntax_matchesIdent(v___x_4303_, v___x_4304_);
                            lean_dec(v___x_4303_);
                            if v___x_4305_ == 0 {
                                lean_dec(v_pre_x3f_4261_);
                                lean_dec(v___y_4259_);
                                lean_dec(v___y_4257_);
                                lean_dec(v_x_4045_);
                                v___x_4306_ = lean_box(1);
                                v___x_4307_ = lean_alloc_ctor(1, 2, (0) as u32);
                                lean_ctor_set(v___x_4307_, 0, v___x_4306_);
                                lean_ctor_set(v___x_4307_, 1, v___y_4263_);
                                return v___x_4307_;
                            } else {
                                v___x_4308_ = lean_unsigned_to_nat(5);
                                v___x_4309_ = l_Lean_Syntax_getArg(v_x_4045_, v___x_4308_);
                                v___x_4310_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__27;
                                lean_inc(v___x_4309_);
                                v___x_4311_ = l_Lean_Syntax_isOfKind(v___x_4309_, v___x_4310_);
                                if v___x_4311_ == 0 {
                                    lean_dec(v___x_4309_);
                                    lean_dec(v_pre_x3f_4261_);
                                    lean_dec(v___y_4259_);
                                    lean_dec(v___y_4257_);
                                    lean_dec(v_x_4045_);
                                    v___x_4312_ = lean_box(1);
                                    v___x_4313_ = lean_alloc_ctor(1, 2, (0) as u32);
                                    lean_ctor_set(v___x_4313_, 0, v___x_4312_);
                                    lean_ctor_set(v___x_4313_, 1, v___y_4263_);
                                    return v___x_4313_;
                                } else {
                                    v_ref_4314_ = lean_ctor_get(v___y_4262_, 5);
                                    v___x_4315_ = lean_unsigned_to_nat(7);
                                    v___x_4316_ = l_Lean_Syntax_getArg(v_x_4045_, v___x_4315_);
                                    v___x_4317_ = lean_unsigned_to_nat(10);
                                    v___x_4318_ = l_Lean_Syntax_getArg(v_x_4045_, v___x_4317_);
                                    lean_dec(v_x_4045_);
                                    v___x_4319_ =
                                        l_Lean_SourceInfo_fromRef(v_ref_4314_, v___x_4266_);
                                    v___x_4320_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__21;
                                    v___x_4321_ = l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__1;
                                    v___x_4322_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27), core::ptr::addr_of_mut!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27_once), _init_l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27);
                                    if lean_obj_tag(v___y_4259_) == 1 {
                                        v_val_4323_ = lean_ctor_get(v___y_4259_, 0);
                                        lean_inc(v_val_4323_);
                                        lean_dec_ref_known(v___y_4259_, 1);
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
                                        lean_dec(v___y_4259_);
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
                    lean_dec(v___x_4265_);
                    v___x_4326_ = lean_unsigned_to_nat(5);
                    v___x_4327_ = l_Lean_Syntax_getArg(v_x_4045_, v___x_4326_);
                    v___x_4328_ = l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__27;
                    lean_inc(v___x_4327_);
                    v___x_4329_ = l_Lean_Syntax_isOfKind(v___x_4327_, v___x_4328_);
                    if v___x_4329_ == 0 {
                        lean_dec(v___x_4327_);
                        lean_dec(v_pre_x3f_4261_);
                        lean_dec(v___y_4259_);
                        lean_dec(v___y_4257_);
                        lean_dec(v_x_4045_);
                        v___x_4330_ = lean_box(1);
                        v___x_4331_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_4331_, 0, v___x_4330_);
                        lean_ctor_set(v___x_4331_, 1, v___y_4263_);
                        return v___x_4331_;
                    } else {
                        v_ref_4332_ = lean_ctor_get(v___y_4262_, 5);
                        v___x_4333_ = lean_unsigned_to_nat(7);
                        v___x_4334_ = l_Lean_Syntax_getArg(v_x_4045_, v___x_4333_);
                        v___x_4335_ = lean_unsigned_to_nat(10);
                        v___x_4336_ = l_Lean_Syntax_getArg(v_x_4045_, v___x_4335_);
                        lean_dec(v_x_4045_);
                        v___x_4337_ = 0;
                        v___x_4338_ = l_Lean_SourceInfo_fromRef(v_ref_4332_, v___x_4337_);
                        v___x_4339_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__21;
                        v___x_4340_ = l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__1;
                        v___x_4341_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27), core::ptr::addr_of_mut!(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27_once), _init_l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27);
                        if lean_obj_tag(v___y_4259_) == 1 {
                            v_val_4342_ = lean_ctor_get(v___y_4259_, 0);
                            lean_inc(v_val_4342_);
                            lean_dec_ref_known(v___y_4259_, 1);
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
                            lean_dec(v___y_4259_);
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
                v___x_4349_ = lean_unsigned_to_nat(1);
                v___x_4350_ = l_Lean_Syntax_getArg(v_x_4045_, v___x_4349_);
                v___x_4351_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__5;
                v___x_4352_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__2;
                lean_inc(v___x_4350_);
                v___x_4353_ = l_Lean_Syntax_isOfKind(v___x_4350_, v___x_4352_);
                if v___x_4353_ == 0 {
                    lean_dec(v___x_4350_);
                    lean_dec(v_doc_x3f_4346_);
                    lean_dec(v_x_4045_);
                    v___x_4354_ = lean_box(1);
                    v___x_4355_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_4355_, 0, v___x_4354_);
                    lean_ctor_set(v___x_4355_, 1, v___y_4348_);
                    return v___x_4355_;
                } else {
                    v___x_4356_ = lean_unsigned_to_nat(2);
                    v___x_4357_ = lean_unsigned_to_nat(3);
                    v___x_4358_ = l_Lean_Syntax_getArg(v_x_4045_, v___x_4357_);
                    v___x_4359_ = l_Lean_Syntax_isNone(v___x_4358_);
                    if v___x_4359_ == 0 {
                        lean_inc(v___x_4358_);
                        v___x_4360_ = l_Lean_Syntax_matchesNull(v___x_4358_, v___x_4349_);
                        if v___x_4360_ == 0 {
                            lean_dec(v___x_4358_);
                            lean_dec(v___x_4350_);
                            lean_dec(v_doc_x3f_4346_);
                            lean_dec(v_x_4045_);
                            v___x_4361_ = lean_box(1);
                            v___x_4362_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v___x_4362_, 0, v___x_4361_);
                            lean_ctor_set(v___x_4362_, 1, v___y_4348_);
                            return v___x_4362_;
                        } else {
                            v_pre_x3f_4363_ = l_Lean_Syntax_getArg(v___x_4358_, v___x_4141_);
                            lean_dec(v___x_4358_);
                            v___x_4364_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_4364_, 0, v_pre_x3f_4363_);
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
                        lean_dec(v___x_4358_);
                        v___x_4365_ = lean_box(0);
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
    mut v_x_4379_: *mut LeanObject,
    mut v_a_4380_: *mut LeanObject,
    mut v_a_4381_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4382_: *mut LeanObject = core::ptr::null_mut();
    v_res_4382_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d____1(v_x_4379_, v_a_4380_, v_a_4381_);
    lean_dec_ref(v_a_4380_);
    return v_res_4382_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Simproc(builtin: u8) -> *mut LeanObject {
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
pub unsafe fn meta_initialize_Init_Simproc(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Init_Data_ToString_Name(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d__ =
        _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d__();
    lean_mark_persistent(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d__);
    l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d__ =
        _init_l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d__();
    lean_mark_persistent(l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d__);
    l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d__ =
        _init_l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d__();
    lean_mark_persistent(
        l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d__,
    );
    l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d__ =
        _init_l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d__();
    lean_mark_persistent(
        l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d__,
    );
    l_Lean_Parser_Attr_simprocAttr = _init_l_Lean_Parser_Attr_simprocAttr();
    lean_mark_persistent(l_Lean_Parser_Attr_simprocAttr);
    l_Lean_Parser_Attr_sevalprocAttr = _init_l_Lean_Parser_Attr_sevalprocAttr();
    lean_mark_persistent(l_Lean_Parser_Attr_sevalprocAttr);
    l_Lean_Parser_Attr_simprocBuiltinAttr = _init_l_Lean_Parser_Attr_simprocBuiltinAttr();
    lean_mark_persistent(l_Lean_Parser_Attr_simprocBuiltinAttr);
    l_Lean_Parser_Attr_sevalprocBuiltinAttr = _init_l_Lean_Parser_Attr_sevalprocBuiltinAttr();
    lean_mark_persistent(l_Lean_Parser_Attr_sevalprocBuiltinAttr);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Simproc(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_ToString_Name(builtin);
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
    res = runtime_initialize_Init_Simproc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Simproc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Simproc(builtin);
}
