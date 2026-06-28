// Lean compiler output
// Module: Init.TacticsExtra
// Imports: Init.Meta Init.Tactics Init.Data.Array.Basic
use crate::r#gen::Init::Data::Array::Basic::{
    initialize_Init_Data_Array_Basic, l_Array_append___redArg,
    runtime_initialize_Init_Data_Array_Basic,
};
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Meta::Defs::{
    l_Lean_Syntax_TSepArray_getElems___redArg, l_Lean_Syntax_isNone, l_Lean_Syntax_mkNumLit,
    l_Lean_Syntax_toNat, l_Lean_mkSepArray,
};
use crate::r#gen::Init::Meta::{initialize_Init_Meta, runtime_initialize_Init_Meta};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Array_mkArray1___redArg, l_Array_mkArray2___redArg, l_Lean_Name_mkStr1,
    l_Lean_Name_mkStr2, l_Lean_Name_mkStr3, l_Lean_Name_mkStr4, l_Lean_SourceInfo_fromRef,
    l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs, l_Lean_Syntax_isMissing, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_matchesNull, l_Lean_Syntax_node1, l_Lean_Syntax_node2, l_Lean_Syntax_node3,
    l_Lean_Syntax_node4, l_Lean_Syntax_node5, l_Lean_Syntax_node8, l_Lean_addMacroScope,
    l_Lean_replaceRef, l_String_toRawSubstring_x27,
};
use crate::r#gen::Init::Tactics::{
    initialize_Init_Tactics, l_Lean_Parser_Tactic_location, l_Lean_Parser_Tactic_optConfig,
    l_Lean_Parser_Tactic_rwRuleSeq, runtime_initialize_Init_Tactics,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_dec_lt};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_sub,
};
pub static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__2_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__3_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [115, 121, 110, 116, 104, 101, 116, 105, 99, 72, 111, 108, 101, 0]};
static mut l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__3_value) as *mut crate::leanh::LeanObject;
static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__4_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__3_value) as *mut crate::leanh::LeanObject,11921244625177918938 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__5_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 111, 108, 101, 0]};
static mut l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__5_value) as *mut crate::leanh::LeanObject;
static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__6_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__6_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__6_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__6_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__6_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__5_value) as *mut crate::leanh::LeanObject,3984140175429830279 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__7_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__8_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0]};
static mut l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__8_value) as *mut crate::leanh::LeanObject;
static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__9_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__9_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__9_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__9_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__9_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__7_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__9_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__9_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__8_value) as *mut crate::leanh::LeanObject,8504843326314613972 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__10_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0]};
static mut l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__10_value) as *mut crate::leanh::LeanObject;
static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__11_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__11_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__11_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__11_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__11_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__7_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__11_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__11_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__10_value) as *mut crate::leanh::LeanObject,17228437386856258271 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__12_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__13_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__12_value) as *mut crate::leanh::LeanObject,9855511589286918680 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__14_value: crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [119, 105, 116, 104, 65, 110, 110, 111, 116, 97, 116, 101, 83, 116, 97, 116, 101, 0]};
static mut l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__14_value) as *mut crate::leanh::LeanObject;
static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__15_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__15_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__15_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__15_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__15_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__7_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__15_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__15_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__14_value) as *mut crate::leanh::LeanObject,10829944387272139803 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__16_value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [119, 105, 116, 104, 95, 97, 110, 110, 111, 116, 97, 116, 101, 95, 115, 116, 97, 116, 101, 0]};
static mut l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__16_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__17_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 107, 105, 112, 0]};
static mut l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__17_value) as *mut crate::leanh::LeanObject;
static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__18_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__18_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__18_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__18_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__18_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__7_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__18_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__18_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__17_value) as *mut crate::leanh::LeanObject,7630385922513644276 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__18_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__19_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__19: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__20_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [112, 97, 114, 101, 110, 0]};
static mut l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__20: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__20_value) as *mut crate::leanh::LeanObject;
static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__21_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__21_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__21_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__21_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__21_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__7_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__21_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__21_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__20_value) as *mut crate::leanh::LeanObject,8689124066155232629 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__21: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__21_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__22_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__22: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__22_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__23_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__23: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__23_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__24_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [99, 97, 115, 101, 0]};
static mut l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__24: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__24_value) as *mut crate::leanh::LeanObject;
static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__25_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__25_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__25_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__25_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__25_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__7_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__25_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__25_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__24_value) as *mut crate::leanh::LeanObject,3714280620155270360 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__25: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__25_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__26_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [99, 97, 115, 101, 65, 114, 103, 0]};
static mut l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__26: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__26_value) as *mut crate::leanh::LeanObject;
static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__27_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__27_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__27_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__27_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__27_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__7_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__27_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__27_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__26_value) as *mut crate::leanh::LeanObject,14546932361418667927 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__27: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__27_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__28_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [98, 105, 110, 100, 101, 114, 73, 100, 101, 110, 116, 0]};
static mut l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__28: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__28_value) as *mut crate::leanh::LeanObject;
static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__29_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__29_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__29_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__28_value) as *mut crate::leanh::LeanObject,13771926289831477797 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__29: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__29_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__30_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [61, 62, 0]};
static mut l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__30: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__30_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__31_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [115, 111, 114, 114, 121, 0]};
static mut l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__31: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__31_value) as *mut crate::leanh::LeanObject;
static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__32_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__32_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__32_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__32_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__32_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__32_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__32_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__31_value) as *mut crate::leanh::LeanObject,4292506374233281930 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__32: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__32_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__33_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__33: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__33_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__3___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [63, 0]};
static mut l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__3___closed__1_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [112, 111, 115, 0]};
static mut l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__3___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__3___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__3___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__3___closed__1_value) as *mut crate::leanh::LeanObject,6391873163851744175 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__3___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__4___closed__0_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [110, 101, 103, 0]};
static mut l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__4___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__4___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__4___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__4___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__4___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__4___closed__0_value) as *mut crate::leanh::LeanObject,7212229036697944544 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__4___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__4___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__1___boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__2___boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__2_value: crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2) as u16, other: 0, tag: 245 }, m_fun: l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__3___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 2, m_objs: [core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__0_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__3_value: crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2) as u16, other: 0, tag: 245 }, m_fun: l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__4___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 2, m_objs: [core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__0_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__4_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [111, 112, 101, 110, 0]};
static mut l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__4_value
) as *mut crate::leanh::LeanObject;
static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__5_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__5_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__5_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__5_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__7_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__5_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__4_value) as *mut crate::leanh::LeanObject,1617625281282625860 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__6_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [67, 111, 109, 109, 97, 110, 100, 0]};
static mut l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__6_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__7_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [111, 112, 101, 110, 83, 105, 109, 112, 108, 101, 0]};
static mut l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__7_value
) as *mut crate::leanh::LeanObject;
static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__8_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__8_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__8_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__8_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__8_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__6_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__8_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__7_value) as *mut crate::leanh::LeanObject,4840083868155834027 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__8_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__9_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [67, 108, 97, 115, 115, 105, 99, 97, 108, 0]};
static mut l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__9_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__10_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__11_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__9_value) as *mut crate::leanh::LeanObject,10854111772627758120 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__11_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__12_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__11_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__12_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__13_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__12_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__13_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__14_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [105, 110, 0]};
static mut l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__14:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__14_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__15_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [114, 101, 102, 105, 110, 101, 0]};
static mut l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__15_value
) as *mut crate::leanh::LeanObject;
static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__16_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__16_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__16_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__16_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__16_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__7_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__16_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__16_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__15_value) as *mut crate::leanh::LeanObject,17704266427038597681 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__16:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__16_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__17_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [59, 0]};
static mut l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__17:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__17_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__18_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__18:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__18_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__19_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 1 }, m_objs: [((( 2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__13_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__18_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__19:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__19_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__0_value: crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [116, 101, 114, 109, 68, 101, 112, 73, 102, 84, 104, 101, 110, 69, 108, 115, 101, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,12532511233276993215 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__2_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [105, 102, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__3_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [58, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__4_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 104, 101, 110, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__5_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [101, 108, 115, 101, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___closed__0_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [116, 97, 99, 68, 101, 112, 73, 102, 84, 104, 101, 110, 69, 108, 115, 101, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__7_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___closed__0_value) as *mut crate::leanh::LeanObject,2027926140108456694 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___lam__0___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [104, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___lam__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___lam__0___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,8738205681931236784 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___lam__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___closed__0_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [116, 97, 99, 73, 102, 84, 104, 101, 110, 69, 108, 115, 101, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__7_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___closed__0_value) as *mut crate::leanh::LeanObject,14874919684502089306 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_tacticIterate_________00__closed__0_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 18,
    m_capacity: 18,
    m_length: 17,
    m_data: [
        116, 97, 99, 116, 105, 99, 73, 116, 101, 114, 97, 116, 101, 95, 95, 95, 95, 0,
    ],
};
static mut l_Lean_Parser_Tactic_tacticIterate_________00__closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticIterate_________00__closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_tacticIterate_________00__closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Tactic_tacticIterate_________00__closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticIterate_________00__closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Tactic_tacticIterate_________00__closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticIterate_________00__closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__7_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Parser_Tactic_tacticIterate_________00__closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticIterate_________00__closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticIterate_________00__closed__0_value)
            as *mut crate::leanh::LeanObject,
        10202523486328991725 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_tacticIterate_________00__closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticIterate_________00__closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_tacticIterate_________00__closed__2_value:
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
static mut l_Lean_Parser_Tactic_tacticIterate_________00__closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticIterate_________00__closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_tacticIterate_________00__closed__3_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticIterate_________00__closed__2_value)
            as *mut crate::leanh::LeanObject,
        12571085391447129896 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_tacticIterate_________00__closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticIterate_________00__closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_tacticIterate_________00__closed__4_value:
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
    m_data: [105, 116, 101, 114, 97, 116, 101, 0],
};
static mut l_Lean_Parser_Tactic_tacticIterate_________00__closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticIterate_________00__closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_tacticIterate_________00__closed__5_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticIterate_________00__closed__4_value)
            as *mut crate::leanh::LeanObject,
        0 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_tacticIterate_________00__closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticIterate_________00__closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_tacticIterate_________00__closed__6_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [111, 112, 116, 105, 111, 110, 97, 108, 0],
};
static mut l_Lean_Parser_Tactic_tacticIterate_________00__closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticIterate_________00__closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_tacticIterate_________00__closed__7_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticIterate_________00__closed__6_value)
            as *mut crate::leanh::LeanObject,
        18170484695678750185 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_tacticIterate_________00__closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticIterate_________00__closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_tacticIterate_________00__closed__8_value:
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
    m_data: [112, 112, 83, 112, 97, 99, 101, 0],
};
static mut l_Lean_Parser_Tactic_tacticIterate_________00__closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticIterate_________00__closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_tacticIterate_________00__closed__9_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticIterate_________00__closed__8_value)
            as *mut crate::leanh::LeanObject,
        17761616517784022991 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_tacticIterate_________00__closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticIterate_________00__closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_tacticIterate_________00__closed__10_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticIterate_________00__closed__9_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_tacticIterate_________00__closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticIterate_________00__closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_tacticIterate_________00__closed__11_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [110, 117, 109, 0],
};
static mut l_Lean_Parser_Tactic_tacticIterate_________00__closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticIterate_________00__closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_tacticIterate_________00__closed__12_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticIterate_________00__closed__11_value)
            as *mut crate::leanh::LeanObject,
        6110315075117401315 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_tacticIterate_________00__closed__12:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticIterate_________00__closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_tacticIterate_________00__closed__13_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticIterate_________00__closed__12_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_tacticIterate_________00__closed__13:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticIterate_________00__closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_tacticIterate_________00__closed__14_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticIterate_________00__closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticIterate_________00__closed__10_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticIterate_________00__closed__13_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_tacticIterate_________00__closed__14:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticIterate_________00__closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_tacticIterate_________00__closed__15_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticIterate_________00__closed__7_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticIterate_________00__closed__14_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_tacticIterate_________00__closed__15:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticIterate_________00__closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_tacticIterate_________00__closed__16_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticIterate_________00__closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticIterate_________00__closed__5_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticIterate_________00__closed__15_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_tacticIterate_________00__closed__16:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticIterate_________00__closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_tacticIterate_________00__closed__17_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticIterate_________00__closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticIterate_________00__closed__16_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticIterate_________00__closed__10_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_tacticIterate_________00__closed__17:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticIterate_________00__closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_tacticIterate_________00__closed__18_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__8_value) as *mut crate::leanh::LeanObject,11103865283154438669 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Parser_Tactic_tacticIterate_________00__closed__18:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticIterate_________00__closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_tacticIterate_________00__closed__19_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticIterate_________00__closed__18_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_tacticIterate_________00__closed__19:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticIterate_________00__closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_tacticIterate_________00__closed__20_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticIterate_________00__closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticIterate_________00__closed__17_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticIterate_________00__closed__19_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_tacticIterate_________00__closed__20:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticIterate_________00__closed__20_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_tacticIterate_________00__closed__21_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticIterate_________00__closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1022 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticIterate_________00__closed__20_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_tacticIterate_________00__closed__21:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticIterate_________00__closed__21_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Tactic_tacticIterate________: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticIterate_________00__closed__21_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 101, 113, 49, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__7_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1___closed__0_value) as *mut crate::leanh::LeanObject,8471002125274025202 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1___closed__2_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [116, 97, 99, 116, 105, 99, 84, 114, 121, 95, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1___closed__2_value) as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__7_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1___closed__2_value) as *mut crate::leanh::LeanObject,10962186005905108258 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1___closed__4_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [116, 114, 121, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__0_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        116, 97, 99, 116, 105, 99, 82, 119, 95, 109, 111, 100, 95, 99, 97, 115, 116, 95, 95, 95, 0,
    ],
};
static mut l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__7_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__1_value:
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
        core::ptr::addr_of!(
            l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__1_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__0_value)
            as *mut crate::leanh::LeanObject,
        2560884927058161985 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__2_value:
    crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [114, 119, 95, 109, 111, 100, 95, 99, 97, 115, 116, 0],
};
static mut l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__3_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__2_value)
            as *mut crate::leanh::LeanObject,
        0 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__8_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__8:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_tacticRw__mod__cast______: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__0_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [111, 112, 116, 67, 111, 110, 102, 105, 103, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__7_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,3488656302031949961 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__2_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [114, 119, 82, 117, 108, 101, 83, 101, 113, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__2_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__7_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__2_value) as *mut crate::leanh::LeanObject,7234207980690920618 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__4_value: crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [116, 97, 99, 116, 105, 99, 78, 111, 114, 109, 95, 99, 97, 115, 116, 95, 95, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__4_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__5_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__5_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__5_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__5_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__7_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__5_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__4_value) as *mut crate::leanh::LeanObject,12540619166955942124 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__6_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [110, 111, 114, 109, 95, 99, 97, 115, 116, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__7_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [108, 111, 99, 97, 116, 105, 111, 110, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__7_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__8_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__8_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__8_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__8_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__8_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__7_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__8_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__7_value) as *mut crate::leanh::LeanObject,1767494567867404924 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__9_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [97, 116, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__10_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [108, 111, 99, 97, 116, 105, 111, 110, 87, 105, 108, 100, 99, 97, 114, 100, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__10_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__11_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__11_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__11_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__11_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__11_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__7_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__11_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__11_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__10_value) as *mut crate::leanh::LeanObject,1262264483427375750 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__12_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [42, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__13_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [114, 119, 83, 101, 113, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__13_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__14_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__14_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__14_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__14_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__14_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__7_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__14_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__14_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__13_value) as *mut crate::leanh::LeanObject,11075965128531316786 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__15_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [114, 119, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__16_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [91, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__16_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__17_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__17_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__0_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        116, 97, 99, 116, 105, 99, 69, 120, 97, 99, 116, 95, 109, 111, 100, 95, 99, 97, 115, 116,
        95, 0,
    ],
};
static mut l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__7_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__0_value)
            as *mut crate::leanh::LeanObject,
        11661875473047057264 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__2_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 16,
    m_capacity: 16,
    m_length: 15,
    m_data: [
        101, 120, 97, 99, 116, 95, 109, 111, 100, 95, 99, 97, 115, 116, 32, 0,
    ],
};
static mut l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__3_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__2_value)
            as *mut crate::leanh::LeanObject,
        0 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__4_value:
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
static mut l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__5_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__4_value)
            as *mut crate::leanh::LeanObject,
        8609355255726335675 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__6_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__5_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__7_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticIterate_________00__closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__6_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__8_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1022 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__7_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Tactic_tacticExact__mod__cast__: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [101, 120, 97, 99, 116, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__7_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__0_value) as *mut crate::leanh::LeanObject,14997215300048349804 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__2_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [109, 111, 100, 67, 97, 115, 116, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__2_value) as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__2_value) as *mut crate::leanh::LeanObject,9992539781328639569 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__4_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [109, 111, 100, 95, 99, 97, 115, 116, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__5_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [116, 121, 112, 101, 65, 115, 99, 114, 105, 112, 116, 105, 111, 110, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__5_value) as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__6_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__6_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__6_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__6_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__6_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__5_value) as *mut crate::leanh::LeanObject,5346268661279150583 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__7_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [104, 121, 103, 105, 101, 110, 105, 99, 76, 80, 97, 114, 101, 110, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__7_value) as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__8_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__8_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__8_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__8_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__8_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__8_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__7_value) as *mut crate::leanh::LeanObject,7306243862518720553 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__9_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__10_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__9_value) as *mut crate::leanh::LeanObject,9871775667037945883 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__11_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__11_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__12_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__12: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__13_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__13_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__13_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__13_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__13_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__7_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__14_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__13_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__15_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__14_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__16_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [95, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__16_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_tacticApply__mod__cast___00__closed__0_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        116, 97, 99, 116, 105, 99, 65, 112, 112, 108, 121, 95, 109, 111, 100, 95, 99, 97, 115, 116,
        95, 0,
    ],
};
static mut l_Lean_Parser_Tactic_tacticApply__mod__cast___00__closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticApply__mod__cast___00__closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_tacticApply__mod__cast___00__closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Tactic_tacticApply__mod__cast___00__closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticApply__mod__cast___00__closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Tactic_tacticApply__mod__cast___00__closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticApply__mod__cast___00__closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__7_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Parser_Tactic_tacticApply__mod__cast___00__closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticApply__mod__cast___00__closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticApply__mod__cast___00__closed__0_value)
            as *mut crate::leanh::LeanObject,
        9295407634137188843 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_tacticApply__mod__cast___00__closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticApply__mod__cast___00__closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_tacticApply__mod__cast___00__closed__2_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 16,
    m_capacity: 16,
    m_length: 15,
    m_data: [
        97, 112, 112, 108, 121, 95, 109, 111, 100, 95, 99, 97, 115, 116, 32, 0,
    ],
};
static mut l_Lean_Parser_Tactic_tacticApply__mod__cast___00__closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticApply__mod__cast___00__closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_tacticApply__mod__cast___00__closed__3_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticApply__mod__cast___00__closed__2_value)
            as *mut crate::leanh::LeanObject,
        0 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_tacticApply__mod__cast___00__closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticApply__mod__cast___00__closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_tacticApply__mod__cast___00__closed__4_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticIterate_________00__closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticApply__mod__cast___00__closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__6_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_tacticApply__mod__cast___00__closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticApply__mod__cast___00__closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_tacticApply__mod__cast___00__closed__5_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticApply__mod__cast___00__closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1022 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticApply__mod__cast___00__closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_tacticApply__mod__cast___00__closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticApply__mod__cast___00__closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Tactic_tacticApply__mod__cast__: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticApply__mod__cast___00__closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticApply__mod__cast____1___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [97, 112, 112, 108, 121, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticApply__mod__cast____1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticApply__mod__cast____1___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticApply__mod__cast____1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticApply__mod__cast____1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticApply__mod__cast____1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticApply__mod__cast____1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticApply__mod__cast____1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__7_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticApply__mod__cast____1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticApply__mod__cast____1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticApply__mod__cast____1___closed__0_value) as *mut crate::leanh::LeanObject,5826123769708379594 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticApply__mod__cast____1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticApply__mod__cast____1___closed__1_value) as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1340_ = l_Array_mkArray0(crate::leanh::lean_box(0));
    return v___x_1340_;
}
pub unsafe fn l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0(
    mut v_tk_1374_: *mut crate::leanh::LeanObject,
    mut v_holeOrTacticSeq_1375_: *mut crate::leanh::LeanObject,
    mut v_mkName_1376_: *mut crate::leanh::LeanObject,
    mut v___y_1377_: *mut crate::leanh::LeanObject,
    mut v___y_1378_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: u8 = 0;
    let mut v___x_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: u8 = 0;
    let mut v___x_1383_: u8 = 0;
    let mut v_macroScope_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceMsgs_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expandedMacroDecls_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1389_: u8 = 0;
    let mut v_methods_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1405_: u8 = 0;
    let mut v___x_1406_: u8 = 0;
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
    let mut v_ref_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1453_: u8 = 0;
    let mut v_a_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1458_: u8 = 0;
    let mut v___x_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1462_: u8 = 0;
    let mut v_reuseFailAlloc_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1464_: u8 = 0;
    let mut v_ref_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1479_: u8 = 0;
    let mut v___x_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1485_: u8 = 0;
    let mut v_a_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1490_: u8 = 0;
    let mut v___x_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1494_: u8 = 0;
    let mut v___x_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1379_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__4;
                crate::leanh::lean_inc(v_holeOrTacticSeq_1375_);
                v___x_1380_ = l_Lean_Syntax_isOfKind(v_holeOrTacticSeq_1375_, v___x_1379_);
                if v___x_1380_ == 0 {
                    v___x_1381_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__6;
                    crate::leanh::lean_inc(v_holeOrTacticSeq_1375_);
                    v___x_1382_ = l_Lean_Syntax_isOfKind(v_holeOrTacticSeq_1375_, v___x_1381_);
                    if v___x_1382_ == 0 {
                        v___x_1383_ = l_Lean_Syntax_isMissing(v_tk_1374_);
                        if v___x_1383_ == 0 {
                            v_macroScope_1384_ = crate::leanh::lean_ctor_get(v___y_1378_, 0);
                            v_traceMsgs_1385_ = crate::leanh::lean_ctor_get(v___y_1378_, 1);
                            v_expandedMacroDecls_1386_ =
                                crate::leanh::lean_ctor_get(v___y_1378_, 2);
                            v_isSharedCheck_1464_ =
                                (!crate::leanh::lean_is_exclusive(v___y_1378_)) as u8;
                            if v_isSharedCheck_1464_ == 0 {
                                v___x_1388_ = v___y_1378_;
                                v_isShared_1389_ = v_isSharedCheck_1464_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_expandedMacroDecls_1386_);
                                crate::leanh::lean_inc(v_traceMsgs_1385_);
                                crate::leanh::lean_inc(v_macroScope_1384_);
                                crate::leanh::lean_dec(v___y_1378_);
                                v___x_1388_ = crate::leanh::lean_box(0);
                                v_isShared_1389_ = v_isSharedCheck_1464_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_mkName_1376_);
                            crate::leanh::lean_dec(v_holeOrTacticSeq_1375_);
                            crate::leanh::lean_dec(v_tk_1374_);
                            v_ref_1465_ = crate::leanh::lean_ctor_get(v___y_1377_, 5);
                            v___x_1466_ = l_Lean_SourceInfo_fromRef(v_ref_1465_, v___x_1382_);
                            v___x_1467_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__31;
                            v___x_1468_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__32;
                            crate::leanh::lean_inc(v___x_1466_);
                            v___x_1469_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1469_, 0, v___x_1466_);
                            crate::leanh::lean_ctor_set(v___x_1469_, 1, v___x_1467_);
                            v___x_1470_ =
                                l_Lean_Syntax_node1(v___x_1466_, v___x_1468_, v___x_1469_);
                            v___x_1471_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__33;
                            v___x_1472_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1472_, 0, v___x_1470_);
                            crate::leanh::lean_ctor_set(v___x_1472_, 1, v___x_1471_);
                            v___x_1473_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1473_, 0, v___x_1472_);
                            crate::leanh::lean_ctor_set(v___x_1473_, 1, v___y_1378_);
                            return v___x_1473_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_holeOrTacticSeq_1375_);
                        crate::leanh::lean_dec(v_tk_1374_);
                        crate::leanh::lean_inc_ref(v___y_1377_);
                        v___x_1474_ =
                            crate::leanh::lean_apply_2(v_mkName_1376_, v___y_1377_, v___y_1378_);
                        if crate::leanh::lean_obj_tag(v___x_1474_) == 0 {
                            v_a_1475_ = crate::leanh::lean_ctor_get(v___x_1474_, 0);
                            v_a_1476_ = crate::leanh::lean_ctor_get(v___x_1474_, 1);
                            v_isSharedCheck_1485_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1474_)) as u8;
                            if v_isSharedCheck_1485_ == 0 {
                                v___x_1478_ = v___x_1474_;
                                v_isShared_1479_ = v_isSharedCheck_1485_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1476_);
                                crate::leanh::lean_inc(v_a_1475_);
                                crate::leanh::lean_dec(v___x_1474_);
                                v___x_1478_ = crate::leanh::lean_box(0);
                                v_isShared_1479_ = v_isSharedCheck_1485_;
                                state = 7;
                                continue;
                            }
                        } else {
                            v_a_1486_ = crate::leanh::lean_ctor_get(v___x_1474_, 0);
                            v_a_1487_ = crate::leanh::lean_ctor_get(v___x_1474_, 1);
                            v_isSharedCheck_1494_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1474_)) as u8;
                            if v_isSharedCheck_1494_ == 0 {
                                v___x_1489_ = v___x_1474_;
                                v_isShared_1490_ = v_isSharedCheck_1494_;
                                state = 9;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1487_);
                                crate::leanh::lean_inc(v_a_1486_);
                                crate::leanh::lean_dec(v___x_1474_);
                                v___x_1489_ = crate::leanh::lean_box(0);
                                v_isShared_1490_ = v_isSharedCheck_1494_;
                                state = 9;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_mkName_1376_);
                    crate::leanh::lean_dec(v_tk_1374_);
                    v___x_1495_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__33;
                    v___x_1496_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1496_, 0, v_holeOrTacticSeq_1375_);
                    crate::leanh::lean_ctor_set(v___x_1496_, 1, v___x_1495_);
                    v___x_1497_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1497_, 0, v___x_1496_);
                    crate::leanh::lean_ctor_set(v___x_1497_, 1, v___y_1378_);
                    return v___x_1497_;
                }
            }
            1 => {
                v_methods_1390_ = crate::leanh::lean_ctor_get(v___y_1377_, 0);
                v_quotContext_1391_ = crate::leanh::lean_ctor_get(v___y_1377_, 1);
                v_currRecDepth_1392_ = crate::leanh::lean_ctor_get(v___y_1377_, 3);
                v_maxRecDepth_1393_ = crate::leanh::lean_ctor_get(v___y_1377_, 4);
                v_ref_1394_ = crate::leanh::lean_ctor_get(v___y_1377_, 5);
                v___x_1395_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1396_ = lean_nat_add(v_macroScope_1384_, v___x_1395_);
                if v_isShared_1389_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1388_, 0, v___x_1396_);
                    v___x_1398_ = v___x_1388_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1463_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1463_, 0, v___x_1396_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1463_, 1, v_traceMsgs_1385_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1463_,
                        2,
                        v_expandedMacroDecls_1386_,
                    );
                    v___x_1398_ = v_reuseFailAlloc_1463_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_ref_1394_);
                crate::leanh::lean_inc(v_maxRecDepth_1393_);
                crate::leanh::lean_inc(v_currRecDepth_1392_);
                crate::leanh::lean_inc(v_quotContext_1391_);
                crate::leanh::lean_inc(v_methods_1390_);
                v___x_1399_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1399_, 0, v_methods_1390_);
                crate::leanh::lean_ctor_set(v___x_1399_, 1, v_quotContext_1391_);
                crate::leanh::lean_ctor_set(v___x_1399_, 2, v_macroScope_1384_);
                crate::leanh::lean_ctor_set(v___x_1399_, 3, v_currRecDepth_1392_);
                crate::leanh::lean_ctor_set(v___x_1399_, 4, v_maxRecDepth_1393_);
                crate::leanh::lean_ctor_set(v___x_1399_, 5, v_ref_1394_);
                v___x_1400_ = crate::leanh::lean_apply_2(v_mkName_1376_, v___x_1399_, v___x_1398_);
                if crate::leanh::lean_obj_tag(v___x_1400_) == 0 {
                    v_a_1401_ = crate::leanh::lean_ctor_get(v___x_1400_, 0);
                    v_a_1402_ = crate::leanh::lean_ctor_get(v___x_1400_, 1);
                    v_isSharedCheck_1453_ = (!crate::leanh::lean_is_exclusive(v___x_1400_)) as u8;
                    if v_isSharedCheck_1453_ == 0 {
                        v___x_1404_ = v___x_1400_;
                        v_isShared_1405_ = v_isSharedCheck_1453_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1402_);
                        crate::leanh::lean_inc(v_a_1401_);
                        crate::leanh::lean_dec(v___x_1400_);
                        v___x_1404_ = crate::leanh::lean_box(0);
                        v_isShared_1405_ = v_isSharedCheck_1453_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_holeOrTacticSeq_1375_);
                    crate::leanh::lean_dec(v_tk_1374_);
                    v_a_1454_ = crate::leanh::lean_ctor_get(v___x_1400_, 0);
                    v_a_1455_ = crate::leanh::lean_ctor_get(v___x_1400_, 1);
                    v_isSharedCheck_1462_ = (!crate::leanh::lean_is_exclusive(v___x_1400_)) as u8;
                    if v_isSharedCheck_1462_ == 0 {
                        v___x_1457_ = v___x_1400_;
                        v_isShared_1458_ = v_isSharedCheck_1462_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1455_);
                        crate::leanh::lean_inc(v_a_1454_);
                        crate::leanh::lean_dec(v___x_1400_);
                        v___x_1457_ = crate::leanh::lean_box(0);
                        v_isShared_1458_ = v_isSharedCheck_1462_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1406_ = 1;
                v___x_1407_ = l_Lean_Syntax_getArg(v_a_1401_, v___x_1395_);
                v___x_1408_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__9;
                v___x_1409_ = crate::leanh::lean_box(0);
                v___x_1410_ = l_Lean_SourceInfo_fromRef(v___x_1409_, v___x_1383_);
                v___x_1411_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__11;
                v___x_1412_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__13;
                v___x_1413_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__15;
                v___x_1414_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__16;
                crate::leanh::lean_inc_n(v___x_1410_, 10);
                v___x_1415_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1415_, 0, v___x_1410_);
                crate::leanh::lean_ctor_set(v___x_1415_, 1, v___x_1414_);
                v___x_1416_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__17;
                v___x_1417_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__18;
                v___x_1418_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1418_, 0, v___x_1410_);
                crate::leanh::lean_ctor_set(v___x_1418_, 1, v___x_1416_);
                v___x_1419_ = l_Lean_Syntax_node1(v___x_1410_, v___x_1417_, v___x_1418_);
                crate::leanh::lean_inc(v_tk_1374_);
                v___x_1420_ = l_Lean_Syntax_node3(
                    v___x_1410_,
                    v___x_1413_,
                    v___x_1415_,
                    v_tk_1374_,
                    v___x_1419_,
                );
                v___x_1421_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__19), core::ptr::addr_of_mut!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__19_once), _init_l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__19);
                v___x_1422_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1422_, 0, v___x_1410_);
                crate::leanh::lean_ctor_set(v___x_1422_, 1, v___x_1412_);
                crate::leanh::lean_ctor_set(v___x_1422_, 2, v___x_1421_);
                v___x_1423_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__21;
                v___x_1424_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__22;
                v___x_1425_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1425_, 0, v___x_1410_);
                crate::leanh::lean_ctor_set(v___x_1425_, 1, v___x_1424_);
                v___x_1426_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__23;
                v___x_1427_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1427_, 0, v___x_1410_);
                crate::leanh::lean_ctor_set(v___x_1427_, 1, v___x_1426_);
                v___x_1428_ = l_Lean_Syntax_node3(
                    v___x_1410_,
                    v___x_1423_,
                    v___x_1425_,
                    v_holeOrTacticSeq_1375_,
                    v___x_1427_,
                );
                v___x_1429_ = l_Lean_Syntax_node3(
                    v___x_1410_,
                    v___x_1412_,
                    v___x_1420_,
                    v___x_1422_,
                    v___x_1428_,
                );
                v___x_1430_ = l_Lean_Syntax_node1(v___x_1410_, v___x_1411_, v___x_1429_);
                v___x_1431_ = l_Lean_Syntax_node1(v___x_1410_, v___x_1408_, v___x_1430_);
                v_ref_1432_ = l_Lean_replaceRef(v_tk_1374_, v_ref_1394_);
                v___x_1433_ = l_Lean_SourceInfo_fromRef(v_ref_1432_, v___x_1383_);
                crate::leanh::lean_dec(v_ref_1432_);
                v___x_1434_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__24;
                v___x_1435_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__25;
                crate::leanh::lean_inc_n(v___x_1433_, 5);
                v___x_1436_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1436_, 0, v___x_1433_);
                crate::leanh::lean_ctor_set(v___x_1436_, 1, v___x_1434_);
                v___x_1437_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__27;
                v___x_1438_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__29;
                v___x_1439_ = l_Lean_Syntax_node1(v___x_1433_, v___x_1438_, v___x_1407_);
                v___x_1440_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1440_, 0, v___x_1433_);
                crate::leanh::lean_ctor_set(v___x_1440_, 1, v___x_1412_);
                crate::leanh::lean_ctor_set(v___x_1440_, 2, v___x_1421_);
                v___x_1441_ =
                    l_Lean_Syntax_node2(v___x_1433_, v___x_1437_, v___x_1439_, v___x_1440_);
                v___x_1442_ = l_Lean_Syntax_node1(v___x_1433_, v___x_1412_, v___x_1441_);
                v___x_1443_ = l_Lean_SourceInfo_fromRef(v_tk_1374_, v___x_1406_);
                crate::leanh::lean_dec(v_tk_1374_);
                v___x_1444_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__30;
                v___x_1445_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1445_, 0, v___x_1443_);
                crate::leanh::lean_ctor_set(v___x_1445_, 1, v___x_1444_);
                v___x_1446_ = l_Lean_Syntax_node4(
                    v___x_1433_,
                    v___x_1435_,
                    v___x_1436_,
                    v___x_1442_,
                    v___x_1445_,
                    v___x_1431_,
                );
                v___x_1447_ = lean_mk_empty_array_with_capacity(v___x_1395_);
                v___x_1448_ = lean_array_push(v___x_1447_, v___x_1446_);
                v___x_1449_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1449_, 0, v_a_1401_);
                crate::leanh::lean_ctor_set(v___x_1449_, 1, v___x_1448_);
                if v_isShared_1405_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1404_, 0, v___x_1449_);
                    v___x_1451_ = v___x_1404_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1452_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1452_, 0, v___x_1449_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1452_, 1, v_a_1402_);
                    v___x_1451_ = v_reuseFailAlloc_1452_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1451_;
            }
            5 => {
                if v_isShared_1458_ == 0 {
                    v___x_1460_ = v___x_1457_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1461_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1461_, 0, v_a_1454_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1461_, 1, v_a_1455_);
                    v___x_1460_ = v_reuseFailAlloc_1461_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1460_;
            }
            7 => {
                v___x_1480_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__33;
                v___x_1481_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1481_, 0, v_a_1475_);
                crate::leanh::lean_ctor_set(v___x_1481_, 1, v___x_1480_);
                if v_isShared_1479_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1478_, 0, v___x_1481_);
                    v___x_1483_ = v___x_1478_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1484_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1484_, 0, v___x_1481_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1484_, 1, v_a_1476_);
                    v___x_1483_ = v_reuseFailAlloc_1484_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1483_;
            }
            9 => {
                if v_isShared_1490_ == 0 {
                    v___x_1492_ = v___x_1489_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1493_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1493_, 0, v_a_1486_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1493_, 1, v_a_1487_);
                    v___x_1492_ = v_reuseFailAlloc_1493_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1492_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___boxed(
    mut v_tk_1498_: *mut crate::leanh::LeanObject,
    mut v_holeOrTacticSeq_1499_: *mut crate::leanh::LeanObject,
    mut v_mkName_1500_: *mut crate::leanh::LeanObject,
    mut v___y_1501_: *mut crate::leanh::LeanObject,
    mut v___y_1502_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1503_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0(
        v_tk_1498_,
        v_holeOrTacticSeq_1499_,
        v_mkName_1500_,
        v___y_1501_,
        v___y_1502_,
    );
    crate::leanh::lean_dec_ref(v___y_1501_);
    return v_res_1503_;
}
pub unsafe fn l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__1(
    mut v_ctx_1504_: *mut crate::leanh::LeanObject,
    mut v___y_1505_: *mut crate::leanh::LeanObject,
    mut v___y_1506_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_1507_ = crate::leanh::lean_ctor_get(v_ctx_1504_, 5);
    crate::leanh::lean_inc(v_ref_1507_);
    v___x_1508_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1508_, 0, v_ref_1507_);
    crate::leanh::lean_ctor_set(v___x_1508_, 1, v___y_1506_);
    return v___x_1508_;
}
pub unsafe fn l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__1___boxed(
    mut v_ctx_1509_: *mut crate::leanh::LeanObject,
    mut v___y_1510_: *mut crate::leanh::LeanObject,
    mut v___y_1511_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1512_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__1(
        v_ctx_1509_,
        v___y_1510_,
        v___y_1511_,
    );
    crate::leanh::lean_dec_ref(v___y_1510_);
    crate::leanh::lean_dec_ref(v_ctx_1509_);
    return v_res_1512_;
}
pub unsafe fn l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__2(
    mut v_____do__lift_1513_: *mut crate::leanh::LeanObject,
    mut v___y_1514_: *mut crate::leanh::LeanObject,
    mut v___y_1515_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1516_: u8 = 0;
    let mut v___x_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1516_ = 0;
    v___x_1517_ = l_Lean_SourceInfo_fromRef(v_____do__lift_1513_, v___x_1516_);
    v___x_1518_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1518_, 0, v___x_1517_);
    crate::leanh::lean_ctor_set(v___x_1518_, 1, v___y_1515_);
    return v___x_1518_;
}
pub unsafe fn l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__2___boxed(
    mut v_____do__lift_1519_: *mut crate::leanh::LeanObject,
    mut v___y_1520_: *mut crate::leanh::LeanObject,
    mut v___y_1521_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1522_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__2(
        v_____do__lift_1519_,
        v___y_1520_,
        v___y_1521_,
    );
    crate::leanh::lean_dec_ref(v___y_1520_);
    crate::leanh::lean_dec(v_____do__lift_1519_);
    return v_res_1522_;
}
pub unsafe fn _init_l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__3___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1525_ =
        l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__3___closed__1;
    v___x_1526_ = l_String_toRawSubstring_x27(v___x_1525_);
    return v___x_1526_;
}
pub unsafe fn l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__3(
    mut v___f_1529_: *mut crate::leanh::LeanObject,
    mut v___f_1530_: *mut crate::leanh::LeanObject,
    mut v___y_1531_: *mut crate::leanh::LeanObject,
    mut v___y_1532_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1541_: u8 = 0;
    let mut v_quotContext_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1556_: u8 = 0;
    let mut v_a_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1561_: u8 = 0;
    let mut v___x_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1565_: u8 = 0;
    let mut v_a_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1570_: u8 = 0;
    let mut v___x_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1574_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref_n(v___y_1531_, 2);
                v___x_1533_ =
                    crate::leanh::lean_apply_3(v___f_1529_, v___y_1531_, v___y_1531_, v___y_1532_);
                if crate::leanh::lean_obj_tag(v___x_1533_) == 0 {
                    v_a_1534_ = crate::leanh::lean_ctor_get(v___x_1533_, 0);
                    crate::leanh::lean_inc(v_a_1534_);
                    v_a_1535_ = crate::leanh::lean_ctor_get(v___x_1533_, 1);
                    crate::leanh::lean_inc(v_a_1535_);
                    crate::leanh::lean_dec_ref_known(v___x_1533_, 2);
                    crate::leanh::lean_inc_ref(v___y_1531_);
                    v___x_1536_ =
                        crate::leanh::lean_apply_3(v___f_1530_, v_a_1534_, v___y_1531_, v_a_1535_);
                    if crate::leanh::lean_obj_tag(v___x_1536_) == 0 {
                        v_a_1537_ = crate::leanh::lean_ctor_get(v___x_1536_, 0);
                        v_a_1538_ = crate::leanh::lean_ctor_get(v___x_1536_, 1);
                        v_isSharedCheck_1556_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1536_)) as u8;
                        if v_isSharedCheck_1556_ == 0 {
                            v___x_1540_ = v___x_1536_;
                            v_isShared_1541_ = v_isSharedCheck_1556_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1538_);
                            crate::leanh::lean_inc(v_a_1537_);
                            crate::leanh::lean_dec(v___x_1536_);
                            v___x_1540_ = crate::leanh::lean_box(0);
                            v_isShared_1541_ = v_isSharedCheck_1556_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1557_ = crate::leanh::lean_ctor_get(v___x_1536_, 0);
                        v_a_1558_ = crate::leanh::lean_ctor_get(v___x_1536_, 1);
                        v_isSharedCheck_1565_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1536_)) as u8;
                        if v_isSharedCheck_1565_ == 0 {
                            v___x_1560_ = v___x_1536_;
                            v_isShared_1561_ = v_isSharedCheck_1565_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1558_);
                            crate::leanh::lean_inc(v_a_1557_);
                            crate::leanh::lean_dec(v___x_1536_);
                            v___x_1560_ = crate::leanh::lean_box(0);
                            v_isShared_1561_ = v_isSharedCheck_1565_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___f_1530_);
                    v_a_1566_ = crate::leanh::lean_ctor_get(v___x_1533_, 0);
                    v_a_1567_ = crate::leanh::lean_ctor_get(v___x_1533_, 1);
                    v_isSharedCheck_1574_ = (!crate::leanh::lean_is_exclusive(v___x_1533_)) as u8;
                    if v_isSharedCheck_1574_ == 0 {
                        v___x_1569_ = v___x_1533_;
                        v_isShared_1570_ = v_isSharedCheck_1574_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1567_);
                        crate::leanh::lean_inc(v_a_1566_);
                        crate::leanh::lean_dec(v___x_1533_);
                        v___x_1569_ = crate::leanh::lean_box(0);
                        v_isShared_1570_ = v_isSharedCheck_1574_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_quotContext_1542_ = crate::leanh::lean_ctor_get(v___y_1531_, 1);
                v_currMacroScope_1543_ = crate::leanh::lean_ctor_get(v___y_1531_, 2);
                v___x_1544_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__4;
                v___x_1545_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__3___closed__0;
                crate::leanh::lean_inc_n(v_a_1537_, 2);
                v___x_1546_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1546_, 0, v_a_1537_);
                crate::leanh::lean_ctor_set(v___x_1546_, 1, v___x_1545_);
                v___x_1547_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__3___closed__2), core::ptr::addr_of_mut!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__3___closed__2_once), _init_l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__3___closed__2);
                v___x_1548_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__3___closed__3;
                crate::leanh::lean_inc(v_currMacroScope_1543_);
                crate::leanh::lean_inc(v_quotContext_1542_);
                v___x_1549_ =
                    l_Lean_addMacroScope(v_quotContext_1542_, v___x_1548_, v_currMacroScope_1543_);
                v___x_1550_ = crate::leanh::lean_box(0);
                v___x_1551_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1551_, 0, v_a_1537_);
                crate::leanh::lean_ctor_set(v___x_1551_, 1, v___x_1547_);
                crate::leanh::lean_ctor_set(v___x_1551_, 2, v___x_1549_);
                crate::leanh::lean_ctor_set(v___x_1551_, 3, v___x_1550_);
                v___x_1552_ = l_Lean_Syntax_node2(v_a_1537_, v___x_1544_, v___x_1546_, v___x_1551_);
                if v_isShared_1541_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1540_, 0, v___x_1552_);
                    v___x_1554_ = v___x_1540_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1555_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1555_, 0, v___x_1552_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1555_, 1, v_a_1538_);
                    v___x_1554_ = v_reuseFailAlloc_1555_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1554_;
            }
            3 => {
                if v_isShared_1561_ == 0 {
                    v___x_1563_ = v___x_1560_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1564_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1564_, 0, v_a_1557_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1564_, 1, v_a_1558_);
                    v___x_1563_ = v_reuseFailAlloc_1564_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1563_;
            }
            5 => {
                if v_isShared_1570_ == 0 {
                    v___x_1572_ = v___x_1569_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1573_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1573_, 0, v_a_1566_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1573_, 1, v_a_1567_);
                    v___x_1572_ = v_reuseFailAlloc_1573_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1572_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__3___boxed(
    mut v___f_1575_: *mut crate::leanh::LeanObject,
    mut v___f_1576_: *mut crate::leanh::LeanObject,
    mut v___y_1577_: *mut crate::leanh::LeanObject,
    mut v___y_1578_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1579_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__3(
        v___f_1575_,
        v___f_1576_,
        v___y_1577_,
        v___y_1578_,
    );
    crate::leanh::lean_dec_ref(v___y_1577_);
    return v_res_1579_;
}
pub unsafe fn _init_l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__4___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1581_ =
        l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__4___closed__0;
    v___x_1582_ = l_String_toRawSubstring_x27(v___x_1581_);
    return v___x_1582_;
}
pub unsafe fn l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__4(
    mut v___f_1585_: *mut crate::leanh::LeanObject,
    mut v___f_1586_: *mut crate::leanh::LeanObject,
    mut v___y_1587_: *mut crate::leanh::LeanObject,
    mut v___y_1588_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1597_: u8 = 0;
    let mut v_quotContext_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1612_: u8 = 0;
    let mut v_a_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1617_: u8 = 0;
    let mut v___x_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1621_: u8 = 0;
    let mut v_a_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1626_: u8 = 0;
    let mut v___x_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1630_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref_n(v___y_1587_, 2);
                v___x_1589_ =
                    crate::leanh::lean_apply_3(v___f_1585_, v___y_1587_, v___y_1587_, v___y_1588_);
                if crate::leanh::lean_obj_tag(v___x_1589_) == 0 {
                    v_a_1590_ = crate::leanh::lean_ctor_get(v___x_1589_, 0);
                    crate::leanh::lean_inc(v_a_1590_);
                    v_a_1591_ = crate::leanh::lean_ctor_get(v___x_1589_, 1);
                    crate::leanh::lean_inc(v_a_1591_);
                    crate::leanh::lean_dec_ref_known(v___x_1589_, 2);
                    crate::leanh::lean_inc_ref(v___y_1587_);
                    v___x_1592_ =
                        crate::leanh::lean_apply_3(v___f_1586_, v_a_1590_, v___y_1587_, v_a_1591_);
                    if crate::leanh::lean_obj_tag(v___x_1592_) == 0 {
                        v_a_1593_ = crate::leanh::lean_ctor_get(v___x_1592_, 0);
                        v_a_1594_ = crate::leanh::lean_ctor_get(v___x_1592_, 1);
                        v_isSharedCheck_1612_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1592_)) as u8;
                        if v_isSharedCheck_1612_ == 0 {
                            v___x_1596_ = v___x_1592_;
                            v_isShared_1597_ = v_isSharedCheck_1612_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1594_);
                            crate::leanh::lean_inc(v_a_1593_);
                            crate::leanh::lean_dec(v___x_1592_);
                            v___x_1596_ = crate::leanh::lean_box(0);
                            v_isShared_1597_ = v_isSharedCheck_1612_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1613_ = crate::leanh::lean_ctor_get(v___x_1592_, 0);
                        v_a_1614_ = crate::leanh::lean_ctor_get(v___x_1592_, 1);
                        v_isSharedCheck_1621_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1592_)) as u8;
                        if v_isSharedCheck_1621_ == 0 {
                            v___x_1616_ = v___x_1592_;
                            v_isShared_1617_ = v_isSharedCheck_1621_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1614_);
                            crate::leanh::lean_inc(v_a_1613_);
                            crate::leanh::lean_dec(v___x_1592_);
                            v___x_1616_ = crate::leanh::lean_box(0);
                            v_isShared_1617_ = v_isSharedCheck_1621_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___f_1586_);
                    v_a_1622_ = crate::leanh::lean_ctor_get(v___x_1589_, 0);
                    v_a_1623_ = crate::leanh::lean_ctor_get(v___x_1589_, 1);
                    v_isSharedCheck_1630_ = (!crate::leanh::lean_is_exclusive(v___x_1589_)) as u8;
                    if v_isSharedCheck_1630_ == 0 {
                        v___x_1625_ = v___x_1589_;
                        v_isShared_1626_ = v_isSharedCheck_1630_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1623_);
                        crate::leanh::lean_inc(v_a_1622_);
                        crate::leanh::lean_dec(v___x_1589_);
                        v___x_1625_ = crate::leanh::lean_box(0);
                        v_isShared_1626_ = v_isSharedCheck_1630_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_quotContext_1598_ = crate::leanh::lean_ctor_get(v___y_1587_, 1);
                v_currMacroScope_1599_ = crate::leanh::lean_ctor_get(v___y_1587_, 2);
                v___x_1600_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__4;
                v___x_1601_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__3___closed__0;
                crate::leanh::lean_inc_n(v_a_1593_, 2);
                v___x_1602_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1602_, 0, v_a_1593_);
                crate::leanh::lean_ctor_set(v___x_1602_, 1, v___x_1601_);
                v___x_1603_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__4___closed__1), core::ptr::addr_of_mut!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__4___closed__1_once), _init_l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__4___closed__1);
                v___x_1604_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__4___closed__2;
                crate::leanh::lean_inc(v_currMacroScope_1599_);
                crate::leanh::lean_inc(v_quotContext_1598_);
                v___x_1605_ =
                    l_Lean_addMacroScope(v_quotContext_1598_, v___x_1604_, v_currMacroScope_1599_);
                v___x_1606_ = crate::leanh::lean_box(0);
                v___x_1607_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1607_, 0, v_a_1593_);
                crate::leanh::lean_ctor_set(v___x_1607_, 1, v___x_1603_);
                crate::leanh::lean_ctor_set(v___x_1607_, 2, v___x_1605_);
                crate::leanh::lean_ctor_set(v___x_1607_, 3, v___x_1606_);
                v___x_1608_ = l_Lean_Syntax_node2(v_a_1593_, v___x_1600_, v___x_1602_, v___x_1607_);
                if v_isShared_1597_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1596_, 0, v___x_1608_);
                    v___x_1610_ = v___x_1596_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1611_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1611_, 0, v___x_1608_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1611_, 1, v_a_1594_);
                    v___x_1610_ = v_reuseFailAlloc_1611_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1610_;
            }
            3 => {
                if v_isShared_1617_ == 0 {
                    v___x_1619_ = v___x_1616_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1620_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1620_, 0, v_a_1613_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1620_, 1, v_a_1614_);
                    v___x_1619_ = v_reuseFailAlloc_1620_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1619_;
            }
            5 => {
                if v_isShared_1626_ == 0 {
                    v___x_1628_ = v___x_1625_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1629_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1629_, 0, v_a_1622_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1629_, 1, v_a_1623_);
                    v___x_1628_ = v_reuseFailAlloc_1629_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1628_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__4___boxed(
    mut v___f_1631_: *mut crate::leanh::LeanObject,
    mut v___f_1632_: *mut crate::leanh::LeanObject,
    mut v___y_1633_: *mut crate::leanh::LeanObject,
    mut v___y_1634_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1635_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__4(
        v___f_1631_,
        v___f_1632_,
        v___y_1633_,
        v___y_1634_,
    );
    crate::leanh::lean_dec_ref(v___y_1633_);
    return v_res_1635_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse_spec__0(
    mut v_sz_1636_: usize,
    mut v_i_1637_: usize,
    mut v_bs_1638_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1639_: u8 = 0;
    let mut v_v_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: usize = 0;
    let mut v___x_1644_: usize = 0;
    let mut v___x_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1639_ = lean_usize_dec_lt(v_i_1637_, v_sz_1636_);
                if v___x_1639_ == 0 {
                    return v_bs_1638_;
                } else {
                    v_v_1640_ = lean_array_uget(v_bs_1638_, v_i_1637_);
                    v___x_1641_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1642_ = lean_array_uset(v_bs_1638_, v_i_1637_, v___x_1641_);
                    v___x_1643_ = 1usize;
                    v___x_1644_ = lean_usize_add(v_i_1637_, v___x_1643_);
                    v___x_1645_ = lean_array_uset(v_bs_x27_1642_, v_i_1637_, v_v_1640_);
                    v_i_1637_ = v___x_1644_;
                    v_bs_1638_ = v___x_1645_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse_spec__0___boxed(
    mut v_sz_1647_: *mut crate::leanh::LeanObject,
    mut v_i_1648_: *mut crate::leanh::LeanObject,
    mut v_bs_1649_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1650_: usize = 0;
    let mut v_i_boxed_1651_: usize = 0;
    let mut v_res_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1650_ = crate::leanh::lean_unbox_usize(v_sz_1647_);
    crate::leanh::lean_dec(v_sz_1647_);
    v_i_boxed_1651_ = crate::leanh::lean_unbox_usize(v_i_1648_);
    crate::leanh::lean_dec(v_i_1648_);
    v_res_1652_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse_spec__0(v_sz_boxed_1650_, v_i_boxed_1651_, v_bs_1649_);
    return v_res_1652_;
}
pub unsafe fn _init_l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1675_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__9;
    v___x_1676_ = l_String_toRawSubstring_x27(v___x_1675_);
    return v___x_1676_;
}
pub unsafe fn l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse(
    mut v_ifTk_1698_: *mut crate::leanh::LeanObject,
    mut v_thenTk_1699_: *mut crate::leanh::LeanObject,
    mut v_elseTk_1700_: *mut crate::leanh::LeanObject,
    mut v_pos_1701_: *mut crate::leanh::LeanObject,
    mut v_neg_1702_: *mut crate::leanh::LeanObject,
    mut v_mkIf_1703_: *mut crate::leanh::LeanObject,
    mut v_a_1704_: *mut crate::leanh::LeanObject,
    mut v_a_1705_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1714_: u8 = 0;
    let mut v___f_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1723_: u8 = 0;
    let mut v___x_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1729_: u8 = 0;
    let mut v_quotContext_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: u8 = 0;
    let mut v___x_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: u8 = 0;
    let mut v___x_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1776_: usize = 0;
    let mut v___x_1777_: usize = 0;
    let mut v___x_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1791_: u8 = 0;
    let mut v_isSharedCheck_1792_: u8 = 0;
    let mut v_a_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1797_: u8 = 0;
    let mut v___x_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1801_: u8 = 0;
    let mut v_isSharedCheck_1802_: u8 = 0;
    let mut v_a_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1807_: u8 = 0;
    let mut v___x_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1811_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1706_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__2;
                v___x_1707_ =
                    l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0(
                        v_thenTk_1699_,
                        v_pos_1701_,
                        v___f_1706_,
                        v_a_1704_,
                        v_a_1705_,
                    );
                if crate::leanh::lean_obj_tag(v___x_1707_) == 0 {
                    v_a_1708_ = crate::leanh::lean_ctor_get(v___x_1707_, 0);
                    crate::leanh::lean_inc(v_a_1708_);
                    v_a_1709_ = crate::leanh::lean_ctor_get(v___x_1707_, 1);
                    crate::leanh::lean_inc(v_a_1709_);
                    crate::leanh::lean_dec_ref_known(v___x_1707_, 2);
                    v_fst_1710_ = crate::leanh::lean_ctor_get(v_a_1708_, 0);
                    v_snd_1711_ = crate::leanh::lean_ctor_get(v_a_1708_, 1);
                    v_isSharedCheck_1802_ = (!crate::leanh::lean_is_exclusive(v_a_1708_)) as u8;
                    if v_isSharedCheck_1802_ == 0 {
                        v___x_1713_ = v_a_1708_;
                        v_isShared_1714_ = v_isSharedCheck_1802_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_1711_);
                        crate::leanh::lean_inc(v_fst_1710_);
                        crate::leanh::lean_dec(v_a_1708_);
                        v___x_1713_ = crate::leanh::lean_box(0);
                        v_isShared_1714_ = v_isSharedCheck_1802_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_mkIf_1703_);
                    crate::leanh::lean_dec(v_neg_1702_);
                    crate::leanh::lean_dec(v_elseTk_1700_);
                    v_a_1803_ = crate::leanh::lean_ctor_get(v___x_1707_, 0);
                    v_a_1804_ = crate::leanh::lean_ctor_get(v___x_1707_, 1);
                    v_isSharedCheck_1811_ = (!crate::leanh::lean_is_exclusive(v___x_1707_)) as u8;
                    if v_isSharedCheck_1811_ == 0 {
                        v___x_1806_ = v___x_1707_;
                        v_isShared_1807_ = v_isSharedCheck_1811_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1804_);
                        crate::leanh::lean_inc(v_a_1803_);
                        crate::leanh::lean_dec(v___x_1707_);
                        v___x_1806_ = crate::leanh::lean_box(0);
                        v_isShared_1807_ = v_isSharedCheck_1811_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___f_1715_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__3;
                v___x_1716_ =
                    l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0(
                        v_elseTk_1700_,
                        v_neg_1702_,
                        v___f_1715_,
                        v_a_1704_,
                        v_a_1709_,
                    );
                if crate::leanh::lean_obj_tag(v___x_1716_) == 0 {
                    v_a_1717_ = crate::leanh::lean_ctor_get(v___x_1716_, 0);
                    crate::leanh::lean_inc(v_a_1717_);
                    v_a_1718_ = crate::leanh::lean_ctor_get(v___x_1716_, 1);
                    crate::leanh::lean_inc(v_a_1718_);
                    crate::leanh::lean_dec_ref_known(v___x_1716_, 2);
                    v_fst_1719_ = crate::leanh::lean_ctor_get(v_a_1717_, 0);
                    v_snd_1720_ = crate::leanh::lean_ctor_get(v_a_1717_, 1);
                    v_isSharedCheck_1792_ = (!crate::leanh::lean_is_exclusive(v_a_1717_)) as u8;
                    if v_isSharedCheck_1792_ == 0 {
                        v___x_1722_ = v_a_1717_;
                        v_isShared_1723_ = v_isSharedCheck_1792_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_1720_);
                        crate::leanh::lean_inc(v_fst_1719_);
                        crate::leanh::lean_dec(v_a_1717_);
                        v___x_1722_ = crate::leanh::lean_box(0);
                        v_isShared_1723_ = v_isSharedCheck_1792_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1713_);
                    crate::leanh::lean_dec(v_snd_1711_);
                    crate::leanh::lean_dec(v_fst_1710_);
                    crate::leanh::lean_dec_ref(v_mkIf_1703_);
                    v_a_1793_ = crate::leanh::lean_ctor_get(v___x_1716_, 0);
                    v_a_1794_ = crate::leanh::lean_ctor_get(v___x_1716_, 1);
                    v_isSharedCheck_1801_ = (!crate::leanh::lean_is_exclusive(v___x_1716_)) as u8;
                    if v_isSharedCheck_1801_ == 0 {
                        v___x_1796_ = v___x_1716_;
                        v_isShared_1797_ = v_isSharedCheck_1801_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1794_);
                        crate::leanh::lean_inc(v_a_1793_);
                        crate::leanh::lean_dec(v___x_1716_);
                        v___x_1796_ = crate::leanh::lean_box(0);
                        v_isShared_1797_ = v_isSharedCheck_1801_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                crate::leanh::lean_inc_ref(v_a_1704_);
                v___x_1724_ = crate::leanh::lean_apply_4(
                    v_mkIf_1703_,
                    v_fst_1710_,
                    v_fst_1719_,
                    v_a_1704_,
                    v_a_1718_,
                );
                if crate::leanh::lean_obj_tag(v___x_1724_) == 0 {
                    v_a_1725_ = crate::leanh::lean_ctor_get(v___x_1724_, 0);
                    v_a_1726_ = crate::leanh::lean_ctor_get(v___x_1724_, 1);
                    v_isSharedCheck_1791_ = (!crate::leanh::lean_is_exclusive(v___x_1724_)) as u8;
                    if v_isSharedCheck_1791_ == 0 {
                        v___x_1728_ = v___x_1724_;
                        v_isShared_1729_ = v_isSharedCheck_1791_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1726_);
                        crate::leanh::lean_inc(v_a_1725_);
                        crate::leanh::lean_dec(v___x_1724_);
                        v___x_1728_ = crate::leanh::lean_box(0);
                        v_isShared_1729_ = v_isSharedCheck_1791_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1722_);
                    crate::leanh::lean_dec(v_snd_1720_);
                    crate::leanh::lean_del_object(v___x_1713_);
                    crate::leanh::lean_dec(v_snd_1711_);
                    return v___x_1724_;
                }
            }
            3 => {
                v_quotContext_1730_ = crate::leanh::lean_ctor_get(v_a_1704_, 1);
                v_currMacroScope_1731_ = crate::leanh::lean_ctor_get(v_a_1704_, 2);
                v_ref_1732_ = crate::leanh::lean_ctor_get(v_a_1704_, 5);
                v___x_1733_ = 0;
                v___x_1734_ = l_Lean_SourceInfo_fromRef(v_ref_1732_, v___x_1733_);
                v___x_1735_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__21;
                v___x_1736_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__22;
                crate::leanh::lean_inc(v___x_1734_);
                if v_isShared_1723_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1722_, 2);
                    crate::leanh::lean_ctor_set(v___x_1722_, 1, v___x_1736_);
                    crate::leanh::lean_ctor_set(v___x_1722_, 0, v___x_1734_);
                    v___x_1738_ = v___x_1722_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1790_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1790_, 0, v___x_1734_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1790_, 1, v___x_1736_);
                    v___x_1738_ = v_reuseFailAlloc_1790_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1739_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__9;
                v___x_1740_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__11;
                v___x_1741_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__13;
                v___x_1742_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__4;
                v___x_1743_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__5;
                crate::leanh::lean_inc(v___x_1734_);
                if v_isShared_1714_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1713_, 2);
                    crate::leanh::lean_ctor_set(v___x_1713_, 1, v___x_1742_);
                    crate::leanh::lean_ctor_set(v___x_1713_, 0, v___x_1734_);
                    v___x_1745_ = v___x_1713_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1789_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1789_, 0, v___x_1734_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1789_, 1, v___x_1742_);
                    v___x_1745_ = v_reuseFailAlloc_1789_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1746_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__8;
                v___x_1747_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__10), core::ptr::addr_of_mut!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__10_once), _init_l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__10);
                v___x_1748_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__11;
                crate::leanh::lean_inc(v_currMacroScope_1731_);
                crate::leanh::lean_inc(v_quotContext_1730_);
                v___x_1749_ =
                    l_Lean_addMacroScope(v_quotContext_1730_, v___x_1748_, v_currMacroScope_1731_);
                v___x_1750_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__13;
                crate::leanh::lean_inc_n(v___x_1734_, 18);
                v___x_1751_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1751_, 0, v___x_1734_);
                crate::leanh::lean_ctor_set(v___x_1751_, 1, v___x_1747_);
                crate::leanh::lean_ctor_set(v___x_1751_, 2, v___x_1749_);
                crate::leanh::lean_ctor_set(v___x_1751_, 3, v___x_1750_);
                v___x_1752_ = l_Lean_Syntax_node1(v___x_1734_, v___x_1741_, v___x_1751_);
                v___x_1753_ = l_Lean_Syntax_node1(v___x_1734_, v___x_1746_, v___x_1752_);
                v___x_1754_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__14;
                v___x_1755_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1755_, 0, v___x_1734_);
                crate::leanh::lean_ctor_set(v___x_1755_, 1, v___x_1754_);
                v___x_1756_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__15;
                v___x_1757_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__16;
                v___x_1758_ = 1;
                v___x_1759_ = l_Lean_SourceInfo_fromRef(v_ifTk_1698_, v___x_1758_);
                v___x_1760_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1760_, 0, v___x_1759_);
                crate::leanh::lean_ctor_set(v___x_1760_, 1, v___x_1756_);
                v___x_1761_ = l_Lean_Syntax_node2(v___x_1734_, v___x_1757_, v___x_1760_, v_a_1725_);
                v___x_1762_ = l_Lean_Syntax_node1(v___x_1734_, v___x_1741_, v___x_1761_);
                v___x_1763_ = l_Lean_Syntax_node1(v___x_1734_, v___x_1740_, v___x_1762_);
                v___x_1764_ = l_Lean_Syntax_node1(v___x_1734_, v___x_1739_, v___x_1763_);
                v___x_1765_ = l_Lean_Syntax_node4(
                    v___x_1734_,
                    v___x_1743_,
                    v___x_1745_,
                    v___x_1753_,
                    v___x_1755_,
                    v___x_1764_,
                );
                v___x_1766_ = l_Lean_Syntax_node1(v___x_1734_, v___x_1741_, v___x_1765_);
                v___x_1767_ = l_Lean_Syntax_node1(v___x_1734_, v___x_1740_, v___x_1766_);
                v___x_1768_ = l_Lean_Syntax_node1(v___x_1734_, v___x_1739_, v___x_1767_);
                v___x_1769_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__23;
                v___x_1770_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1770_, 0, v___x_1734_);
                crate::leanh::lean_ctor_set(v___x_1770_, 1, v___x_1769_);
                crate::leanh::lean_inc_ref(v___x_1770_);
                crate::leanh::lean_inc_ref(v___x_1738_);
                v___x_1771_ = l_Lean_Syntax_node3(
                    v___x_1734_,
                    v___x_1735_,
                    v___x_1738_,
                    v___x_1768_,
                    v___x_1770_,
                );
                v___x_1772_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__17;
                v___x_1773_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1773_, 0, v___x_1734_);
                crate::leanh::lean_ctor_set(v___x_1773_, 1, v___x_1772_);
                v___x_1774_ = l_Array_mkArray2___redArg(v___x_1771_, v___x_1773_);
                v___x_1775_ = l_Array_append___redArg(v_snd_1711_, v_snd_1720_);
                crate::leanh::lean_dec(v_snd_1720_);
                v_sz_1776_ = lean_array_size(v___x_1775_);
                v___x_1777_ = 0usize;
                v___x_1778_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse_spec__0(v_sz_1776_, v___x_1777_, v___x_1775_);
                v___x_1779_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__19;
                v___x_1780_ = l_Lean_mkSepArray(v___x_1778_, v___x_1779_);
                crate::leanh::lean_dec_ref(v___x_1778_);
                v___x_1781_ = l_Array_append___redArg(v___x_1774_, v___x_1780_);
                crate::leanh::lean_dec_ref(v___x_1780_);
                v___x_1782_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1782_, 0, v___x_1734_);
                crate::leanh::lean_ctor_set(v___x_1782_, 1, v___x_1741_);
                crate::leanh::lean_ctor_set(v___x_1782_, 2, v___x_1781_);
                v___x_1783_ = l_Lean_Syntax_node1(v___x_1734_, v___x_1740_, v___x_1782_);
                v___x_1784_ = l_Lean_Syntax_node1(v___x_1734_, v___x_1739_, v___x_1783_);
                v___x_1785_ = l_Lean_Syntax_node3(
                    v___x_1734_,
                    v___x_1735_,
                    v___x_1738_,
                    v___x_1784_,
                    v___x_1770_,
                );
                if v_isShared_1729_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1728_, 0, v___x_1785_);
                    v___x_1787_ = v___x_1728_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1788_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1788_, 0, v___x_1785_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1788_, 1, v_a_1726_);
                    v___x_1787_ = v_reuseFailAlloc_1788_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1787_;
            }
            7 => {
                if v_isShared_1797_ == 0 {
                    v___x_1799_ = v___x_1796_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1800_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1800_, 0, v_a_1793_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1800_, 1, v_a_1794_);
                    v___x_1799_ = v_reuseFailAlloc_1800_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1799_;
            }
            9 => {
                if v_isShared_1807_ == 0 {
                    v___x_1809_ = v___x_1806_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1810_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1810_, 0, v_a_1803_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1810_, 1, v_a_1804_);
                    v___x_1809_ = v_reuseFailAlloc_1810_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1809_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___boxed(
    mut v_ifTk_1812_: *mut crate::leanh::LeanObject,
    mut v_thenTk_1813_: *mut crate::leanh::LeanObject,
    mut v_elseTk_1814_: *mut crate::leanh::LeanObject,
    mut v_pos_1815_: *mut crate::leanh::LeanObject,
    mut v_neg_1816_: *mut crate::leanh::LeanObject,
    mut v_mkIf_1817_: *mut crate::leanh::LeanObject,
    mut v_a_1818_: *mut crate::leanh::LeanObject,
    mut v_a_1819_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1820_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse(
        v_ifTk_1812_,
        v_thenTk_1813_,
        v_elseTk_1814_,
        v_pos_1815_,
        v_neg_1816_,
        v_mkIf_1817_,
        v_a_1818_,
        v_a_1819_,
    );
    crate::leanh::lean_dec_ref(v_a_1818_);
    crate::leanh::lean_dec(v_ifTk_1812_);
    return v_res_1820_;
}
pub unsafe fn l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0(
    mut v___x_1828_: *mut crate::leanh::LeanObject,
    mut v___x_1829_: *mut crate::leanh::LeanObject,
    mut v_pos_1830_: *mut crate::leanh::LeanObject,
    mut v_neg_1831_: *mut crate::leanh::LeanObject,
    mut v___y_1832_: *mut crate::leanh::LeanObject,
    mut v___y_1833_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: u8 = 0;
    let mut v___x_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_1834_ = crate::leanh::lean_ctor_get(v___y_1832_, 5);
    v___x_1835_ = 0;
    v___x_1836_ = l_Lean_SourceInfo_fromRef(v_ref_1834_, v___x_1835_);
    v___x_1837_ = l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__1;
    v___x_1838_ = l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__2;
    crate::leanh::lean_inc_n(v___x_1836_, 4);
    v___x_1839_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1839_, 0, v___x_1836_);
    crate::leanh::lean_ctor_set(v___x_1839_, 1, v___x_1838_);
    v___x_1840_ = l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__3;
    v___x_1841_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1841_, 0, v___x_1836_);
    crate::leanh::lean_ctor_set(v___x_1841_, 1, v___x_1840_);
    v___x_1842_ = l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__4;
    v___x_1843_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1843_, 0, v___x_1836_);
    crate::leanh::lean_ctor_set(v___x_1843_, 1, v___x_1842_);
    v___x_1844_ = l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__5;
    v___x_1845_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1845_, 0, v___x_1836_);
    crate::leanh::lean_ctor_set(v___x_1845_, 1, v___x_1844_);
    v___x_1846_ = l_Lean_Syntax_node8(
        v___x_1836_,
        v___x_1837_,
        v___x_1839_,
        v___x_1828_,
        v___x_1841_,
        v___x_1829_,
        v___x_1843_,
        v_pos_1830_,
        v___x_1845_,
        v_neg_1831_,
    );
    v___x_1847_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1847_, 0, v___x_1846_);
    crate::leanh::lean_ctor_set(v___x_1847_, 1, v___y_1833_);
    return v___x_1847_;
}
pub unsafe fn l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___boxed(
    mut v___x_1848_: *mut crate::leanh::LeanObject,
    mut v___x_1849_: *mut crate::leanh::LeanObject,
    mut v_pos_1850_: *mut crate::leanh::LeanObject,
    mut v_neg_1851_: *mut crate::leanh::LeanObject,
    mut v___y_1852_: *mut crate::leanh::LeanObject,
    mut v___y_1853_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1854_ = l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0(v___x_1848_, v___x_1849_, v_pos_1850_, v_neg_1851_, v___y_1852_, v___y_1853_);
    crate::leanh::lean_dec_ref(v___y_1852_);
    return v_res_1854_;
}
pub unsafe fn l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1(
    mut v_x_1861_: *mut crate::leanh::LeanObject,
    mut v_a_1862_: *mut crate::leanh::LeanObject,
    mut v_a_1863_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: u8 = 0;
    let mut v___x_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_methods_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ttk_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_etk_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1896_: u8 = 0;
    let mut v___x_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1900_: u8 = 0;
    let mut v_a_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1905_: u8 = 0;
    let mut v___x_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1909_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1864_ = l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___closed__1;
                crate::leanh::lean_inc(v_x_1861_);
                v___x_1865_ = l_Lean_Syntax_isOfKind(v_x_1861_, v___x_1864_);
                if v___x_1865_ == 0 {
                    crate::leanh::lean_dec(v_x_1861_);
                    v___x_1866_ = crate::leanh::lean_box(1);
                    v___x_1867_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1867_, 0, v___x_1866_);
                    crate::leanh::lean_ctor_set(v___x_1867_, 1, v_a_1863_);
                    return v___x_1867_;
                } else {
                    v_methods_1868_ = crate::leanh::lean_ctor_get(v_a_1862_, 0);
                    v_quotContext_1869_ = crate::leanh::lean_ctor_get(v_a_1862_, 1);
                    v_currMacroScope_1870_ = crate::leanh::lean_ctor_get(v_a_1862_, 2);
                    v_currRecDepth_1871_ = crate::leanh::lean_ctor_get(v_a_1862_, 3);
                    v_maxRecDepth_1872_ = crate::leanh::lean_ctor_get(v_a_1862_, 4);
                    v_ref_1873_ = crate::leanh::lean_ctor_get(v_a_1862_, 5);
                    v___x_1874_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_tk_1875_ = l_Lean_Syntax_getArg(v_x_1861_, v___x_1874_);
                    v___x_1876_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1877_ = l_Lean_Syntax_getArg(v_x_1861_, v___x_1876_);
                    v___x_1878_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_1879_ = l_Lean_Syntax_getArg(v_x_1861_, v___x_1878_);
                    v___f_1880_ = crate::leanh::lean_alloc_closure(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___boxed as *mut core::ffi::c_void, 6, 2);
                    crate::leanh::lean_closure_set(v___f_1880_, 0, v___x_1877_);
                    crate::leanh::lean_closure_set(v___f_1880_, 1, v___x_1879_);
                    v___x_1881_ = crate::leanh::lean_unsigned_to_nat(4);
                    v_ttk_1882_ = l_Lean_Syntax_getArg(v_x_1861_, v___x_1881_);
                    v___x_1883_ = crate::leanh::lean_unsigned_to_nat(5);
                    v___x_1884_ = l_Lean_Syntax_getArg(v_x_1861_, v___x_1883_);
                    v___x_1885_ = crate::leanh::lean_unsigned_to_nat(6);
                    v_etk_1886_ = l_Lean_Syntax_getArg(v_x_1861_, v___x_1885_);
                    v___x_1887_ = crate::leanh::lean_unsigned_to_nat(7);
                    v___x_1888_ = l_Lean_Syntax_getArg(v_x_1861_, v___x_1887_);
                    crate::leanh::lean_dec(v_x_1861_);
                    v_ref_1889_ = l_Lean_replaceRef(v_tk_1875_, v_ref_1873_);
                    crate::leanh::lean_inc(v_maxRecDepth_1872_);
                    crate::leanh::lean_inc(v_currRecDepth_1871_);
                    crate::leanh::lean_inc(v_currMacroScope_1870_);
                    crate::leanh::lean_inc(v_quotContext_1869_);
                    crate::leanh::lean_inc(v_methods_1868_);
                    v___x_1890_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1890_, 0, v_methods_1868_);
                    crate::leanh::lean_ctor_set(v___x_1890_, 1, v_quotContext_1869_);
                    crate::leanh::lean_ctor_set(v___x_1890_, 2, v_currMacroScope_1870_);
                    crate::leanh::lean_ctor_set(v___x_1890_, 3, v_currRecDepth_1871_);
                    crate::leanh::lean_ctor_set(v___x_1890_, 4, v_maxRecDepth_1872_);
                    crate::leanh::lean_ctor_set(v___x_1890_, 5, v_ref_1889_);
                    v___x_1891_ =
                        l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse(
                            v_tk_1875_,
                            v_ttk_1882_,
                            v_etk_1886_,
                            v___x_1884_,
                            v___x_1888_,
                            v___f_1880_,
                            v___x_1890_,
                            v_a_1863_,
                        );
                    crate::leanh::lean_dec_ref_known(v___x_1890_, 6);
                    crate::leanh::lean_dec(v_tk_1875_);
                    if crate::leanh::lean_obj_tag(v___x_1891_) == 0 {
                        v_a_1892_ = crate::leanh::lean_ctor_get(v___x_1891_, 0);
                        v_a_1893_ = crate::leanh::lean_ctor_get(v___x_1891_, 1);
                        v_isSharedCheck_1900_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1891_)) as u8;
                        if v_isSharedCheck_1900_ == 0 {
                            v___x_1895_ = v___x_1891_;
                            v_isShared_1896_ = v_isSharedCheck_1900_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1893_);
                            crate::leanh::lean_inc(v_a_1892_);
                            crate::leanh::lean_dec(v___x_1891_);
                            v___x_1895_ = crate::leanh::lean_box(0);
                            v_isShared_1896_ = v_isSharedCheck_1900_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1901_ = crate::leanh::lean_ctor_get(v___x_1891_, 0);
                        v_a_1902_ = crate::leanh::lean_ctor_get(v___x_1891_, 1);
                        v_isSharedCheck_1909_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1891_)) as u8;
                        if v_isSharedCheck_1909_ == 0 {
                            v___x_1904_ = v___x_1891_;
                            v_isShared_1905_ = v_isSharedCheck_1909_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1902_);
                            crate::leanh::lean_inc(v_a_1901_);
                            crate::leanh::lean_dec(v___x_1891_);
                            v___x_1904_ = crate::leanh::lean_box(0);
                            v_isShared_1905_ = v_isSharedCheck_1909_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1896_ == 0 {
                    v___x_1898_ = v___x_1895_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1899_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1899_, 0, v_a_1892_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1899_, 1, v_a_1893_);
                    v___x_1898_ = v_reuseFailAlloc_1899_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1898_;
            }
            3 => {
                if v_isShared_1905_ == 0 {
                    v___x_1907_ = v___x_1904_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1908_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1908_, 0, v_a_1901_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1908_, 1, v_a_1902_);
                    v___x_1907_ = v_reuseFailAlloc_1908_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1907_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___boxed(
    mut v_x_1910_: *mut crate::leanh::LeanObject,
    mut v_a_1911_: *mut crate::leanh::LeanObject,
    mut v_a_1912_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1913_ = l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1(v_x_1910_, v_a_1911_, v_a_1912_);
    crate::leanh::lean_dec_ref(v_a_1911_);
    return v_res_1913_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1915_ = l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___lam__0___closed__0;
    v___x_1916_ = l_String_toRawSubstring_x27(v___x_1915_);
    return v___x_1916_;
}
pub unsafe fn l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___lam__0(
    mut v___x_1919_: *mut crate::leanh::LeanObject,
    mut v___x_1920_: *mut crate::leanh::LeanObject,
    mut v_pos_1921_: *mut crate::leanh::LeanObject,
    mut v_neg_1922_: *mut crate::leanh::LeanObject,
    mut v___y_1923_: *mut crate::leanh::LeanObject,
    mut v___y_1924_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_quotContext_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: u8 = 0;
    let mut v___x_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_quotContext_1925_ = crate::leanh::lean_ctor_get(v___y_1923_, 1);
    v_currMacroScope_1926_ = crate::leanh::lean_ctor_get(v___y_1923_, 2);
    v_ref_1927_ = crate::leanh::lean_ctor_get(v___y_1923_, 5);
    v___x_1928_ = 0;
    v___x_1929_ = l_Lean_SourceInfo_fromRef(v_ref_1927_, v___x_1928_);
    v___x_1930_ = l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__1;
    v___x_1931_ = l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__2;
    crate::leanh::lean_inc_n(v___x_1929_, 6);
    v___x_1932_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1932_, 0, v___x_1929_);
    crate::leanh::lean_ctor_set(v___x_1932_, 1, v___x_1931_);
    v___x_1933_ =
        l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__28;
    v___x_1934_ = l_Lean_Name_mkStr2(v___x_1919_, v___x_1933_);
    v___x_1935_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___lam__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___lam__0___closed__1_once), _init_l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___lam__0___closed__1);
    v___x_1936_ = l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___lam__0___closed__2;
    crate::leanh::lean_inc(v_currMacroScope_1926_);
    crate::leanh::lean_inc(v_quotContext_1925_);
    v___x_1937_ = l_Lean_addMacroScope(v_quotContext_1925_, v___x_1936_, v_currMacroScope_1926_);
    v___x_1938_ = crate::leanh::lean_box(0);
    v___x_1939_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1939_, 0, v___x_1929_);
    crate::leanh::lean_ctor_set(v___x_1939_, 1, v___x_1935_);
    crate::leanh::lean_ctor_set(v___x_1939_, 2, v___x_1937_);
    crate::leanh::lean_ctor_set(v___x_1939_, 3, v___x_1938_);
    v___x_1940_ = l_Lean_Syntax_node1(v___x_1929_, v___x_1934_, v___x_1939_);
    v___x_1941_ = l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__3;
    v___x_1942_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1942_, 0, v___x_1929_);
    crate::leanh::lean_ctor_set(v___x_1942_, 1, v___x_1941_);
    v___x_1943_ = l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__4;
    v___x_1944_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1944_, 0, v___x_1929_);
    crate::leanh::lean_ctor_set(v___x_1944_, 1, v___x_1943_);
    v___x_1945_ = l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__5;
    v___x_1946_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1946_, 0, v___x_1929_);
    crate::leanh::lean_ctor_set(v___x_1946_, 1, v___x_1945_);
    v___x_1947_ = l_Lean_Syntax_node8(
        v___x_1929_,
        v___x_1930_,
        v___x_1932_,
        v___x_1940_,
        v___x_1942_,
        v___x_1920_,
        v___x_1944_,
        v_pos_1921_,
        v___x_1946_,
        v_neg_1922_,
    );
    v___x_1948_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1948_, 0, v___x_1947_);
    crate::leanh::lean_ctor_set(v___x_1948_, 1, v___y_1924_);
    return v___x_1948_;
}
pub unsafe fn l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___lam__0___boxed(
    mut v___x_1949_: *mut crate::leanh::LeanObject,
    mut v___x_1950_: *mut crate::leanh::LeanObject,
    mut v_pos_1951_: *mut crate::leanh::LeanObject,
    mut v_neg_1952_: *mut crate::leanh::LeanObject,
    mut v___y_1953_: *mut crate::leanh::LeanObject,
    mut v___y_1954_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1955_ = l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___lam__0(v___x_1949_, v___x_1950_, v_pos_1951_, v_neg_1952_, v___y_1953_, v___y_1954_);
    crate::leanh::lean_dec_ref(v___y_1953_);
    return v_res_1955_;
}
pub unsafe fn l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1(
    mut v_x_1962_: *mut crate::leanh::LeanObject,
    mut v_a_1963_: *mut crate::leanh::LeanObject,
    mut v_a_1964_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: u8 = 0;
    let mut v___x_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_methods_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ttk_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_etk_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1996_: u8 = 0;
    let mut v___x_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2000_: u8 = 0;
    let mut v_a_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2005_: u8 = 0;
    let mut v___x_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2009_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1965_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0;
                v___x_1966_ = l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___closed__1;
                crate::leanh::lean_inc(v_x_1962_);
                v___x_1967_ = l_Lean_Syntax_isOfKind(v_x_1962_, v___x_1966_);
                if v___x_1967_ == 0 {
                    crate::leanh::lean_dec(v_x_1962_);
                    v___x_1968_ = crate::leanh::lean_box(1);
                    v___x_1969_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1969_, 0, v___x_1968_);
                    crate::leanh::lean_ctor_set(v___x_1969_, 1, v_a_1964_);
                    return v___x_1969_;
                } else {
                    v_methods_1970_ = crate::leanh::lean_ctor_get(v_a_1963_, 0);
                    v_quotContext_1971_ = crate::leanh::lean_ctor_get(v_a_1963_, 1);
                    v_currMacroScope_1972_ = crate::leanh::lean_ctor_get(v_a_1963_, 2);
                    v_currRecDepth_1973_ = crate::leanh::lean_ctor_get(v_a_1963_, 3);
                    v_maxRecDepth_1974_ = crate::leanh::lean_ctor_get(v_a_1963_, 4);
                    v_ref_1975_ = crate::leanh::lean_ctor_get(v_a_1963_, 5);
                    v___x_1976_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_tk_1977_ = l_Lean_Syntax_getArg(v_x_1962_, v___x_1976_);
                    v___x_1978_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1979_ = l_Lean_Syntax_getArg(v_x_1962_, v___x_1978_);
                    v___f_1980_ = crate::leanh::lean_alloc_closure(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___lam__0___boxed as *mut core::ffi::c_void, 6, 2);
                    crate::leanh::lean_closure_set(v___f_1980_, 0, v___x_1965_);
                    crate::leanh::lean_closure_set(v___f_1980_, 1, v___x_1979_);
                    v___x_1981_ = crate::leanh::lean_unsigned_to_nat(2);
                    v_ttk_1982_ = l_Lean_Syntax_getArg(v_x_1962_, v___x_1981_);
                    v___x_1983_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_1984_ = l_Lean_Syntax_getArg(v_x_1962_, v___x_1983_);
                    v___x_1985_ = crate::leanh::lean_unsigned_to_nat(4);
                    v_etk_1986_ = l_Lean_Syntax_getArg(v_x_1962_, v___x_1985_);
                    v___x_1987_ = crate::leanh::lean_unsigned_to_nat(5);
                    v___x_1988_ = l_Lean_Syntax_getArg(v_x_1962_, v___x_1987_);
                    crate::leanh::lean_dec(v_x_1962_);
                    v_ref_1989_ = l_Lean_replaceRef(v_tk_1977_, v_ref_1975_);
                    crate::leanh::lean_inc(v_maxRecDepth_1974_);
                    crate::leanh::lean_inc(v_currRecDepth_1973_);
                    crate::leanh::lean_inc(v_currMacroScope_1972_);
                    crate::leanh::lean_inc(v_quotContext_1971_);
                    crate::leanh::lean_inc(v_methods_1970_);
                    v___x_1990_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1990_, 0, v_methods_1970_);
                    crate::leanh::lean_ctor_set(v___x_1990_, 1, v_quotContext_1971_);
                    crate::leanh::lean_ctor_set(v___x_1990_, 2, v_currMacroScope_1972_);
                    crate::leanh::lean_ctor_set(v___x_1990_, 3, v_currRecDepth_1973_);
                    crate::leanh::lean_ctor_set(v___x_1990_, 4, v_maxRecDepth_1974_);
                    crate::leanh::lean_ctor_set(v___x_1990_, 5, v_ref_1989_);
                    v___x_1991_ =
                        l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse(
                            v_tk_1977_,
                            v_ttk_1982_,
                            v_etk_1986_,
                            v___x_1984_,
                            v___x_1988_,
                            v___f_1980_,
                            v___x_1990_,
                            v_a_1964_,
                        );
                    crate::leanh::lean_dec_ref_known(v___x_1990_, 6);
                    crate::leanh::lean_dec(v_tk_1977_);
                    if crate::leanh::lean_obj_tag(v___x_1991_) == 0 {
                        v_a_1992_ = crate::leanh::lean_ctor_get(v___x_1991_, 0);
                        v_a_1993_ = crate::leanh::lean_ctor_get(v___x_1991_, 1);
                        v_isSharedCheck_2000_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1991_)) as u8;
                        if v_isSharedCheck_2000_ == 0 {
                            v___x_1995_ = v___x_1991_;
                            v_isShared_1996_ = v_isSharedCheck_2000_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1993_);
                            crate::leanh::lean_inc(v_a_1992_);
                            crate::leanh::lean_dec(v___x_1991_);
                            v___x_1995_ = crate::leanh::lean_box(0);
                            v_isShared_1996_ = v_isSharedCheck_2000_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2001_ = crate::leanh::lean_ctor_get(v___x_1991_, 0);
                        v_a_2002_ = crate::leanh::lean_ctor_get(v___x_1991_, 1);
                        v_isSharedCheck_2009_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1991_)) as u8;
                        if v_isSharedCheck_2009_ == 0 {
                            v___x_2004_ = v___x_1991_;
                            v_isShared_2005_ = v_isSharedCheck_2009_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2002_);
                            crate::leanh::lean_inc(v_a_2001_);
                            crate::leanh::lean_dec(v___x_1991_);
                            v___x_2004_ = crate::leanh::lean_box(0);
                            v_isShared_2005_ = v_isSharedCheck_2009_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1996_ == 0 {
                    v___x_1998_ = v___x_1995_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1999_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1999_, 0, v_a_1992_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1999_, 1, v_a_1993_);
                    v___x_1998_ = v_reuseFailAlloc_1999_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1998_;
            }
            3 => {
                if v_isShared_2005_ == 0 {
                    v___x_2007_ = v___x_2004_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2008_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_a_2001_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2008_, 1, v_a_2002_);
                    v___x_2007_ = v_reuseFailAlloc_2008_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2007_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___boxed(
    mut v_x_2010_: *mut crate::leanh::LeanObject,
    mut v_a_2011_: *mut crate::leanh::LeanObject,
    mut v_a_2012_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2013_ = l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1(v_x_2010_, v_a_2011_, v_a_2012_);
    crate::leanh::lean_dec_ref(v_a_2011_);
    return v_res_2013_;
}
pub unsafe fn l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1(
    mut v_x_2081_: *mut crate::leanh::LeanObject,
    mut v_a_2082_: *mut crate::leanh::LeanObject,
    mut v_a_2083_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: u8 = 0;
    v___x_2084_ = l_Lean_Parser_Tactic_tacticIterate_________00__closed__1;
    crate::leanh::lean_inc(v_x_2081_);
    v___x_2085_ = l_Lean_Syntax_isOfKind(v_x_2081_, v___x_2084_);
    if v___x_2085_ == 0 {
        let mut v___x_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_2081_);
        v___x_2086_ = crate::leanh::lean_box(1);
        v___x_2087_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2087_, 0, v___x_2086_);
        crate::leanh::lean_ctor_set(v___x_2087_, 1, v_a_2083_);
        return v___x_2087_;
    } else {
        let mut v___x_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2091_: u8 = 0;
        v___x_2088_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_2089_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_2090_ = l_Lean_Syntax_getArg(v_x_2081_, v___x_2089_);
        crate::leanh::lean_inc(v___x_2090_);
        v___x_2091_ = l_Lean_Syntax_matchesNull(v___x_2090_, v___x_2088_);
        if v___x_2091_ == 0 {
            let mut v___x_2092_: u8 = 0;
            crate::leanh::lean_inc(v___x_2090_);
            v___x_2092_ = l_Lean_Syntax_matchesNull(v___x_2090_, v___x_2089_);
            if v___x_2092_ == 0 {
                let mut v___x_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v___x_2090_);
                crate::leanh::lean_dec(v_x_2081_);
                v___x_2093_ = crate::leanh::lean_box(1);
                v___x_2094_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2094_, 0, v___x_2093_);
                crate::leanh::lean_ctor_set(v___x_2094_, 1, v_a_2083_);
                return v___x_2094_;
            } else {
                let mut v___x_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2098_: u8 = 0;
                v___x_2095_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_2096_ = l_Lean_Syntax_getArg(v_x_2081_, v___x_2095_);
                crate::leanh::lean_dec(v_x_2081_);
                v___x_2097_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__9;
                crate::leanh::lean_inc(v___x_2096_);
                v___x_2098_ = l_Lean_Syntax_isOfKind(v___x_2096_, v___x_2097_);
                if v___x_2098_ == 0 {
                    let mut v___x_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v___x_2096_);
                    crate::leanh::lean_dec(v___x_2090_);
                    v___x_2099_ = crate::leanh::lean_box(1);
                    v___x_2100_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2100_, 0, v___x_2099_);
                    crate::leanh::lean_ctor_set(v___x_2100_, 1, v_a_2083_);
                    return v___x_2100_;
                } else {
                    let mut v___x_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_2102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_isZero_2103_: u8 = 0;
                    v___x_2101_ = l_Lean_Syntax_getArg(v___x_2090_, v___x_2088_);
                    crate::leanh::lean_dec(v___x_2090_);
                    v___x_2102_ = l_Lean_Syntax_toNat(v___x_2101_);
                    crate::leanh::lean_dec(v___x_2101_);
                    v_isZero_2103_ = lean_nat_dec_eq(v___x_2102_, v___x_2088_);
                    if v_isZero_2103_ == 1 {
                        let mut v_ref_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_2107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        crate::leanh::lean_dec(v___x_2102_);
                        crate::leanh::lean_dec(v___x_2096_);
                        v_ref_2104_ = crate::leanh::lean_ctor_get(v_a_2082_, 5);
                        v___x_2105_ = l_Lean_SourceInfo_fromRef(v_ref_2104_, v___x_2091_);
                        v___x_2106_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__17;
                        v___x_2107_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__18;
                        crate::leanh::lean_inc(v___x_2105_);
                        v___x_2108_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2108_, 0, v___x_2105_);
                        crate::leanh::lean_ctor_set(v___x_2108_, 1, v___x_2106_);
                        v___x_2109_ = l_Lean_Syntax_node1(v___x_2105_, v___x_2107_, v___x_2108_);
                        v___x_2110_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2110_, 0, v___x_2109_);
                        crate::leanh::lean_ctor_set(v___x_2110_, 1, v_a_2083_);
                        return v___x_2110_;
                    } else {
                        let mut v_ref_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v_n_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_2124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v_ref_2111_ = crate::leanh::lean_ctor_get(v_a_2082_, 5);
                        v_n_2112_ = lean_nat_sub(v___x_2102_, v___x_2089_);
                        crate::leanh::lean_dec(v___x_2102_);
                        v___x_2113_ = l_Lean_SourceInfo_fromRef(v_ref_2111_, v___x_2091_);
                        v___x_2114_ = l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1___closed__1;
                        v___x_2115_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__13;
                        v___x_2116_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__21;
                        v___x_2117_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__22;
                        crate::leanh::lean_inc_n(v___x_2113_, 8);
                        v___x_2118_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2118_, 0, v___x_2113_);
                        crate::leanh::lean_ctor_set(v___x_2118_, 1, v___x_2117_);
                        v___x_2119_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__23;
                        v___x_2120_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2120_, 0, v___x_2113_);
                        crate::leanh::lean_ctor_set(v___x_2120_, 1, v___x_2119_);
                        crate::leanh::lean_inc(v___x_2096_);
                        v___x_2121_ = l_Lean_Syntax_node3(
                            v___x_2113_,
                            v___x_2116_,
                            v___x_2118_,
                            v___x_2096_,
                            v___x_2120_,
                        );
                        v___x_2122_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__17;
                        v___x_2123_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2123_, 0, v___x_2113_);
                        crate::leanh::lean_ctor_set(v___x_2123_, 1, v___x_2122_);
                        v___x_2124_ = l_Lean_Parser_Tactic_tacticIterate_________00__closed__4;
                        v___x_2125_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2125_, 0, v___x_2113_);
                        crate::leanh::lean_ctor_set(v___x_2125_, 1, v___x_2124_);
                        v___x_2126_ = l_Nat_reprFast(v_n_2112_);
                        v___x_2127_ = crate::leanh::lean_box(2);
                        v___x_2128_ = l_Lean_Syntax_mkNumLit(v___x_2126_, v___x_2127_);
                        v___x_2129_ = l_Lean_Syntax_node1(v___x_2113_, v___x_2115_, v___x_2128_);
                        v___x_2130_ = l_Lean_Syntax_node3(
                            v___x_2113_,
                            v___x_2084_,
                            v___x_2125_,
                            v___x_2129_,
                            v___x_2096_,
                        );
                        v___x_2131_ = l_Lean_Syntax_node3(
                            v___x_2113_,
                            v___x_2115_,
                            v___x_2121_,
                            v___x_2123_,
                            v___x_2130_,
                        );
                        v___x_2132_ = l_Lean_Syntax_node1(v___x_2113_, v___x_2114_, v___x_2131_);
                        v___x_2133_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2133_, 0, v___x_2132_);
                        crate::leanh::lean_ctor_set(v___x_2133_, 1, v_a_2083_);
                        return v___x_2133_;
                    }
                }
            }
        } else {
            let mut v___x_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2137_: u8 = 0;
            crate::leanh::lean_dec(v___x_2090_);
            v___x_2134_ = crate::leanh::lean_unsigned_to_nat(2);
            v___x_2135_ = l_Lean_Syntax_getArg(v_x_2081_, v___x_2134_);
            crate::leanh::lean_dec(v_x_2081_);
            v___x_2136_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__9;
            crate::leanh::lean_inc(v___x_2135_);
            v___x_2137_ = l_Lean_Syntax_isOfKind(v___x_2135_, v___x_2136_);
            if v___x_2137_ == 0 {
                let mut v___x_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v___x_2135_);
                v___x_2138_ = crate::leanh::lean_box(1);
                v___x_2139_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2139_, 0, v___x_2138_);
                crate::leanh::lean_ctor_set(v___x_2139_, 1, v_a_2083_);
                return v___x_2139_;
            } else {
                let mut v_ref_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2141_: u8 = 0;
                let mut v___x_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_ref_2140_ = crate::leanh::lean_ctor_get(v_a_2082_, 5);
                v___x_2141_ = 0;
                v___x_2142_ = l_Lean_SourceInfo_fromRef(v_ref_2140_, v___x_2141_);
                v___x_2143_ = l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1___closed__3;
                v___x_2144_ = l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1___closed__4;
                crate::leanh::lean_inc_n(v___x_2142_, 11);
                v___x_2145_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2145_, 0, v___x_2142_);
                crate::leanh::lean_ctor_set(v___x_2145_, 1, v___x_2144_);
                v___x_2146_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__11;
                v___x_2147_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__13;
                v___x_2148_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__21;
                v___x_2149_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__22;
                v___x_2150_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2150_, 0, v___x_2142_);
                crate::leanh::lean_ctor_set(v___x_2150_, 1, v___x_2149_);
                v___x_2151_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__23;
                v___x_2152_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2152_, 0, v___x_2142_);
                crate::leanh::lean_ctor_set(v___x_2152_, 1, v___x_2151_);
                crate::leanh::lean_inc(v___x_2135_);
                v___x_2153_ = l_Lean_Syntax_node3(
                    v___x_2142_,
                    v___x_2148_,
                    v___x_2150_,
                    v___x_2135_,
                    v___x_2152_,
                );
                v___x_2154_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__17;
                v___x_2155_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2155_, 0, v___x_2142_);
                crate::leanh::lean_ctor_set(v___x_2155_, 1, v___x_2154_);
                v___x_2156_ = l_Lean_Parser_Tactic_tacticIterate_________00__closed__4;
                v___x_2157_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2157_, 0, v___x_2142_);
                crate::leanh::lean_ctor_set(v___x_2157_, 1, v___x_2156_);
                v___x_2158_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__19), core::ptr::addr_of_mut!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__19_once), _init_l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__19);
                v___x_2159_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2159_, 0, v___x_2142_);
                crate::leanh::lean_ctor_set(v___x_2159_, 1, v___x_2147_);
                crate::leanh::lean_ctor_set(v___x_2159_, 2, v___x_2158_);
                v___x_2160_ = l_Lean_Syntax_node3(
                    v___x_2142_,
                    v___x_2084_,
                    v___x_2157_,
                    v___x_2159_,
                    v___x_2135_,
                );
                v___x_2161_ = l_Lean_Syntax_node3(
                    v___x_2142_,
                    v___x_2147_,
                    v___x_2153_,
                    v___x_2155_,
                    v___x_2160_,
                );
                v___x_2162_ = l_Lean_Syntax_node1(v___x_2142_, v___x_2146_, v___x_2161_);
                v___x_2163_ = l_Lean_Syntax_node1(v___x_2142_, v___x_2136_, v___x_2162_);
                v___x_2164_ =
                    l_Lean_Syntax_node2(v___x_2142_, v___x_2143_, v___x_2145_, v___x_2163_);
                v___x_2165_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2165_, 0, v___x_2164_);
                crate::leanh::lean_ctor_set(v___x_2165_, 1, v_a_2083_);
                return v___x_2165_;
            }
        }
    }
}
pub unsafe fn l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1___boxed(
    mut v_x_2166_: *mut crate::leanh::LeanObject,
    mut v_a_2167_: *mut crate::leanh::LeanObject,
    mut v_a_2168_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2169_ = l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1(v_x_2166_, v_a_2167_, v_a_2168_);
    crate::leanh::lean_dec_ref(v_a_2167_);
    return v_res_2169_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2180_ = l_Lean_Parser_Tactic_optConfig;
    v___x_2181_ = l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__3;
    v___x_2182_ = l_Lean_Parser_Tactic_tacticIterate_________00__closed__3;
    v___x_2183_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2183_, 0, v___x_2182_);
    crate::leanh::lean_ctor_set(v___x_2183_, 1, v___x_2181_);
    crate::leanh::lean_ctor_set(v___x_2183_, 2, v___x_2180_);
    return v___x_2183_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2184_ = l_Lean_Parser_Tactic_rwRuleSeq;
    v___x_2185_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__4_once),
        _init_l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__4,
    );
    v___x_2186_ = l_Lean_Parser_Tactic_tacticIterate_________00__closed__3;
    v___x_2187_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2187_, 0, v___x_2186_);
    crate::leanh::lean_ctor_set(v___x_2187_, 1, v___x_2185_);
    crate::leanh::lean_ctor_set(v___x_2187_, 2, v___x_2184_);
    return v___x_2187_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2188_ = l_Lean_Parser_Tactic_location;
    v___x_2189_ = l_Lean_Parser_Tactic_tacticIterate_________00__closed__7;
    v___x_2190_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2190_, 0, v___x_2189_);
    crate::leanh::lean_ctor_set(v___x_2190_, 1, v___x_2188_);
    return v___x_2190_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2191_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__6_once),
        _init_l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__6,
    );
    v___x_2192_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__5_once),
        _init_l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__5,
    );
    v___x_2193_ = l_Lean_Parser_Tactic_tacticIterate_________00__closed__3;
    v___x_2194_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2194_, 0, v___x_2193_);
    crate::leanh::lean_ctor_set(v___x_2194_, 1, v___x_2192_);
    crate::leanh::lean_ctor_set(v___x_2194_, 2, v___x_2191_);
    return v___x_2194_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2195_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__7_once),
        _init_l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__7,
    );
    v___x_2196_ = crate::leanh::lean_unsigned_to_nat(1022);
    v___x_2197_ = l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__1;
    v___x_2198_ = crate::leanh::lean_alloc_ctor(3, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2198_, 0, v___x_2197_);
    crate::leanh::lean_ctor_set(v___x_2198_, 1, v___x_2196_);
    crate::leanh::lean_ctor_set(v___x_2198_, 2, v___x_2195_);
    return v___x_2198_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_tacticRw__mod__cast______() -> *mut crate::leanh::LeanObject
{
    let mut v___x_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2199_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__8_once),
        _init_l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__8,
    );
    return v___x_2199_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0(
    mut v___x_2242_: *mut crate::leanh::LeanObject,
    mut v_loc_2243_: *mut crate::leanh::LeanObject,
    mut v_sz_2244_: usize,
    mut v_i_2245_: usize,
    mut v_bs_2246_: *mut crate::leanh::LeanObject,
    mut v___y_2247_: *mut crate::leanh::LeanObject,
    mut v___y_2248_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2249_: u8 = 0;
    let mut v___x_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: u8 = 0;
    let mut v___x_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: usize = 0;
    let mut v___x_2304_: usize = 0;
    let mut v___x_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2249_ = lean_usize_dec_lt(v_i_2245_, v_sz_2244_);
                if v___x_2249_ == 0 {
                    crate::leanh::lean_dec(v_loc_2243_);
                    crate::leanh::lean_dec(v___x_2242_);
                    v___x_2250_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2250_, 0, v_bs_2246_);
                    crate::leanh::lean_ctor_set(v___x_2250_, 1, v___y_2248_);
                    return v___x_2250_;
                } else {
                    v_ref_2251_ = crate::leanh::lean_ctor_get(v___y_2247_, 5);
                    v___x_2252_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__1;
                    v_v_2253_ = lean_array_uget(v_bs_2246_, v_i_2245_);
                    v___x_2254_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__3;
                    v___x_2255_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_2256_ = lean_array_uset(v_bs_2246_, v_i_2245_, v___x_2255_);
                    v___x_2257_ = 0;
                    v___x_2258_ = l_Lean_SourceInfo_fromRef(v_ref_2251_, v___x_2257_);
                    v___x_2259_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__21;
                    v___x_2260_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__22;
                    crate::leanh::lean_inc_n(v___x_2258_, 16);
                    v___x_2261_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2261_, 0, v___x_2258_);
                    crate::leanh::lean_ctor_set(v___x_2261_, 1, v___x_2260_);
                    v___x_2262_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__9;
                    v___x_2263_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__11;
                    v___x_2264_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__13;
                    v___x_2265_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__5;
                    v___x_2266_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__6;
                    v___x_2267_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2267_, 0, v___x_2258_);
                    crate::leanh::lean_ctor_set(v___x_2267_, 1, v___x_2266_);
                    v___x_2268_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__19), core::ptr::addr_of_mut!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__19_once), _init_l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__19);
                    v___x_2269_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2269_, 0, v___x_2258_);
                    crate::leanh::lean_ctor_set(v___x_2269_, 1, v___x_2264_);
                    crate::leanh::lean_ctor_set(v___x_2269_, 2, v___x_2268_);
                    v___x_2270_ = l_Lean_Syntax_node1(v___x_2258_, v___x_2252_, v___x_2269_);
                    v___x_2271_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__8;
                    v___x_2272_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__9;
                    v___x_2273_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2273_, 0, v___x_2258_);
                    crate::leanh::lean_ctor_set(v___x_2273_, 1, v___x_2272_);
                    v___x_2274_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__11;
                    v___x_2275_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__12;
                    v___x_2276_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2276_, 0, v___x_2258_);
                    crate::leanh::lean_ctor_set(v___x_2276_, 1, v___x_2275_);
                    v___x_2277_ = l_Lean_Syntax_node1(v___x_2258_, v___x_2274_, v___x_2276_);
                    v___x_2278_ =
                        l_Lean_Syntax_node2(v___x_2258_, v___x_2271_, v___x_2273_, v___x_2277_);
                    v___x_2279_ = l_Lean_Syntax_node1(v___x_2258_, v___x_2264_, v___x_2278_);
                    v___x_2280_ = l_Lean_Syntax_node3(
                        v___x_2258_,
                        v___x_2265_,
                        v___x_2267_,
                        v___x_2270_,
                        v___x_2279_,
                    );
                    v___x_2281_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__17;
                    v___x_2282_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2282_, 0, v___x_2258_);
                    crate::leanh::lean_ctor_set(v___x_2282_, 1, v___x_2281_);
                    v___x_2283_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__14;
                    v___x_2284_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__15;
                    v___x_2285_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2285_, 0, v___x_2258_);
                    crate::leanh::lean_ctor_set(v___x_2285_, 1, v___x_2284_);
                    v___x_2286_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__16;
                    v___x_2287_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2287_, 0, v___x_2258_);
                    crate::leanh::lean_ctor_set(v___x_2287_, 1, v___x_2286_);
                    v___x_2288_ = l_Lean_Syntax_node1(v___x_2258_, v___x_2264_, v_v_2253_);
                    v___x_2289_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__17;
                    v___x_2290_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2290_, 0, v___x_2258_);
                    crate::leanh::lean_ctor_set(v___x_2290_, 1, v___x_2289_);
                    v___x_2291_ = l_Lean_Syntax_node3(
                        v___x_2258_,
                        v___x_2254_,
                        v___x_2287_,
                        v___x_2288_,
                        v___x_2290_,
                    );
                    if crate::leanh::lean_obj_tag(v_loc_2243_) == 1 {
                        v_val_2307_ = crate::leanh::lean_ctor_get(v_loc_2243_, 0);
                        crate::leanh::lean_inc(v_val_2307_);
                        v___x_2308_ = l_Array_mkArray1___redArg(v_val_2307_);
                        v___y_2293_ = v___x_2308_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2309_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__18;
                        v___y_2293_ = v___x_2309_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2294_ = l_Array_append___redArg(v___x_2268_, v___y_2293_);
                crate::leanh::lean_dec_ref(v___y_2293_);
                crate::leanh::lean_inc_n(v___x_2258_, 6);
                v___x_2295_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2295_, 0, v___x_2258_);
                crate::leanh::lean_ctor_set(v___x_2295_, 1, v___x_2264_);
                crate::leanh::lean_ctor_set(v___x_2295_, 2, v___x_2294_);
                crate::leanh::lean_inc(v___x_2242_);
                v___x_2296_ = l_Lean_Syntax_node4(
                    v___x_2258_,
                    v___x_2283_,
                    v___x_2285_,
                    v___x_2242_,
                    v___x_2291_,
                    v___x_2295_,
                );
                v___x_2297_ = l_Lean_Syntax_node3(
                    v___x_2258_,
                    v___x_2264_,
                    v___x_2280_,
                    v___x_2282_,
                    v___x_2296_,
                );
                v___x_2298_ = l_Lean_Syntax_node1(v___x_2258_, v___x_2263_, v___x_2297_);
                v___x_2299_ = l_Lean_Syntax_node1(v___x_2258_, v___x_2262_, v___x_2298_);
                v___x_2300_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__23;
                v___x_2301_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2301_, 0, v___x_2258_);
                crate::leanh::lean_ctor_set(v___x_2301_, 1, v___x_2300_);
                v___x_2302_ = l_Lean_Syntax_node3(
                    v___x_2258_,
                    v___x_2259_,
                    v___x_2261_,
                    v___x_2299_,
                    v___x_2301_,
                );
                v___x_2303_ = 1usize;
                v___x_2304_ = lean_usize_add(v_i_2245_, v___x_2303_);
                v___x_2305_ = lean_array_uset(v_bs_x27_2256_, v_i_2245_, v___x_2302_);
                v_i_2245_ = v___x_2304_;
                v_bs_2246_ = v___x_2305_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___boxed(
    mut v___x_2310_: *mut crate::leanh::LeanObject,
    mut v_loc_2311_: *mut crate::leanh::LeanObject,
    mut v_sz_2312_: *mut crate::leanh::LeanObject,
    mut v_i_2313_: *mut crate::leanh::LeanObject,
    mut v_bs_2314_: *mut crate::leanh::LeanObject,
    mut v___y_2315_: *mut crate::leanh::LeanObject,
    mut v___y_2316_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2317_: usize = 0;
    let mut v_i_boxed_2318_: usize = 0;
    let mut v_res_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2317_ = crate::leanh::lean_unbox_usize(v_sz_2312_);
    crate::leanh::lean_dec(v_sz_2312_);
    v_i_boxed_2318_ = crate::leanh::lean_unbox_usize(v_i_2313_);
    crate::leanh::lean_dec(v_i_2313_);
    v_res_2319_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0(v___x_2310_, v_loc_2311_, v_sz_boxed_2317_, v_i_boxed_2318_, v_bs_2314_, v___y_2315_, v___y_2316_);
    crate::leanh::lean_dec_ref(v___y_2315_);
    return v_res_2319_;
}
pub unsafe fn l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1(
    mut v_x_2320_: *mut crate::leanh::LeanObject,
    mut v_a_2321_: *mut crate::leanh::LeanObject,
    mut v_a_2322_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: u8 = 0;
    let mut v___x_2325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: u8 = 0;
    let mut v___x_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: u8 = 0;
    let mut v___x_2337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_loc_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rules_2344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2346_: usize = 0;
    let mut v___x_2347_: usize = 0;
    let mut v___x_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2353_: u8 = 0;
    let mut v_ref_2354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: u8 = 0;
    let mut v___x_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2364_: usize = 0;
    let mut v___x_2365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2378_: u8 = 0;
    let mut v_a_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2383_: u8 = 0;
    let mut v___x_2385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2387_: u8 = 0;
    let mut v___x_2388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: u8 = 0;
    let mut v___x_2391_: u8 = 0;
    let mut v___x_2392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_loc_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2323_ = l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__1;
                crate::leanh::lean_inc(v_x_2320_);
                v___x_2324_ = l_Lean_Syntax_isOfKind(v_x_2320_, v___x_2323_);
                if v___x_2324_ == 0 {
                    crate::leanh::lean_dec(v_x_2320_);
                    v___x_2325_ = crate::leanh::lean_box(1);
                    v___x_2326_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2326_, 0, v___x_2325_);
                    crate::leanh::lean_ctor_set(v___x_2326_, 1, v_a_2322_);
                    return v___x_2326_;
                } else {
                    v___x_2327_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2328_ = l_Lean_Syntax_getArg(v_x_2320_, v___x_2327_);
                    v___x_2329_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__1;
                    crate::leanh::lean_inc(v___x_2328_);
                    v___x_2330_ = l_Lean_Syntax_isOfKind(v___x_2328_, v___x_2329_);
                    if v___x_2330_ == 0 {
                        crate::leanh::lean_dec(v___x_2328_);
                        crate::leanh::lean_dec(v_x_2320_);
                        v___x_2331_ = crate::leanh::lean_box(1);
                        v___x_2332_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2332_, 0, v___x_2331_);
                        crate::leanh::lean_ctor_set(v___x_2332_, 1, v_a_2322_);
                        return v___x_2332_;
                    } else {
                        v___x_2333_ = crate::leanh::lean_unsigned_to_nat(2);
                        v___x_2334_ = l_Lean_Syntax_getArg(v_x_2320_, v___x_2333_);
                        v___x_2335_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__3;
                        crate::leanh::lean_inc(v___x_2334_);
                        v___x_2336_ = l_Lean_Syntax_isOfKind(v___x_2334_, v___x_2335_);
                        if v___x_2336_ == 0 {
                            crate::leanh::lean_dec(v___x_2334_);
                            crate::leanh::lean_dec(v___x_2328_);
                            crate::leanh::lean_dec(v_x_2320_);
                            v___x_2337_ = crate::leanh::lean_box(1);
                            v___x_2338_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2338_, 0, v___x_2337_);
                            crate::leanh::lean_ctor_set(v___x_2338_, 1, v_a_2322_);
                            return v___x_2338_;
                        } else {
                            v___x_2339_ = l_Lean_Syntax_getArg(v___x_2334_, v___x_2327_);
                            crate::leanh::lean_dec(v___x_2334_);
                            v___x_2388_ = crate::leanh::lean_unsigned_to_nat(3);
                            v___x_2389_ = l_Lean_Syntax_getArg(v_x_2320_, v___x_2388_);
                            crate::leanh::lean_dec(v_x_2320_);
                            v___x_2390_ = l_Lean_Syntax_isNone(v___x_2389_);
                            if v___x_2390_ == 0 {
                                crate::leanh::lean_inc(v___x_2389_);
                                v___x_2391_ = l_Lean_Syntax_matchesNull(v___x_2389_, v___x_2327_);
                                if v___x_2391_ == 0 {
                                    crate::leanh::lean_dec(v___x_2389_);
                                    crate::leanh::lean_dec(v___x_2339_);
                                    crate::leanh::lean_dec(v___x_2328_);
                                    v___x_2392_ = crate::leanh::lean_box(1);
                                    v___x_2393_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_2393_, 0, v___x_2392_);
                                    crate::leanh::lean_ctor_set(v___x_2393_, 1, v_a_2322_);
                                    return v___x_2393_;
                                } else {
                                    v___x_2394_ = crate::leanh::lean_unsigned_to_nat(0);
                                    v_loc_2395_ = l_Lean_Syntax_getArg(v___x_2389_, v___x_2394_);
                                    crate::leanh::lean_dec(v___x_2389_);
                                    v___x_2396_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_2396_, 0, v_loc_2395_);
                                    v_loc_2341_ = v___x_2396_;
                                    v___y_2342_ = v_a_2321_;
                                    v___y_2343_ = v_a_2322_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v___x_2389_);
                                v___x_2397_ = crate::leanh::lean_box(0);
                                v_loc_2341_ = v___x_2397_;
                                v___y_2342_ = v_a_2321_;
                                v___y_2343_ = v_a_2322_;
                                state = 1;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v_rules_2344_ = l_Lean_Syntax_getArgs(v___x_2339_);
                crate::leanh::lean_dec(v___x_2339_);
                v___x_2345_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_rules_2344_);
                crate::leanh::lean_dec_ref(v_rules_2344_);
                v_sz_2346_ = lean_array_size(v___x_2345_);
                v___x_2347_ = 0usize;
                v___x_2348_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0(v___x_2328_, v_loc_2341_, v_sz_2346_, v___x_2347_, v___x_2345_, v___y_2342_, v___y_2343_);
                if crate::leanh::lean_obj_tag(v___x_2348_) == 0 {
                    v_a_2349_ = crate::leanh::lean_ctor_get(v___x_2348_, 0);
                    v_a_2350_ = crate::leanh::lean_ctor_get(v___x_2348_, 1);
                    v_isSharedCheck_2378_ = (!crate::leanh::lean_is_exclusive(v___x_2348_)) as u8;
                    if v_isSharedCheck_2378_ == 0 {
                        v___x_2352_ = v___x_2348_;
                        v_isShared_2353_ = v_isSharedCheck_2378_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2350_);
                        crate::leanh::lean_inc(v_a_2349_);
                        crate::leanh::lean_dec(v___x_2348_);
                        v___x_2352_ = crate::leanh::lean_box(0);
                        v_isShared_2353_ = v_isSharedCheck_2378_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_2379_ = crate::leanh::lean_ctor_get(v___x_2348_, 0);
                    v_a_2380_ = crate::leanh::lean_ctor_get(v___x_2348_, 1);
                    v_isSharedCheck_2387_ = (!crate::leanh::lean_is_exclusive(v___x_2348_)) as u8;
                    if v_isSharedCheck_2387_ == 0 {
                        v___x_2382_ = v___x_2348_;
                        v_isShared_2383_ = v_isSharedCheck_2387_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2380_);
                        crate::leanh::lean_inc(v_a_2379_);
                        crate::leanh::lean_dec(v___x_2348_);
                        v___x_2382_ = crate::leanh::lean_box(0);
                        v_isShared_2383_ = v_isSharedCheck_2387_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v_ref_2354_ = crate::leanh::lean_ctor_get(v___y_2342_, 5);
                v___x_2355_ = 0;
                v___x_2356_ = l_Lean_SourceInfo_fromRef(v_ref_2354_, v___x_2355_);
                v___x_2357_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__21;
                v___x_2358_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__22;
                crate::leanh::lean_inc_n(v___x_2356_, 5);
                v___x_2359_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2359_, 0, v___x_2356_);
                crate::leanh::lean_ctor_set(v___x_2359_, 1, v___x_2358_);
                v___x_2360_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__9;
                v___x_2361_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__11;
                v___x_2362_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__13;
                v___x_2363_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__19), core::ptr::addr_of_mut!(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__19_once), _init_l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__19);
                v_sz_2364_ = lean_array_size(v_a_2349_);
                v___x_2365_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse_spec__0(v_sz_2364_, v___x_2347_, v_a_2349_);
                v___x_2366_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__19;
                v___x_2367_ = l_Lean_mkSepArray(v___x_2365_, v___x_2366_);
                crate::leanh::lean_dec_ref(v___x_2365_);
                v___x_2368_ = l_Array_append___redArg(v___x_2363_, v___x_2367_);
                crate::leanh::lean_dec_ref(v___x_2367_);
                v___x_2369_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2369_, 0, v___x_2356_);
                crate::leanh::lean_ctor_set(v___x_2369_, 1, v___x_2362_);
                crate::leanh::lean_ctor_set(v___x_2369_, 2, v___x_2368_);
                v___x_2370_ = l_Lean_Syntax_node1(v___x_2356_, v___x_2361_, v___x_2369_);
                v___x_2371_ = l_Lean_Syntax_node1(v___x_2356_, v___x_2360_, v___x_2370_);
                v___x_2372_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__23;
                v___x_2373_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2373_, 0, v___x_2356_);
                crate::leanh::lean_ctor_set(v___x_2373_, 1, v___x_2372_);
                v___x_2374_ = l_Lean_Syntax_node3(
                    v___x_2356_,
                    v___x_2357_,
                    v___x_2359_,
                    v___x_2371_,
                    v___x_2373_,
                );
                if v_isShared_2353_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2352_, 0, v___x_2374_);
                    v___x_2376_ = v___x_2352_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2377_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2377_, 0, v___x_2374_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2377_, 1, v_a_2350_);
                    v___x_2376_ = v_reuseFailAlloc_2377_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2376_;
            }
            4 => {
                if v_isShared_2383_ == 0 {
                    v___x_2385_ = v___x_2382_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2386_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2386_, 0, v_a_2379_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2386_, 1, v_a_2380_);
                    v___x_2385_ = v_reuseFailAlloc_2386_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2385_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1___boxed(
    mut v_x_2398_: *mut crate::leanh::LeanObject,
    mut v_a_2399_: *mut crate::leanh::LeanObject,
    mut v_a_2400_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2401_ = l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1(v_x_2398_, v_a_2399_, v_a_2400_);
    crate::leanh::lean_dec_ref(v_a_2399_);
    return v_res_2401_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2454_ = l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__11;
    v___x_2455_ = l_String_toRawSubstring_x27(v___x_2454_);
    return v___x_2455_;
}
pub unsafe fn l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1(
    mut v_x_2466_: *mut crate::leanh::LeanObject,
    mut v_a_2467_: *mut crate::leanh::LeanObject,
    mut v_a_2468_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: u8 = 0;
    v___x_2469_ = l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__1;
    crate::leanh::lean_inc(v_x_2466_);
    v___x_2470_ = l_Lean_Syntax_isOfKind(v_x_2466_, v___x_2469_);
    if v___x_2470_ == 0 {
        let mut v___x_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_2466_);
        v___x_2471_ = crate::leanh::lean_box(1);
        v___x_2472_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2472_, 0, v___x_2471_);
        crate::leanh::lean_ctor_set(v___x_2472_, 1, v_a_2468_);
        return v___x_2472_;
    } else {
        let mut v_quotContext_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2478_: u8 = 0;
        let mut v___x_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_2473_ = crate::leanh::lean_ctor_get(v_a_2467_, 1);
        v_currMacroScope_2474_ = crate::leanh::lean_ctor_get(v_a_2467_, 2);
        v_ref_2475_ = crate::leanh::lean_ctor_get(v_a_2467_, 5);
        v___x_2476_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_2477_ = l_Lean_Syntax_getArg(v_x_2466_, v___x_2476_);
        crate::leanh::lean_dec(v_x_2466_);
        v___x_2478_ = 0;
        v___x_2479_ = l_Lean_SourceInfo_fromRef(v_ref_2475_, v___x_2478_);
        v___x_2480_ = l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__0;
        v___x_2481_ = l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__1;
        crate::leanh::lean_inc_n(v___x_2479_, 13);
        v___x_2482_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2482_, 0, v___x_2479_);
        crate::leanh::lean_ctor_set(v___x_2482_, 1, v___x_2480_);
        v___x_2483_ = l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__3;
        v___x_2484_ = l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__4;
        v___x_2485_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2485_, 0, v___x_2479_);
        crate::leanh::lean_ctor_set(v___x_2485_, 1, v___x_2484_);
        v___x_2486_ = l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__6;
        v___x_2487_ = l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__8;
        v___x_2488_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__22;
        v___x_2489_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2489_, 0, v___x_2479_);
        crate::leanh::lean_ctor_set(v___x_2489_, 1, v___x_2488_);
        v___x_2490_ = l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__10;
        v___x_2491_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__12), core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__12_once), _init_l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__12);
        v___x_2492_ = crate::leanh::lean_box(0);
        crate::leanh::lean_inc(v_currMacroScope_2474_);
        crate::leanh::lean_inc(v_quotContext_2473_);
        v___x_2493_ =
            l_Lean_addMacroScope(v_quotContext_2473_, v___x_2492_, v_currMacroScope_2474_);
        v___x_2494_ = l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__15;
        v___x_2495_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2495_, 0, v___x_2479_);
        crate::leanh::lean_ctor_set(v___x_2495_, 1, v___x_2491_);
        crate::leanh::lean_ctor_set(v___x_2495_, 2, v___x_2493_);
        crate::leanh::lean_ctor_set(v___x_2495_, 3, v___x_2494_);
        v___x_2496_ = l_Lean_Syntax_node1(v___x_2479_, v___x_2490_, v___x_2495_);
        v___x_2497_ = l_Lean_Syntax_node2(v___x_2479_, v___x_2487_, v___x_2489_, v___x_2496_);
        v___x_2498_ = l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__3;
        v___x_2499_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2499_, 0, v___x_2479_);
        crate::leanh::lean_ctor_set(v___x_2499_, 1, v___x_2498_);
        v___x_2500_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__13;
        v___x_2501_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__6;
        v___x_2502_ = l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__16;
        v___x_2503_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2503_, 0, v___x_2479_);
        crate::leanh::lean_ctor_set(v___x_2503_, 1, v___x_2502_);
        v___x_2504_ = l_Lean_Syntax_node1(v___x_2479_, v___x_2501_, v___x_2503_);
        v___x_2505_ = l_Lean_Syntax_node1(v___x_2479_, v___x_2500_, v___x_2504_);
        v___x_2506_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__23;
        v___x_2507_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2507_, 0, v___x_2479_);
        crate::leanh::lean_ctor_set(v___x_2507_, 1, v___x_2506_);
        v___x_2508_ = l_Lean_Syntax_node5(
            v___x_2479_,
            v___x_2486_,
            v___x_2497_,
            v___x_2477_,
            v___x_2499_,
            v___x_2505_,
            v___x_2507_,
        );
        v___x_2509_ = l_Lean_Syntax_node2(v___x_2479_, v___x_2483_, v___x_2485_, v___x_2508_);
        v___x_2510_ = l_Lean_Syntax_node2(v___x_2479_, v___x_2481_, v___x_2482_, v___x_2509_);
        v___x_2511_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2511_, 0, v___x_2510_);
        crate::leanh::lean_ctor_set(v___x_2511_, 1, v_a_2468_);
        return v___x_2511_;
    }
}
pub unsafe fn l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___boxed(
    mut v_x_2512_: *mut crate::leanh::LeanObject,
    mut v_a_2513_: *mut crate::leanh::LeanObject,
    mut v_a_2514_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2515_ = l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1(v_x_2512_, v_a_2513_, v_a_2514_);
    crate::leanh::lean_dec_ref(v_a_2513_);
    return v_res_2515_;
}
pub unsafe fn l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticApply__mod__cast____1(
    mut v_x_2541_: *mut crate::leanh::LeanObject,
    mut v_a_2542_: *mut crate::leanh::LeanObject,
    mut v_a_2543_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: u8 = 0;
    v___x_2544_ = l_Lean_Parser_Tactic_tacticApply__mod__cast___00__closed__1;
    crate::leanh::lean_inc(v_x_2541_);
    v___x_2545_ = l_Lean_Syntax_isOfKind(v_x_2541_, v___x_2544_);
    if v___x_2545_ == 0 {
        let mut v___x_2546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_2541_);
        v___x_2546_ = crate::leanh::lean_box(1);
        v___x_2547_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2547_, 0, v___x_2546_);
        crate::leanh::lean_ctor_set(v___x_2547_, 1, v_a_2543_);
        return v___x_2547_;
    } else {
        let mut v_quotContext_2548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_2549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2553_: u8 = 0;
        let mut v___x_2554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_2548_ = crate::leanh::lean_ctor_get(v_a_2542_, 1);
        v_currMacroScope_2549_ = crate::leanh::lean_ctor_get(v_a_2542_, 2);
        v_ref_2550_ = crate::leanh::lean_ctor_get(v_a_2542_, 5);
        v___x_2551_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_2552_ = l_Lean_Syntax_getArg(v_x_2541_, v___x_2551_);
        crate::leanh::lean_dec(v_x_2541_);
        v___x_2553_ = 0;
        v___x_2554_ = l_Lean_SourceInfo_fromRef(v_ref_2550_, v___x_2553_);
        v___x_2555_ = l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticApply__mod__cast____1___closed__0;
        v___x_2556_ = l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticApply__mod__cast____1___closed__1;
        crate::leanh::lean_inc_n(v___x_2554_, 13);
        v___x_2557_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2557_, 0, v___x_2554_);
        crate::leanh::lean_ctor_set(v___x_2557_, 1, v___x_2555_);
        v___x_2558_ = l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__3;
        v___x_2559_ = l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__4;
        v___x_2560_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2560_, 0, v___x_2554_);
        crate::leanh::lean_ctor_set(v___x_2560_, 1, v___x_2559_);
        v___x_2561_ = l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__6;
        v___x_2562_ = l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__8;
        v___x_2563_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__22;
        v___x_2564_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2564_, 0, v___x_2554_);
        crate::leanh::lean_ctor_set(v___x_2564_, 1, v___x_2563_);
        v___x_2565_ = l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__10;
        v___x_2566_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__12), core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__12_once), _init_l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__12);
        v___x_2567_ = crate::leanh::lean_box(0);
        crate::leanh::lean_inc(v_currMacroScope_2549_);
        crate::leanh::lean_inc(v_quotContext_2548_);
        v___x_2568_ =
            l_Lean_addMacroScope(v_quotContext_2548_, v___x_2567_, v_currMacroScope_2549_);
        v___x_2569_ = l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__15;
        v___x_2570_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2570_, 0, v___x_2554_);
        crate::leanh::lean_ctor_set(v___x_2570_, 1, v___x_2566_);
        crate::leanh::lean_ctor_set(v___x_2570_, 2, v___x_2568_);
        crate::leanh::lean_ctor_set(v___x_2570_, 3, v___x_2569_);
        v___x_2571_ = l_Lean_Syntax_node1(v___x_2554_, v___x_2565_, v___x_2570_);
        v___x_2572_ = l_Lean_Syntax_node2(v___x_2554_, v___x_2562_, v___x_2564_, v___x_2571_);
        v___x_2573_ = l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__3;
        v___x_2574_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2574_, 0, v___x_2554_);
        crate::leanh::lean_ctor_set(v___x_2574_, 1, v___x_2573_);
        v___x_2575_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__13;
        v___x_2576_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__6;
        v___x_2577_ = l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__16;
        v___x_2578_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2578_, 0, v___x_2554_);
        crate::leanh::lean_ctor_set(v___x_2578_, 1, v___x_2577_);
        v___x_2579_ = l_Lean_Syntax_node1(v___x_2554_, v___x_2576_, v___x_2578_);
        v___x_2580_ = l_Lean_Syntax_node1(v___x_2554_, v___x_2575_, v___x_2579_);
        v___x_2581_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__23;
        v___x_2582_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2582_, 0, v___x_2554_);
        crate::leanh::lean_ctor_set(v___x_2582_, 1, v___x_2581_);
        v___x_2583_ = l_Lean_Syntax_node5(
            v___x_2554_,
            v___x_2561_,
            v___x_2572_,
            v___x_2552_,
            v___x_2574_,
            v___x_2580_,
            v___x_2582_,
        );
        v___x_2584_ = l_Lean_Syntax_node2(v___x_2554_, v___x_2558_, v___x_2560_, v___x_2583_);
        v___x_2585_ = l_Lean_Syntax_node2(v___x_2554_, v___x_2556_, v___x_2557_, v___x_2584_);
        v___x_2586_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2586_, 0, v___x_2585_);
        crate::leanh::lean_ctor_set(v___x_2586_, 1, v_a_2543_);
        return v___x_2586_;
    }
}
pub unsafe fn l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticApply__mod__cast____1___boxed(
    mut v_x_2587_: *mut crate::leanh::LeanObject,
    mut v_a_2588_: *mut crate::leanh::LeanObject,
    mut v_a_2589_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2590_ = l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticApply__mod__cast____1(v_x_2587_, v_a_2588_, v_a_2589_);
    crate::leanh::lean_dec_ref(v_a_2588_);
    return v_res_2590_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_TacticsExtra(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Tactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_TacticsExtra(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Init_Meta(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Parser_Tactic_tacticRw__mod__cast______ =
        _init_l_Lean_Parser_Tactic_tacticRw__mod__cast______();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Tactic_tacticRw__mod__cast______);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_TacticsExtra(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Meta(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Tactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_TacticsExtra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_TacticsExtra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_TacticsExtra(builtin);
}
