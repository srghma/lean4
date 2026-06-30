// Lean compiler output
// Module: Lean.Compiler.NameDemangling
// Imports: Init.While Init.Data.String.TakeDrop Init.Data.String.Search Init.Data.String.Iterate Lean.Data.NameTrie Lean.Compiler.NameMangling
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size, lean_array_mk,
    lean_array_pop, lean_array_push, lean_array_size, lean_array_to_list, lean_array_uget_borrowed,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub,
    lean_string_append, lean_string_dec_eq, lean_string_get_byte_fast, lean_string_memcmp,
    lean_string_utf8_byte_size, lean_string_utf8_extract, lean_string_utf8_get_fast,
    lean_string_utf8_next_fast, lean_uint8_dec_eq, lean_uint32_dec_eq, lean_uint32_dec_le,
    lean_usize_add, lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::String::Basic::l_String_Slice_pos_x21;
use crate::r#gen::Init::Data::String::Defs::l_String_intercalate;
use crate::r#gen::Init::Data::String::FindPos::l_String_Slice_posGE___redArg;
use crate::r#gen::Init::Data::String::Iterate::{
    initialize_Init_Data_String_Iterate, runtime_initialize_Init_Data_String_Iterate,
};
use crate::r#gen::Init::Data::String::Pattern::String::l_String_Slice_Pattern_ForwardSliceSearcher_buildTable;
use crate::r#gen::Init::Data::String::Search::{
    initialize_Init_Data_String_Search, runtime_initialize_Init_Data_String_Search,
};
use crate::r#gen::Init::Data::String::Slice::l_String_Slice_toString;
use crate::r#gen::Init::Data::String::TakeDrop::{
    initialize_Init_Data_String_TakeDrop, runtime_initialize_Init_Data_String_TakeDrop,
};
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toString;
use crate::r#gen::Init::Prelude::{
    l_Array_extract___redArg, l_Lean_Name_num___override, l_Lean_Name_str___override,
};
use crate::r#gen::Init::While::{initialize_Init_While, runtime_initialize_Init_While};
use crate::r#gen::Lean::Compiler::NameMangling::{
    initialize_Lean_Compiler_NameMangling, l_Lean_Name_demangle, l_Lean_Name_demangle_x3f,
    runtime_initialize_Lean_Compiler_NameMangling,
};
use crate::r#gen::Lean::Data::NameTrie::{
    initialize_Lean_Data_NameTrie, l_Lean_instBEqNamePart_beq,
    l_Lean_instInhabitedNamePart_default, runtime_initialize_Lean_Data_NameTrie,
};
pub static l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts___closed__0_value: leanh::LeanStringObject<1> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__0_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 1, m_data: [206, 187, 0]};
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__1_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__0_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__2_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [95, 101, 108, 97, 109, 95, 0]};
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__3_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [95, 101, 108, 97, 109, 0]};
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__4_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [95, 106, 112, 0]};
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__5_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 99, 108, 111, 115, 101, 100, 0]};
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__6_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [95, 108, 97, 109, 95, 0]};
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__7_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [99, 108, 111, 115, 101, 100, 0]};
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__7_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__8_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__7_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__8_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__9_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [106, 112, 0]};
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__9_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__10_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__9_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__10_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__11_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 114, 101, 100, 65, 114, 103, 0]};
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__11_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__12_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [95, 98, 111, 120, 101, 100, 0]};
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__12_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__13_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [95, 105, 109, 112, 108, 0]};
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__13_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__14_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 108, 97, 109, 0]};
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__14_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__15_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 108, 97, 109, 98, 100, 97, 0]};
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__15: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__15_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__16_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [105, 109, 112, 108, 0]};
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__16_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__17_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__16_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__17: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__17_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__18_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [98, 111, 120, 101, 100, 0]};
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__18_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__19_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__18_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__19: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__19_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__20_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 6, m_data: [97, 114, 105, 116, 121, 226, 134, 147, 0]};
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__20: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__20_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__21_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__20_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__21: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__21_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isSpecIndex___closed__0_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [115, 112, 101, 99, 95, 0]};
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isSpecIndex___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isSpecIndex___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg___closed__1_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg___closed__2_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg___closed__1_value) as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate___closed__0_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate___closed__1_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate___closed__0_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate___closed__2_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate___closed__1_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext___closed__0_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext___closed__1_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext___closed__0_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext___closed__0_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___redArg___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 97, 116, 95, 0]};
static mut l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___redArg___closed__1_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___redArg___closed__0_value) as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg___closed__0_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__0_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [95, 115, 112, 101, 99, 0]};
static mut l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__1_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__0_value) as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__1_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__3_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext___closed__0_value) as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__0_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [32, 115, 112, 101, 99, 32, 97, 116, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__1_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [91, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__2_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [44, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__3_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__4_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [63, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts___closed__0_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [32, 91, 0]};
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts___closed__1_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts___closed__2_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts___closed__1_value) as *mut leanh::LeanObject,((( 1 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts___closed__3_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts___closed__3_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___redArg___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__0_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [46, 99, 111, 108, 100, 0]};
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__2: u8 = 0;
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__6_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__0_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [108, 112, 95, 0]};
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__1_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [32, 40, 0]};
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__2_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__3_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [108, 95, 0]};
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__4_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [105, 110, 105, 116, 105, 97, 108, 105, 122, 101, 95, 0]};
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__5_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [91, 109, 111, 100, 117, 108, 101, 95, 105, 110, 105, 116, 93, 32, 0]};
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__6_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [105, 110, 105, 116, 105, 97, 108, 105, 122, 101, 95, 108, 112, 95, 0]};
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__7_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [105, 110, 105, 116, 105, 97, 108, 105, 122, 101, 95, 108, 95, 0]};
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__7_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__8_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [95, 105, 110, 105, 116, 95, 108, 112, 95, 0]};
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__8_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__9_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [91, 105, 110, 105, 116, 93, 32, 0]};
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__9_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__10_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 105, 110, 105, 116, 95, 108, 95, 0]};
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__10_value) as *mut leanh::LeanObject;
pub static l_Lean_Name_Demangle_demangleSymbol___closed__0_value: leanh::LeanStringObject<
    11,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [95, 108, 101, 97, 110, 95, 109, 97, 105, 110, 0],
};
static mut l_Lean_Name_Demangle_demangleSymbol___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Name_Demangle_demangleSymbol___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Name_Demangle_demangleSymbol___closed__1_value: leanh::LeanStringObject<
    2,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [32, 0],
};
static mut l_Lean_Name_Demangle_demangleSymbol___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Name_Demangle_demangleSymbol___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Name_Demangle_demangleSymbol___closed__2_value: leanh::LeanStringObject<
    13,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [91, 108, 101, 97, 110, 93, 32, 109, 97, 105, 110, 32, 0],
};
static mut l_Lean_Name_Demangle_demangleSymbol___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Name_Demangle_demangleSymbol___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Name_Demangle_demangleSymbol___closed__3_value: leanh::LeanStringObject<
    12,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [91, 108, 101, 97, 110, 93, 32, 109, 97, 105, 110, 0],
};
static mut l_Lean_Name_Demangle_demangleSymbol___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Name_Demangle_demangleSymbol___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Name_Demangle_demangleSymbol___closed__4_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Name_Demangle_demangleSymbol___closed__3_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Name_Demangle_demangleSymbol___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Name_Demangle_demangleSymbol___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Name_Demangle_demangleSymbol___closed__5_value: leanh::LeanStringObject<
    12,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [108, 101, 97, 110, 95, 97, 112, 112, 108, 121, 95, 0],
};
static mut l_Lean_Name_Demangle_demangleSymbol___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Name_Demangle_demangleSymbol___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Name_Demangle_demangleSymbol___closed__6_value: leanh::LeanStringObject<
    8,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [60, 97, 112, 112, 108, 121, 47, 0],
};
static mut l_Lean_Name_Demangle_demangleSymbol___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Name_Demangle_demangleSymbol___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Name_Demangle_demangleSymbol___closed__7_value: leanh::LeanStringObject<
    2,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [62, 0],
};
static mut l_Lean_Name_Demangle_demangleSymbol___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Name_Demangle_demangleSymbol___closed__7_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___lam__0___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__1_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___lam__1___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__2_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [48, 120, 0]};
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__3_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [32, 43, 32, 0]};
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__3_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__5: u8 = 0;
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__6_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__6: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__8_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__8: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__10_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__10: u8 = 0;
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__12_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__12: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__13_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__13: *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_String_dropPrefix_x3f___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f_spec__0___redArg(
    mut v_pre_1850_: *mut leanh::LeanObject,
    mut v_s_1851_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: u8 = 0;
    v___x_1852_ = lean_string_utf8_byte_size(v_s_1851_);
    v___x_1853_ = lean_string_utf8_byte_size(v_pre_1850_);
    v___x_1854_ = lean_nat_dec_le(v___x_1853_, v___x_1852_);
    if v___x_1854_ == 0 {
        let mut v___x_1855_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_s_1851_);
        v___x_1855_ = leanh::lean_box(0);
        return v___x_1855_;
    } else {
        let mut v___x_1856_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1857_: u8 = 0;
        v___x_1856_ = leanh::lean_unsigned_to_nat(0);
        v___x_1857_ = lean_string_memcmp(
            v_s_1851_,
            v_pre_1850_,
            v___x_1856_,
            v___x_1856_,
            v___x_1853_,
        );
        if v___x_1857_ == 0 {
            let mut v___x_1858_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v_s_1851_);
            v___x_1858_ = leanh::lean_box(0);
            return v___x_1858_;
        } else {
            let mut v___x_1859_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1860_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1861_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc_ref(v_s_1851_);
            v___x_1859_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
            leanh::lean_ctor_set(v___x_1859_, 0, v_s_1851_);
            leanh::lean_ctor_set(v___x_1859_, 1, v___x_1856_);
            leanh::lean_ctor_set(v___x_1859_, 2, v___x_1852_);
            v___x_1860_ = l_String_Slice_pos_x21(v___x_1859_, v___x_1853_);
            leanh::lean_dec_ref_known(v___x_1859_, 3);
            v___x_1861_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
            leanh::lean_ctor_set(v___x_1861_, 0, v_s_1851_);
            leanh::lean_ctor_set(v___x_1861_, 1, v___x_1860_);
            leanh::lean_ctor_set(v___x_1861_, 2, v___x_1852_);
            v___x_1862_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_1862_, 0, v___x_1861_);
            return v___x_1862_;
        }
    }
}
pub unsafe fn l_String_dropPrefix_x3f___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f_spec__0___redArg___boxed(
    mut v_pre_1863_: *mut leanh::LeanObject,
    mut v_s_1864_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1865_ = l_String_dropPrefix_x3f___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f_spec__0___redArg(v_pre_1863_, v_s_1864_);
    leanh::lean_dec_ref(v_pre_1863_);
    return v_res_1865_;
}
pub unsafe fn l_String_dropPrefix_x3f___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f_spec__0(
    mut v_pre_1866_: *mut leanh::LeanObject,
    mut v_s_1867_: *mut leanh::LeanObject,
    mut v_pat_1868_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1869_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1869_ = l_String_dropPrefix_x3f___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f_spec__0___redArg(v_pre_1866_, v_s_1867_);
    return v___x_1869_;
}
pub unsafe fn l_String_dropPrefix_x3f___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f_spec__0___boxed(
    mut v_pre_1870_: *mut leanh::LeanObject,
    mut v_s_1871_: *mut leanh::LeanObject,
    mut v_pat_1872_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1873_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1873_ = l_String_dropPrefix_x3f___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f_spec__0(v_pre_1870_, v_s_1871_, v_pat_1872_);
    leanh::lean_dec_ref(v_pat_1872_);
    leanh::lean_dec_ref(v_pre_1870_);
    return v_res_1873_;
}
pub unsafe fn l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(
    mut v_s_1874_: *mut leanh::LeanObject,
    mut v_pre_1875_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1881_: u8 = 0;
    let mut v___x_1882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1886_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1876_ = l_String_dropPrefix_x3f___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f_spec__0___redArg(v_pre_1875_, v_s_1874_);
                if leanh::lean_obj_tag(v___x_1876_) == 0 {
                    v___x_1877_ = leanh::lean_box(0);
                    return v___x_1877_;
                } else {
                    v_val_1878_ = leanh::lean_ctor_get(v___x_1876_, 0);
                    v_isSharedCheck_1886_ = (!leanh::lean_is_exclusive(v___x_1876_)) as u8;
                    if v_isSharedCheck_1886_ == 0 {
                        v___x_1880_ = v___x_1876_;
                        v_isShared_1881_ = v_isSharedCheck_1886_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1878_);
                        leanh::lean_dec(v___x_1876_);
                        v___x_1880_ = leanh::lean_box(0);
                        v_isShared_1881_ = v_isSharedCheck_1886_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1882_ = l_String_Slice_toString(v_val_1878_);
                leanh::lean_dec(v_val_1878_);
                if v_isShared_1881_ == 0 {
                    leanh::lean_ctor_set(v___x_1880_, 0, v___x_1882_);
                    v___x_1884_ = v___x_1880_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1885_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1885_, 0, v___x_1882_);
                    v___x_1884_ = v_reuseFailAlloc_1885_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1884_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f___boxed(
    mut v_s_1887_: *mut leanh::LeanObject,
    mut v_pre_1888_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1889_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1889_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(
        v_s_1887_,
        v_pre_1888_,
    );
    leanh::lean_dec_ref(v_pre_1888_);
    return v_res_1889_;
}
pub unsafe fn l_String_Slice_Pos_skipWhile___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isAllDigits_spec__0(
    mut v_s_1890_: *mut leanh::LeanObject,
    mut v_pos_1891_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_str_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1897_: u8 = 0;
    let mut v___x_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: u8 = 0;
    let mut v___x_1903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: u8 = 0;
    let mut v___x_1906_: u32 = 0;
    let mut v___x_1907_: u32 = 0;
    let mut v___x_1908_: u8 = 0;
    let mut v___x_1909_: u32 = 0;
    let mut v___x_1910_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_1892_ = leanh::lean_ctor_get(v_s_1890_, 0);
                v_startInclusive_1893_ = leanh::lean_ctor_get(v_s_1890_, 1);
                v_endExclusive_1894_ = leanh::lean_ctor_get(v_s_1890_, 2);
                v___x_1895_ = lean_nat_add(v_startInclusive_1893_, v_pos_1891_);
                v___x_1903_ = leanh::lean_unsigned_to_nat(0);
                v___x_1904_ = lean_nat_sub(v_endExclusive_1894_, v___x_1895_);
                v___x_1905_ = lean_nat_dec_eq(v___x_1903_, v___x_1904_);
                leanh::lean_dec(v___x_1904_);
                if v___x_1905_ == 0 {
                    v___x_1906_ = lean_string_utf8_get_fast(v_str_1892_, v___x_1895_);
                    v___x_1907_ = 48;
                    v___x_1908_ = lean_uint32_dec_le(v___x_1907_, v___x_1906_);
                    if v___x_1908_ == 0 {
                        v___y_1897_ = v___x_1908_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1909_ = 57;
                        v___x_1910_ = lean_uint32_dec_le(v___x_1906_, v___x_1909_);
                        v___y_1897_ = v___x_1910_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_1895_);
                    return v_pos_1891_;
                }
            }
            1 => {
                if v___y_1897_ == 0 {
                    leanh::lean_dec(v___x_1895_);
                    return v_pos_1891_;
                } else {
                    v___x_1898_ = lean_string_utf8_next_fast(v_str_1892_, v___x_1895_);
                    v___x_1899_ = lean_nat_sub(v___x_1898_, v___x_1895_);
                    leanh::lean_dec(v___x_1895_);
                    v___x_1900_ = lean_nat_add(v_pos_1891_, v___x_1899_);
                    leanh::lean_dec(v___x_1899_);
                    v___x_1901_ = lean_nat_dec_lt(v_pos_1891_, v___x_1900_);
                    if v___x_1901_ == 0 {
                        leanh::lean_dec(v___x_1900_);
                        return v_pos_1891_;
                    } else {
                        leanh::lean_dec(v_pos_1891_);
                        v_pos_1891_ = v___x_1900_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_Pos_skipWhile___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isAllDigits_spec__0___boxed(
    mut v_s_1911_: *mut leanh::LeanObject,
    mut v_pos_1912_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1913_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1913_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isAllDigits_spec__0(v_s_1911_, v_pos_1912_);
    leanh::lean_dec_ref(v_s_1911_);
    return v_res_1913_;
}
pub unsafe fn l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isAllDigits(
    mut v_s_1914_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: u8 = 0;
    v___x_1915_ = lean_string_utf8_byte_size(v_s_1914_);
    v___x_1916_ = leanh::lean_unsigned_to_nat(0);
    v___x_1917_ = lean_nat_dec_eq(v___x_1915_, v___x_1916_);
    if v___x_1917_ == 0 {
        let mut v___x_1918_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1919_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1920_: u8 = 0;
        v___x_1918_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
        leanh::lean_ctor_set(v___x_1918_, 0, v_s_1914_);
        leanh::lean_ctor_set(v___x_1918_, 1, v___x_1916_);
        leanh::lean_ctor_set(v___x_1918_, 2, v___x_1915_);
        v___x_1919_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isAllDigits_spec__0(v___x_1918_, v___x_1916_);
        leanh::lean_dec_ref_known(v___x_1918_, 3);
        v___x_1920_ = lean_nat_dec_eq(v___x_1919_, v___x_1915_);
        leanh::lean_dec(v___x_1919_);
        return v___x_1920_;
    } else {
        let mut v___x_1921_: u8 = 0;
        leanh::lean_dec_ref(v_s_1914_);
        v___x_1921_ = 0;
        return v___x_1921_;
    }
}
pub unsafe fn l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isAllDigits___boxed(
    mut v_s_1922_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1923_: u8 = 0;
    let mut v_r_1924_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1923_ =
        l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isAllDigits(v_s_1922_);
    v_r_1924_ = leanh::lean_box((v_res_1923_) as usize);
    return v_r_1924_;
}
pub unsafe fn l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_nameToNameParts_go(
    mut v_a_1925_: *mut leanh::LeanObject,
    mut v_a_1926_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pre_1927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_1932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_a_1925_) {
                0 => {
                    return v_a_1926_;
                }
                1 => {
                    v_pre_1927_ = leanh::lean_ctor_get(v_a_1925_, 0);
                    v_str_1928_ = leanh::lean_ctor_get(v_a_1925_, 1);
                    leanh::lean_inc_ref(v_str_1928_);
                    v___x_1929_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1929_, 0, v_str_1928_);
                    v___x_1930_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1930_, 0, v___x_1929_);
                    leanh::lean_ctor_set(v___x_1930_, 1, v_a_1926_);
                    v_a_1925_ = v_pre_1927_;
                    v_a_1926_ = v___x_1930_;
                    state = 0;
                    continue;
                }
                _ => {
                    v_pre_1932_ = leanh::lean_ctor_get(v_a_1925_, 0);
                    v_i_1933_ = leanh::lean_ctor_get(v_a_1925_, 1);
                    leanh::lean_inc(v_i_1933_);
                    v___x_1934_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1934_, 0, v_i_1933_);
                    v___x_1935_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1935_, 0, v___x_1934_);
                    leanh::lean_ctor_set(v___x_1935_, 1, v_a_1926_);
                    v_a_1925_ = v_pre_1932_;
                    v_a_1926_ = v___x_1935_;
                    state = 0;
                    continue;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_nameToNameParts_go___boxed(
    mut v_a_1937_: *mut leanh::LeanObject,
    mut v_a_1938_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1939_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_nameToNameParts_go(
        v_a_1937_, v_a_1938_,
    );
    leanh::lean_dec(v_a_1937_);
    return v_res_1939_;
}
pub unsafe fn l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_nameToNameParts(
    mut v_n_1940_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1941_ = leanh::lean_box(0);
    v___x_1942_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_nameToNameParts_go(
        v_n_1940_,
        v___x_1941_,
    );
    v___x_1943_ = lean_array_mk(v___x_1942_);
    return v___x_1943_;
}
pub unsafe fn l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_nameToNameParts___boxed(
    mut v_n_1944_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1945_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1945_ =
        l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_nameToNameParts(v_n_1944_);
    leanh::lean_dec(v_n_1944_);
    return v_res_1945_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_namePartsToName_spec__0(
    mut v_as_1946_: *mut leanh::LeanObject,
    mut v_i_1947_: usize,
    mut v_stop_1948_: usize,
    mut v_b_1949_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: usize = 0;
    let mut v___x_1953_: usize = 0;
    let mut v___x_1955_: u8 = 0;
    let mut v___x_1956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1955_ = lean_usize_dec_eq(v_i_1947_, v_stop_1948_);
                if v___x_1955_ == 0 {
                    v___x_1956_ = lean_array_uget_borrowed(v_as_1946_, v_i_1947_);
                    if leanh::lean_obj_tag(v___x_1956_) == 0 {
                        v_s_1957_ = leanh::lean_ctor_get(v___x_1956_, 0);
                        leanh::lean_inc_ref(v_s_1957_);
                        v___x_1958_ = l_Lean_Name_str___override(v_b_1949_, v_s_1957_);
                        v___y_1951_ = v___x_1958_;
                        state = 1;
                        continue;
                    } else {
                        v_n_1959_ = leanh::lean_ctor_get(v___x_1956_, 0);
                        leanh::lean_inc(v_n_1959_);
                        v___x_1960_ = l_Lean_Name_num___override(v_b_1949_, v_n_1959_);
                        v___y_1951_ = v___x_1960_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_1949_;
                }
            }
            1 => {
                v___x_1952_ = 1usize;
                v___x_1953_ = lean_usize_add(v_i_1947_, v___x_1952_);
                v_i_1947_ = v___x_1953_;
                v_b_1949_ = v___y_1951_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_namePartsToName_spec__0___boxed(
    mut v_as_1961_: *mut leanh::LeanObject,
    mut v_i_1962_: *mut leanh::LeanObject,
    mut v_stop_1963_: *mut leanh::LeanObject,
    mut v_b_1964_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1965_: usize = 0;
    let mut v_stop_boxed_1966_: usize = 0;
    let mut v_res_1967_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1965_ = leanh::lean_unbox_usize(v_i_1962_);
    leanh::lean_dec(v_i_1962_);
    v_stop_boxed_1966_ = leanh::lean_unbox_usize(v_stop_1963_);
    leanh::lean_dec(v_stop_1963_);
    v_res_1967_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_namePartsToName_spec__0(v_as_1961_, v_i_boxed_1965_, v_stop_boxed_1966_, v_b_1964_);
    leanh::lean_dec_ref(v_as_1961_);
    return v_res_1967_;
}
pub unsafe fn l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_namePartsToName(
    mut v_parts_1968_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: u8 = 0;
    v___x_1969_ = leanh::lean_box(0);
    v___x_1970_ = leanh::lean_unsigned_to_nat(0);
    v___x_1971_ = lean_array_get_size(v_parts_1968_);
    v___x_1972_ = lean_nat_dec_lt(v___x_1970_, v___x_1971_);
    if v___x_1972_ == 0 {
        return v___x_1969_;
    } else {
        let mut v___x_1973_: u8 = 0;
        v___x_1973_ = lean_nat_dec_le(v___x_1971_, v___x_1971_);
        if v___x_1973_ == 0 {
            if v___x_1972_ == 0 {
                return v___x_1969_;
            } else {
                let mut v___x_1974_: usize = 0;
                let mut v___x_1975_: usize = 0;
                let mut v___x_1976_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1974_ = 0usize;
                v___x_1975_ = lean_usize_of_nat(v___x_1971_);
                v___x_1976_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_namePartsToName_spec__0(v_parts_1968_, v___x_1974_, v___x_1975_, v___x_1969_);
                return v___x_1976_;
            }
        } else {
            let mut v___x_1977_: usize = 0;
            let mut v___x_1978_: usize = 0;
            let mut v___x_1979_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1977_ = 0usize;
            v___x_1978_ = lean_usize_of_nat(v___x_1971_);
            v___x_1979_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_namePartsToName_spec__0(v_parts_1968_, v___x_1977_, v___x_1978_, v___x_1969_);
            return v___x_1979_;
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_namePartsToName___boxed(
    mut v_parts_1980_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1981_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1981_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_namePartsToName(
        v_parts_1980_,
    );
    leanh::lean_dec_ref(v_parts_1980_);
    return v_res_1981_;
}
pub unsafe fn l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts(
    mut v_comps_1983_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: u8 = 0;
    v___x_1984_ = lean_array_get_size(v_comps_1983_);
    v___x_1985_ = leanh::lean_unsigned_to_nat(0);
    v___x_1986_ = lean_nat_dec_eq(v___x_1984_, v___x_1985_);
    if v___x_1986_ == 0 {
        let mut v___x_1987_: u8 = 0;
        let mut v___x_1988_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1989_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1987_ = 1;
        v___x_1988_ =
            l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_namePartsToName(
                v_comps_1983_,
            );
        v___x_1989_ = l_Lean_Name_toString(v___x_1988_, v___x_1987_);
        return v___x_1989_;
    } else {
        let mut v___x_1990_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1990_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts___closed__0;
        return v___x_1990_;
    }
}
pub unsafe fn l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts___boxed(
    mut v_comps_1991_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1992_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1992_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts(
        v_comps_1991_,
    );
    leanh::lean_dec_ref(v_comps_1991_);
    return v_res_1992_;
}
pub unsafe fn l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix(
    mut v_c_2021_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_2024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2026_: u8 = 0;
    let mut v___x_2027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2030_: u8 = 0;
    let mut v___x_2031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2035_: u8 = 0;
    let mut v___x_2036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: u8 = 0;
    let mut v___x_2038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: u8 = 0;
    let mut v___x_2040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: u8 = 0;
    let mut v___x_2042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: u8 = 0;
    let mut v___x_2046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: u8 = 0;
    let mut v___x_2050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: u8 = 0;
    let mut v___x_2052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: u8 = 0;
    let mut v___x_2054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: u8 = 0;
    let mut v___x_2056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: u8 = 0;
    let mut v___x_2058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_c_2021_) == 0 {
                    v_s_2024_ = leanh::lean_ctor_get(v_c_2021_, 0);
                    leanh::lean_inc_ref(v_s_2024_);
                    leanh::lean_dec_ref_known(v_c_2021_, 1);
                    v___x_2048_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__11;
                    v___x_2049_ = lean_string_dec_eq(v_s_2024_, v___x_2048_);
                    if v___x_2049_ == 0 {
                        v___x_2050_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__12;
                        v___x_2051_ = lean_string_dec_eq(v_s_2024_, v___x_2050_);
                        if v___x_2051_ == 0 {
                            v___x_2052_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__13;
                            v___x_2053_ = lean_string_dec_eq(v_s_2024_, v___x_2052_);
                            if v___x_2053_ == 0 {
                                v___x_2054_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__14;
                                v___x_2055_ = lean_string_dec_eq(v_s_2024_, v___x_2054_);
                                if v___x_2055_ == 0 {
                                    v___x_2056_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__15;
                                    v___x_2057_ = lean_string_dec_eq(v_s_2024_, v___x_2056_);
                                    v___y_2035_ = v___x_2057_;
                                    state = 3;
                                    continue;
                                } else {
                                    v___y_2035_ = v___x_2055_;
                                    state = 3;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec_ref(v_s_2024_);
                                v___x_2058_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__17;
                                return v___x_2058_;
                            }
                        } else {
                            leanh::lean_dec_ref(v_s_2024_);
                            v___x_2059_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__19;
                            return v___x_2059_;
                        }
                    } else {
                        leanh::lean_dec_ref(v_s_2024_);
                        v___x_2060_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__21;
                        return v___x_2060_;
                    }
                } else {
                    leanh::lean_dec_ref(v_c_2021_);
                    v___x_2061_ = leanh::lean_box(0);
                    return v___x_2061_;
                }
            }
            1 => {
                v___x_2023_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__1;
                return v___x_2023_;
            }
            2 => {
                if v___y_2026_ == 0 {
                    v___x_2027_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__2;
                    v___x_2028_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_2024_, v___x_2027_);
                    if leanh::lean_obj_tag(v___x_2028_) == 0 {
                        return v___x_2028_;
                    } else {
                        v_val_2029_ = leanh::lean_ctor_get(v___x_2028_, 0);
                        leanh::lean_inc(v_val_2029_);
                        leanh::lean_dec_ref_known(v___x_2028_, 1);
                        v___x_2030_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isAllDigits(v_val_2029_);
                        if v___x_2030_ == 0 {
                            v___x_2031_ = leanh::lean_box(0);
                            return v___x_2031_;
                        } else {
                            v___x_2032_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__1;
                            return v___x_2032_;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_s_2024_);
                    v___x_2033_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__1;
                    return v___x_2033_;
                }
            }
            3 => {
                if v___y_2035_ == 0 {
                    v___x_2036_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__3;
                    v___x_2037_ = lean_string_dec_eq(v_s_2024_, v___x_2036_);
                    if v___x_2037_ == 0 {
                        v___x_2038_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__4;
                        v___x_2039_ = lean_string_dec_eq(v_s_2024_, v___x_2038_);
                        if v___x_2039_ == 0 {
                            v___x_2040_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__5;
                            v___x_2041_ = lean_string_dec_eq(v_s_2024_, v___x_2040_);
                            if v___x_2041_ == 0 {
                                v___x_2042_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__6;
                                leanh::lean_inc_ref(v_s_2024_);
                                v___x_2043_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_2024_, v___x_2042_);
                                if leanh::lean_obj_tag(v___x_2043_) == 0 {
                                    v___y_2026_ = v___x_2041_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_val_2044_ = leanh::lean_ctor_get(v___x_2043_, 0);
                                    leanh::lean_inc(v_val_2044_);
                                    leanh::lean_dec_ref_known(v___x_2043_, 1);
                                    v___x_2045_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isAllDigits(v_val_2044_);
                                    v___y_2026_ = v___x_2045_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec_ref(v_s_2024_);
                                v___x_2046_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__8;
                                return v___x_2046_;
                            }
                        } else {
                            leanh::lean_dec_ref(v_s_2024_);
                            v___x_2047_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__10;
                            return v___x_2047_;
                        }
                    } else {
                        leanh::lean_dec_ref(v_s_2024_);
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_s_2024_);
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isSpecIndex(
    mut v_c_2063_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_c_2063_) == 0 {
        let mut v_s_2064_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2065_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2066_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_s_2064_ = leanh::lean_ctor_get(v_c_2063_, 0);
        leanh::lean_inc_ref(v_s_2064_);
        leanh::lean_dec_ref_known(v_c_2063_, 1);
        v___x_2065_ =
            l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isSpecIndex___closed__0;
        v___x_2066_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(
            v_s_2064_,
            v___x_2065_,
        );
        if leanh::lean_obj_tag(v___x_2066_) == 0 {
            let mut v___x_2067_: u8 = 0;
            v___x_2067_ = 0;
            return v___x_2067_;
        } else {
            let mut v_val_2068_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2069_: u8 = 0;
            v_val_2068_ = leanh::lean_ctor_get(v___x_2066_, 0);
            leanh::lean_inc(v_val_2068_);
            leanh::lean_dec_ref_known(v___x_2066_, 1);
            v___x_2069_ =
                l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isAllDigits(
                    v_val_2068_,
                );
            return v___x_2069_;
        }
    } else {
        let mut v___x_2070_: u8 = 0;
        leanh::lean_dec_ref(v_c_2063_);
        v___x_2070_ = 0;
        return v___x_2070_;
    }
}
pub unsafe fn l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isSpecIndex___boxed(
    mut v_c_2071_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2072_: u8 = 0;
    let mut v_r_2073_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2072_ =
        l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isSpecIndex(v_c_2071_);
    v_r_2073_ = leanh::lean_box((v_res_2072_) as usize);
    return v_r_2073_;
}
pub unsafe fn l_Option_instBEq_beq___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__0(
    mut v_x_2074_: *mut leanh::LeanObject,
    mut v_x_2075_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_2074_) == 0 {
        if leanh::lean_obj_tag(v_x_2075_) == 0 {
            let mut v___x_2076_: u8 = 0;
            v___x_2076_ = 1;
            return v___x_2076_;
        } else {
            let mut v___x_2077_: u8 = 0;
            v___x_2077_ = 0;
            return v___x_2077_;
        }
    } else {
        if leanh::lean_obj_tag(v_x_2075_) == 0 {
            let mut v___x_2078_: u8 = 0;
            v___x_2078_ = 0;
            return v___x_2078_;
        } else {
            let mut v_val_2079_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_2080_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2081_: u8 = 0;
            v_val_2079_ = leanh::lean_ctor_get(v_x_2074_, 0);
            v_val_2080_ = leanh::lean_ctor_get(v_x_2075_, 0);
            v___x_2081_ = l_Lean_instBEqNamePart_beq(v_val_2079_, v_val_2080_);
            return v___x_2081_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__0___boxed(
    mut v_x_2082_: *mut leanh::LeanObject,
    mut v_x_2083_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2084_: u8 = 0;
    let mut v_r_2085_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2084_ = l_Option_instBEq_beq___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__0(v_x_2082_, v_x_2083_);
    leanh::lean_dec(v_x_2083_);
    leanh::lean_dec(v_x_2082_);
    v_r_2085_ = leanh::lean_box((v_res_2084_) as usize);
    return v_r_2085_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg(
    mut v_stop_2093_: *mut leanh::LeanObject,
    mut v_start_2094_: *mut leanh::LeanObject,
    mut v___y_2095_: u8,
    mut v_comps_2096_: *mut leanh::LeanObject,
    mut v_range_2097_: *mut leanh::LeanObject,
    mut v_b_2098_: *mut leanh::LeanObject,
    mut v_i_2099_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_stop_2100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_step_2101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: u8 = 0;
    let mut v___x_2103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: u8 = 0;
    let mut v___x_2111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: u8 = 0;
    let mut v___x_2115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: u8 = 0;
    let mut v___x_2125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stop_2100_ = leanh::lean_ctor_get(v_range_2097_, 1);
                v_step_2101_ = leanh::lean_ctor_get(v_range_2097_, 2);
                v___x_2102_ = lean_nat_dec_lt(v_i_2099_, v_stop_2100_);
                if v___x_2102_ == 0 {
                    leanh::lean_dec(v_i_2099_);
                    leanh::lean_dec(v_start_2094_);
                    leanh::lean_inc_ref(v_b_2098_);
                    return v_b_2098_;
                } else {
                    v___x_2103_ = leanh::lean_box(0);
                    v___x_2104_ = leanh::lean_box(0);
                    v___x_2105_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg___closed__0;
                    v___x_2106_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2123_ = lean_array_get_size(v_comps_2096_);
                    v___x_2124_ = lean_nat_dec_lt(v_i_2099_, v___x_2123_);
                    if v___x_2124_ == 0 {
                        v___y_2108_ = v___x_2103_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2125_ = lean_array_fget_borrowed(v_comps_2096_, v_i_2099_);
                        leanh::lean_inc(v___x_2125_);
                        v___x_2126_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2126_, 0, v___x_2125_);
                        v___y_2108_ = v___x_2126_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2109_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg___closed__2;
                v___x_2110_ = l_Option_instBEq_beq___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__0(v___y_2108_, v___x_2109_);
                leanh::lean_dec(v___y_2108_);
                if v___x_2110_ == 0 {
                    v___x_2111_ = lean_nat_add(v_i_2099_, v_step_2101_);
                    leanh::lean_dec(v_i_2099_);
                    v_b_2098_ = v___x_2105_;
                    v_i_2099_ = v___x_2111_;
                    state = 0;
                    continue;
                } else {
                    v___x_2113_ = lean_nat_add(v_i_2099_, v___x_2106_);
                    leanh::lean_dec(v_i_2099_);
                    v___x_2114_ = lean_nat_dec_lt(v___x_2113_, v_stop_2093_);
                    if v___x_2114_ == 0 {
                        leanh::lean_dec(v___x_2113_);
                        v___x_2115_ = leanh::lean_box((v___x_2114_) as usize);
                        v___x_2116_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2116_, 0, v_start_2094_);
                        leanh::lean_ctor_set(v___x_2116_, 1, v___x_2115_);
                        v___x_2117_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2117_, 0, v___x_2116_);
                        v___x_2118_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2118_, 0, v___x_2117_);
                        leanh::lean_ctor_set(v___x_2118_, 1, v___x_2104_);
                        return v___x_2118_;
                    } else {
                        leanh::lean_dec(v_start_2094_);
                        v___x_2119_ = leanh::lean_box((v___y_2095_) as usize);
                        v___x_2120_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2120_, 0, v___x_2113_);
                        leanh::lean_ctor_set(v___x_2120_, 1, v___x_2119_);
                        v___x_2121_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2121_, 0, v___x_2120_);
                        v___x_2122_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2122_, 0, v___x_2121_);
                        leanh::lean_ctor_set(v___x_2122_, 1, v___x_2104_);
                        return v___x_2122_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg___boxed(
    mut v_stop_2127_: *mut leanh::LeanObject,
    mut v_start_2128_: *mut leanh::LeanObject,
    mut v___y_2129_: *mut leanh::LeanObject,
    mut v_comps_2130_: *mut leanh::LeanObject,
    mut v_range_2131_: *mut leanh::LeanObject,
    mut v_b_2132_: *mut leanh::LeanObject,
    mut v_i_2133_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_946__boxed_2134_: u8 = 0;
    let mut v_res_2135_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_946__boxed_2134_ = (leanh::lean_unbox(v___y_2129_) as u8);
    v_res_2135_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg(v_stop_2127_, v_start_2128_, v___y_946__boxed_2134_, v_comps_2130_, v_range_2131_, v_b_2132_, v_i_2133_);
    leanh::lean_dec_ref(v_b_2132_);
    leanh::lean_dec_ref(v_range_2131_);
    leanh::lean_dec_ref(v_comps_2130_);
    leanh::lean_dec(v_stop_2127_);
    return v_res_2135_;
}
pub unsafe fn l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate(
    mut v_comps_2141_: *mut leanh::LeanObject,
    mut v_start_2142_: *mut leanh::LeanObject,
    mut v_stop_2143_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2145_: u8 = 0;
    let mut v___x_2146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2156_: u8 = 0;
    let mut v___x_2157_: u8 = 0;
    let mut v___x_2158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2163_: u8 = 0;
    let mut v_unused_2164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2168_: u8 = 0;
    let mut v___x_2169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: u8 = 0;
    let mut v___x_2172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: u8 = 0;
    let mut v___x_2174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2169_ = leanh::lean_unsigned_to_nat(3);
                v___x_2170_ = lean_nat_sub(v_stop_2143_, v_start_2142_);
                v___x_2171_ = lean_nat_dec_le(v___x_2169_, v___x_2170_);
                leanh::lean_dec(v___x_2170_);
                if v___x_2171_ == 0 {
                    v___y_2145_ = v___x_2171_;
                    state = 1;
                    continue;
                } else {
                    v___x_2172_ = lean_array_get_size(v_comps_2141_);
                    v___x_2173_ = lean_nat_dec_lt(v_start_2142_, v___x_2172_);
                    if v___x_2173_ == 0 {
                        v___x_2174_ = leanh::lean_box(0);
                        v___y_2166_ = v___x_2174_;
                        state = 4;
                        continue;
                    } else {
                        v___x_2175_ = lean_array_fget_borrowed(v_comps_2141_, v_start_2142_);
                        leanh::lean_inc(v___x_2175_);
                        v___x_2176_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2176_, 0, v___x_2175_);
                        v___y_2166_ = v___x_2176_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_2145_ == 0 {
                    leanh::lean_dec(v_stop_2143_);
                    v___x_2146_ = leanh::lean_box((v___y_2145_) as usize);
                    v___x_2147_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2147_, 0, v_start_2142_);
                    leanh::lean_ctor_set(v___x_2147_, 1, v___x_2146_);
                    return v___x_2147_;
                } else {
                    v___x_2148_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2149_ = lean_nat_add(v_start_2142_, v___x_2148_);
                    leanh::lean_inc(v_stop_2143_);
                    leanh::lean_inc(v___x_2149_);
                    v___x_2150_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_2150_, 0, v___x_2149_);
                    leanh::lean_ctor_set(v___x_2150_, 1, v_stop_2143_);
                    leanh::lean_ctor_set(v___x_2150_, 2, v___x_2148_);
                    v___x_2151_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg___closed__0;
                    leanh::lean_inc(v_start_2142_);
                    v___x_2152_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg(v_stop_2143_, v_start_2142_, v___y_2145_, v_comps_2141_, v___x_2150_, v___x_2151_, v___x_2149_);
                    leanh::lean_dec_ref_known(v___x_2150_, 3);
                    leanh::lean_dec(v_stop_2143_);
                    v_fst_2153_ = leanh::lean_ctor_get(v___x_2152_, 0);
                    v_isSharedCheck_2163_ = (!leanh::lean_is_exclusive(v___x_2152_)) as u8;
                    if v_isSharedCheck_2163_ == 0 {
                        v_unused_2164_ = leanh::lean_ctor_get(v___x_2152_, 1);
                        leanh::lean_dec(v_unused_2164_);
                        v___x_2155_ = v___x_2152_;
                        v_isShared_2156_ = v_isSharedCheck_2163_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_fst_2153_);
                        leanh::lean_dec(v___x_2152_);
                        v___x_2155_ = leanh::lean_box(0);
                        v_isShared_2156_ = v_isSharedCheck_2163_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if leanh::lean_obj_tag(v_fst_2153_) == 0 {
                    v___x_2157_ = 0;
                    v___x_2158_ = leanh::lean_box((v___x_2157_) as usize);
                    if v_isShared_2156_ == 0 {
                        leanh::lean_ctor_set(v___x_2155_, 1, v___x_2158_);
                        leanh::lean_ctor_set(v___x_2155_, 0, v_start_2142_);
                        v___x_2160_ = v___x_2155_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2161_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2161_, 0, v_start_2142_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2161_, 1, v___x_2158_);
                        v___x_2160_ = v_reuseFailAlloc_2161_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2155_);
                    leanh::lean_dec(v_start_2142_);
                    v_val_2162_ = leanh::lean_ctor_get(v_fst_2153_, 0);
                    leanh::lean_inc(v_val_2162_);
                    leanh::lean_dec_ref_known(v_fst_2153_, 1);
                    return v_val_2162_;
                }
            }
            3 => {
                return v___x_2160_;
            }
            4 => {
                v___x_2167_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate___closed__2;
                v___x_2168_ = l_Option_instBEq_beq___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__0(v___y_2166_, v___x_2167_);
                leanh::lean_dec(v___y_2166_);
                v___y_2145_ = v___x_2168_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate___boxed(
    mut v_comps_2177_: *mut leanh::LeanObject,
    mut v_start_2178_: *mut leanh::LeanObject,
    mut v_stop_2179_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2180_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2180_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate(
        v_comps_2177_,
        v_start_2178_,
        v_stop_2179_,
    );
    leanh::lean_dec_ref(v_comps_2177_);
    return v_res_2180_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1(
    mut v_stop_2181_: *mut leanh::LeanObject,
    mut v_start_2182_: *mut leanh::LeanObject,
    mut v___y_2183_: u8,
    mut v_comps_2184_: *mut leanh::LeanObject,
    mut v_range_2185_: *mut leanh::LeanObject,
    mut v_b_2186_: *mut leanh::LeanObject,
    mut v_i_2187_: *mut leanh::LeanObject,
    mut v_hs_2188_: *mut leanh::LeanObject,
    mut v_hl_2189_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2190_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2190_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg(v_stop_2181_, v_start_2182_, v___y_2183_, v_comps_2184_, v_range_2185_, v_b_2186_, v_i_2187_);
    return v___x_2190_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___boxed(
    mut v_stop_2191_: *mut leanh::LeanObject,
    mut v_start_2192_: *mut leanh::LeanObject,
    mut v___y_2193_: *mut leanh::LeanObject,
    mut v_comps_2194_: *mut leanh::LeanObject,
    mut v_range_2195_: *mut leanh::LeanObject,
    mut v_b_2196_: *mut leanh::LeanObject,
    mut v_i_2197_: *mut leanh::LeanObject,
    mut v_hs_2198_: *mut leanh::LeanObject,
    mut v_hl_2199_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1088__boxed_2200_: u8 = 0;
    let mut v_res_2201_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_1088__boxed_2200_ = (leanh::lean_unbox(v___y_2193_) as u8);
    v_res_2201_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1(v_stop_2191_, v_start_2192_, v___y_1088__boxed_2200_, v_comps_2194_, v_range_2195_, v_b_2196_, v_i_2197_, v_hs_2198_, v_hl_2199_);
    leanh::lean_dec_ref(v_b_2196_);
    leanh::lean_dec_ref(v_range_2195_);
    leanh::lean_dec_ref(v_comps_2194_);
    leanh::lean_dec(v_stop_2191_);
    return v_res_2201_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__2___redArg(
    mut v___x_2202_: *mut leanh::LeanObject,
    mut v_comps_2203_: *mut leanh::LeanObject,
    mut v_range_2204_: *mut leanh::LeanObject,
    mut v_b_2205_: *mut leanh::LeanObject,
    mut v_i_2206_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_stop_2207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_step_2208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: u8 = 0;
    let mut v___x_2210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2212_: u8 = 0;
    let mut v___x_2213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: u8 = 0;
    let mut v___x_2220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: u8 = 0;
    let mut v___x_2222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: u8 = 0;
    let mut v___x_2224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stop_2207_ = leanh::lean_ctor_get(v_range_2204_, 1);
                v_step_2208_ = leanh::lean_ctor_get(v_range_2204_, 2);
                v___x_2209_ = lean_nat_dec_lt(v_i_2206_, v_stop_2207_);
                if v___x_2209_ == 0 {
                    leanh::lean_dec(v_i_2206_);
                    leanh::lean_inc(v_b_2205_);
                    return v_b_2205_;
                } else {
                    v___x_2210_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2222_ = lean_array_get_size(v_comps_2203_);
                    v___x_2223_ = lean_nat_dec_lt(v_i_2206_, v___x_2222_);
                    if v___x_2223_ == 0 {
                        v___x_2224_ = leanh::lean_box(0);
                        v___y_2217_ = v___x_2224_;
                        state = 2;
                        continue;
                    } else {
                        v___x_2225_ = lean_array_fget_borrowed(v_comps_2203_, v_i_2206_);
                        leanh::lean_inc(v___x_2225_);
                        v___x_2226_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2226_, 0, v___x_2225_);
                        v___y_2217_ = v___x_2226_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_2212_ == 0 {
                    v___x_2213_ = lean_nat_add(v_i_2206_, v_step_2208_);
                    leanh::lean_dec(v_i_2206_);
                    v_i_2206_ = v___x_2213_;
                    state = 0;
                    continue;
                } else {
                    v___x_2215_ = lean_nat_add(v_i_2206_, v___x_2210_);
                    leanh::lean_dec(v_i_2206_);
                    return v___x_2215_;
                }
            }
            2 => {
                v___x_2218_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg___closed__2;
                v___x_2219_ = l_Option_instBEq_beq___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__0(v___y_2217_, v___x_2218_);
                leanh::lean_dec(v___y_2217_);
                if v___x_2219_ == 0 {
                    v___y_2212_ = v___x_2219_;
                    state = 1;
                    continue;
                } else {
                    v___x_2220_ = lean_nat_add(v_i_2206_, v___x_2210_);
                    v___x_2221_ = lean_nat_dec_lt(v___x_2220_, v___x_2202_);
                    leanh::lean_dec(v___x_2220_);
                    v___y_2212_ = v___x_2221_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__2___redArg___boxed(
    mut v___x_2227_: *mut leanh::LeanObject,
    mut v_comps_2228_: *mut leanh::LeanObject,
    mut v_range_2229_: *mut leanh::LeanObject,
    mut v_b_2230_: *mut leanh::LeanObject,
    mut v_i_2231_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2232_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2232_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__2___redArg(v___x_2227_, v_comps_2228_, v_range_2229_, v_b_2230_, v_i_2231_);
    leanh::lean_dec(v_b_2230_);
    leanh::lean_dec_ref(v_range_2229_);
    leanh::lean_dec_ref(v_comps_2228_);
    leanh::lean_dec(v___x_2227_);
    return v_res_2232_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__0_spec__0(
    mut v_a_2233_: *mut leanh::LeanObject,
    mut v_as_2234_: *mut leanh::LeanObject,
    mut v_i_2235_: usize,
    mut v_stop_2236_: usize,
) -> u8 {
    let mut v___x_2237_: u8 = 0;
    let mut v___x_2238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: u8 = 0;
    let mut v___x_2240_: usize = 0;
    let mut v___x_2241_: usize = 0;
    let mut v___x_2243_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2237_ = lean_usize_dec_eq(v_i_2235_, v_stop_2236_);
                if v___x_2237_ == 0 {
                    v___x_2238_ = lean_array_uget_borrowed(v_as_2234_, v_i_2235_);
                    v___x_2239_ = lean_string_dec_eq(v_a_2233_, v___x_2238_);
                    if v___x_2239_ == 0 {
                        v___x_2240_ = 1usize;
                        v___x_2241_ = lean_usize_add(v_i_2235_, v___x_2240_);
                        v_i_2235_ = v___x_2241_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2239_;
                    }
                } else {
                    v___x_2243_ = 0;
                    return v___x_2243_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__0_spec__0___boxed(
    mut v_a_2244_: *mut leanh::LeanObject,
    mut v_as_2245_: *mut leanh::LeanObject,
    mut v_i_2246_: *mut leanh::LeanObject,
    mut v_stop_2247_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2248_: usize = 0;
    let mut v_stop_boxed_2249_: usize = 0;
    let mut v_res_2250_: u8 = 0;
    let mut v_r_2251_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2248_ = leanh::lean_unbox_usize(v_i_2246_);
    leanh::lean_dec(v_i_2246_);
    v_stop_boxed_2249_ = leanh::lean_unbox_usize(v_stop_2247_);
    leanh::lean_dec(v_stop_2247_);
    v_res_2250_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__0_spec__0(v_a_2244_, v_as_2245_, v_i_boxed_2248_, v_stop_boxed_2249_);
    leanh::lean_dec_ref(v_as_2245_);
    leanh::lean_dec_ref(v_a_2244_);
    v_r_2251_ = leanh::lean_box((v_res_2250_) as usize);
    return v_r_2251_;
}
pub unsafe fn l_Array_contains___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__0(
    mut v_as_2252_: *mut leanh::LeanObject,
    mut v_a_2253_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: u8 = 0;
    v___x_2254_ = leanh::lean_unsigned_to_nat(0);
    v___x_2255_ = lean_array_get_size(v_as_2252_);
    v___x_2256_ = lean_nat_dec_lt(v___x_2254_, v___x_2255_);
    if v___x_2256_ == 0 {
        return v___x_2256_;
    } else {
        if v___x_2256_ == 0 {
            return v___x_2256_;
        } else {
            let mut v___x_2257_: usize = 0;
            let mut v___x_2258_: usize = 0;
            let mut v___x_2259_: u8 = 0;
            v___x_2257_ = 0usize;
            v___x_2258_ = lean_usize_of_nat(v___x_2255_);
            v___x_2259_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__0_spec__0(v_a_2253_, v_as_2252_, v___x_2257_, v___x_2258_);
            return v___x_2259_;
        }
    }
}
pub unsafe fn l_Array_contains___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__0___boxed(
    mut v_as_2260_: *mut leanh::LeanObject,
    mut v_a_2261_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2262_: u8 = 0;
    let mut v_r_2263_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2262_ = l_Array_contains___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__0(v_as_2260_, v_a_2261_);
    leanh::lean_dec_ref(v_a_2261_);
    leanh::lean_dec_ref(v_as_2260_);
    v_r_2263_ = leanh::lean_box((v_res_2262_) as usize);
    return v_r_2263_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__1___redArg(
    mut v_comps_2264_: *mut leanh::LeanObject,
    mut v_range_2265_: *mut leanh::LeanObject,
    mut v_b_2266_: *mut leanh::LeanObject,
    mut v_i_2267_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_stop_2268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_step_2269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: u8 = 0;
    let mut v_fst_2275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2279_: u8 = 0;
    let mut v___x_2280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: u8 = 0;
    let mut v___x_2284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: u8 = 0;
    let mut v___x_2293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2300_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stop_2268_ = leanh::lean_ctor_get(v_range_2265_, 1);
                v_step_2269_ = leanh::lean_ctor_get(v_range_2265_, 2);
                v___x_2274_ = lean_nat_dec_lt(v_i_2267_, v_stop_2268_);
                if v___x_2274_ == 0 {
                    leanh::lean_dec(v_i_2267_);
                    return v_b_2266_;
                } else {
                    v_fst_2275_ = leanh::lean_ctor_get(v_b_2266_, 0);
                    v_snd_2276_ = leanh::lean_ctor_get(v_b_2266_, 1);
                    v_isSharedCheck_2300_ = (!leanh::lean_is_exclusive(v_b_2266_)) as u8;
                    if v_isSharedCheck_2300_ == 0 {
                        v___x_2278_ = v_b_2266_;
                        v_isShared_2279_ = v_isSharedCheck_2300_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2276_);
                        leanh::lean_inc(v_fst_2275_);
                        leanh::lean_dec(v_b_2266_);
                        v___x_2278_ = leanh::lean_box(0);
                        v_isShared_2279_ = v_isSharedCheck_2300_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2272_ = lean_nat_add(v_i_2267_, v_step_2269_);
                leanh::lean_dec(v_i_2267_);
                v_b_2266_ = v_a_2271_;
                v_i_2267_ = v___x_2272_;
                state = 0;
                continue;
            }
            2 => {
                v___x_2280_ = l_Lean_instInhabitedNamePart_default;
                v___x_2281_ = lean_array_get_borrowed(v___x_2280_, v_comps_2264_, v_i_2267_);
                leanh::lean_inc(v___x_2281_);
                v___x_2282_ =
                    l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix(
                        v___x_2281_,
                    );
                if leanh::lean_obj_tag(v___x_2282_) == 0 {
                    leanh::lean_inc(v___x_2281_);
                    v___x_2283_ =
                        l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isSpecIndex(
                            v___x_2281_,
                        );
                    if v___x_2283_ == 0 {
                        leanh::lean_inc(v___x_2281_);
                        v___x_2284_ = lean_array_push(v_fst_2275_, v___x_2281_);
                        if v_isShared_2279_ == 0 {
                            leanh::lean_ctor_set(v___x_2278_, 0, v___x_2284_);
                            v___x_2286_ = v___x_2278_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2287_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2287_, 0, v___x_2284_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2287_, 1, v_snd_2276_);
                            v___x_2286_ = v_reuseFailAlloc_2287_;
                            state = 3;
                            continue;
                        }
                    } else {
                        if v_isShared_2279_ == 0 {
                            v___x_2289_ = v___x_2278_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2290_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2290_, 0, v_fst_2275_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2290_, 1, v_snd_2276_);
                            v___x_2289_ = v_reuseFailAlloc_2290_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_val_2291_ = leanh::lean_ctor_get(v___x_2282_, 0);
                    leanh::lean_inc(v_val_2291_);
                    leanh::lean_dec_ref_known(v___x_2282_, 1);
                    v___x_2292_ = l_Array_contains___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__0(v_snd_2276_, v_val_2291_);
                    if v___x_2292_ == 0 {
                        v___x_2293_ = lean_array_push(v_snd_2276_, v_val_2291_);
                        if v_isShared_2279_ == 0 {
                            leanh::lean_ctor_set(v___x_2278_, 1, v___x_2293_);
                            v___x_2295_ = v___x_2278_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_2296_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2296_, 0, v_fst_2275_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2296_, 1, v___x_2293_);
                            v___x_2295_ = v_reuseFailAlloc_2296_;
                            state = 5;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_val_2291_);
                        if v_isShared_2279_ == 0 {
                            v___x_2298_ = v___x_2278_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_2299_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2299_, 0, v_fst_2275_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2299_, 1, v_snd_2276_);
                            v___x_2298_ = v_reuseFailAlloc_2299_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            3 => {
                v_a_2271_ = v___x_2286_;
                state = 1;
                continue;
            }
            4 => {
                v_a_2271_ = v___x_2289_;
                state = 1;
                continue;
            }
            5 => {
                v_a_2271_ = v___x_2295_;
                state = 1;
                continue;
            }
            6 => {
                v_a_2271_ = v___x_2298_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__1___redArg___boxed(
    mut v_comps_2301_: *mut leanh::LeanObject,
    mut v_range_2302_: *mut leanh::LeanObject,
    mut v_b_2303_: *mut leanh::LeanObject,
    mut v_i_2304_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2305_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2305_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__1___redArg(v_comps_2301_, v_range_2302_, v_b_2303_, v_i_2304_);
    leanh::lean_dec_ref(v_range_2302_);
    leanh::lean_dec_ref(v_comps_2301_);
    return v_res_2305_;
}
pub unsafe fn l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext(
    mut v_comps_2310_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_begin___2312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2322_: u8 = 0;
    let mut v___x_2323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2327_: u8 = 0;
    let mut v_begin___2328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2332_: u8 = 0;
    let mut v___x_2333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2339_: u8 = 0;
    let mut v___x_2340_: u8 = 0;
    let mut v___x_2341_: u8 = 0;
    let mut v___x_2342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_begin___2328_ = leanh::lean_unsigned_to_nat(0);
                v___x_2329_ = leanh::lean_unsigned_to_nat(3);
                v___x_2330_ = lean_array_get_size(v_comps_2310_);
                v___x_2340_ = lean_nat_dec_le(v___x_2329_, v___x_2330_);
                if v___x_2340_ == 0 {
                    v___y_2332_ = v___x_2340_;
                    state = 4;
                    continue;
                } else {
                    v___x_2341_ = lean_nat_dec_lt(v_begin___2328_, v___x_2330_);
                    if v___x_2341_ == 0 {
                        v___x_2342_ = leanh::lean_box(0);
                        v___y_2337_ = v___x_2342_;
                        state = 5;
                        continue;
                    } else {
                        v___x_2343_ = lean_array_fget_borrowed(v_comps_2310_, v_begin___2328_);
                        leanh::lean_inc(v___x_2343_);
                        v___x_2344_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2344_, 0, v___x_2343_);
                        v___y_2337_ = v___x_2344_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2313_ = lean_array_get_size(v_comps_2310_);
                v___x_2314_ = leanh::lean_unsigned_to_nat(1);
                leanh::lean_inc(v_begin___2312_);
                v___x_2315_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2315_, 0, v_begin___2312_);
                leanh::lean_ctor_set(v___x_2315_, 1, v___x_2313_);
                leanh::lean_ctor_set(v___x_2315_, 2, v___x_2314_);
                v___x_2316_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext___closed__1;
                v___x_2317_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__1___redArg(v_comps_2310_, v___x_2315_, v___x_2316_, v_begin___2312_);
                leanh::lean_dec_ref_known(v___x_2315_, 3);
                v_fst_2318_ = leanh::lean_ctor_get(v___x_2317_, 0);
                v_snd_2319_ = leanh::lean_ctor_get(v___x_2317_, 1);
                v_isSharedCheck_2327_ = (!leanh::lean_is_exclusive(v___x_2317_)) as u8;
                if v_isSharedCheck_2327_ == 0 {
                    v___x_2321_ = v___x_2317_;
                    v_isShared_2322_ = v_isSharedCheck_2327_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_2319_);
                    leanh::lean_inc(v_fst_2318_);
                    leanh::lean_dec(v___x_2317_);
                    v___x_2321_ = leanh::lean_box(0);
                    v_isShared_2322_ = v_isSharedCheck_2327_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2323_ =
                    l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts(
                        v_fst_2318_,
                    );
                leanh::lean_dec(v_fst_2318_);
                if v_isShared_2322_ == 0 {
                    leanh::lean_ctor_set(v___x_2321_, 0, v___x_2323_);
                    v___x_2325_ = v___x_2321_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2326_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2326_, 0, v___x_2323_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2326_, 1, v_snd_2319_);
                    v___x_2325_ = v_reuseFailAlloc_2326_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2325_;
            }
            4 => {
                if v___y_2332_ == 0 {
                    v_begin___2312_ = v_begin___2328_;
                    state = 1;
                    continue;
                } else {
                    v___x_2333_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2334_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_2334_, 0, v___x_2333_);
                    leanh::lean_ctor_set(v___x_2334_, 1, v___x_2330_);
                    leanh::lean_ctor_set(v___x_2334_, 2, v___x_2333_);
                    v___x_2335_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__2___redArg(v___x_2330_, v_comps_2310_, v___x_2334_, v_begin___2328_, v___x_2333_);
                    leanh::lean_dec_ref_known(v___x_2334_, 3);
                    v_begin___2312_ = v___x_2335_;
                    state = 1;
                    continue;
                }
            }
            5 => {
                v___x_2338_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate___closed__2;
                v___x_2339_ = l_Option_instBEq_beq___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__0(v___y_2337_, v___x_2338_);
                leanh::lean_dec(v___y_2337_);
                v___y_2332_ = v___x_2339_;
                state = 4;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext___boxed(
    mut v_comps_2345_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2346_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2346_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext(
        v_comps_2345_,
    );
    leanh::lean_dec_ref(v_comps_2345_);
    return v_res_2346_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__1(
    mut v_comps_2347_: *mut leanh::LeanObject,
    mut v_range_2348_: *mut leanh::LeanObject,
    mut v_b_2349_: *mut leanh::LeanObject,
    mut v_i_2350_: *mut leanh::LeanObject,
    mut v_hs_2351_: *mut leanh::LeanObject,
    mut v_hl_2352_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2353_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2353_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__1___redArg(v_comps_2347_, v_range_2348_, v_b_2349_, v_i_2350_);
    return v___x_2353_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__1___boxed(
    mut v_comps_2354_: *mut leanh::LeanObject,
    mut v_range_2355_: *mut leanh::LeanObject,
    mut v_b_2356_: *mut leanh::LeanObject,
    mut v_i_2357_: *mut leanh::LeanObject,
    mut v_hs_2358_: *mut leanh::LeanObject,
    mut v_hl_2359_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2360_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2360_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__1(v_comps_2354_, v_range_2355_, v_b_2356_, v_i_2357_, v_hs_2358_, v_hl_2359_);
    leanh::lean_dec_ref(v_range_2355_);
    leanh::lean_dec_ref(v_comps_2354_);
    return v_res_2360_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__2(
    mut v___x_2361_: *mut leanh::LeanObject,
    mut v_comps_2362_: *mut leanh::LeanObject,
    mut v_range_2363_: *mut leanh::LeanObject,
    mut v_b_2364_: *mut leanh::LeanObject,
    mut v_i_2365_: *mut leanh::LeanObject,
    mut v_hs_2366_: *mut leanh::LeanObject,
    mut v_hl_2367_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2368_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2368_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__2___redArg(v___x_2361_, v_comps_2362_, v_range_2363_, v_b_2364_, v_i_2365_);
    return v___x_2368_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__2___boxed(
    mut v___x_2369_: *mut leanh::LeanObject,
    mut v_comps_2370_: *mut leanh::LeanObject,
    mut v_range_2371_: *mut leanh::LeanObject,
    mut v_b_2372_: *mut leanh::LeanObject,
    mut v_i_2373_: *mut leanh::LeanObject,
    mut v_hs_2374_: *mut leanh::LeanObject,
    mut v_hl_2375_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2376_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2376_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__2(v___x_2369_, v_comps_2370_, v_range_2371_, v_b_2372_, v_i_2373_, v_hs_2374_, v_hl_2375_);
    leanh::lean_dec(v_b_2372_);
    leanh::lean_dec_ref(v_range_2371_);
    leanh::lean_dec_ref(v_comps_2370_);
    leanh::lean_dec(v___x_2369_);
    return v_res_2376_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___redArg(
    mut v___x_2380_: *mut leanh::LeanObject,
    mut v_range_2381_: *mut leanh::LeanObject,
    mut v_b_2382_: *mut leanh::LeanObject,
    mut v_i_2383_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_stop_2384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_step_2385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: u8 = 0;
    let mut v___x_2387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: u8 = 0;
    let mut v___x_2391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stop_2384_ = leanh::lean_ctor_get(v_range_2381_, 1);
                v_step_2385_ = leanh::lean_ctor_get(v_range_2381_, 2);
                v___x_2386_ = lean_nat_dec_lt(v_i_2383_, v_stop_2384_);
                if v___x_2386_ == 0 {
                    leanh::lean_dec(v_i_2383_);
                    leanh::lean_inc(v_b_2382_);
                    return v_b_2382_;
                } else {
                    v___x_2387_ = l_Lean_instInhabitedNamePart_default;
                    v___x_2388_ = lean_array_get_borrowed(v___x_2387_, v___x_2380_, v_i_2383_);
                    v___x_2389_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___redArg___closed__1;
                    v___x_2390_ = l_Lean_instBEqNamePart_beq(v___x_2388_, v___x_2389_);
                    if v___x_2390_ == 0 {
                        v___x_2391_ = lean_nat_add(v_i_2383_, v_step_2385_);
                        leanh::lean_dec(v_i_2383_);
                        v_i_2383_ = v___x_2391_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2393_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2393_, 0, v_i_2383_);
                        return v___x_2393_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___redArg___boxed(
    mut v___x_2394_: *mut leanh::LeanObject,
    mut v_range_2395_: *mut leanh::LeanObject,
    mut v_b_2396_: *mut leanh::LeanObject,
    mut v_i_2397_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2398_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2398_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___redArg(v___x_2394_, v_range_2395_, v_b_2396_, v_i_2397_);
    leanh::lean_dec(v_b_2396_);
    leanh::lean_dec_ref(v_range_2395_);
    leanh::lean_dec_ref(v___x_2394_);
    return v_res_2398_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__5(
    mut v___x_2399_: *mut leanh::LeanObject,
    mut v_as_2400_: *mut leanh::LeanObject,
    mut v_sz_2401_: usize,
    mut v_i_2402_: usize,
    mut v_b_2403_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: usize = 0;
    let mut v___x_2407_: usize = 0;
    let mut v___x_2409_: u8 = 0;
    let mut v_a_2410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_flags_2415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2418_: u8 = 0;
    let mut v___x_2419_: u8 = 0;
    let mut v___x_2420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2409_ = lean_usize_dec_lt(v_i_2402_, v_sz_2401_);
                if v___x_2409_ == 0 {
                    return v_b_2403_;
                } else {
                    v_a_2410_ = lean_array_uget_borrowed(v_as_2400_, v_i_2402_);
                    v___x_2411_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext(v_a_2410_);
                    v_name_2414_ = leanh::lean_ctor_get(v___x_2411_, 0);
                    leanh::lean_inc_ref(v_name_2414_);
                    v_flags_2415_ = leanh::lean_ctor_get(v___x_2411_, 1);
                    leanh::lean_inc_ref(v_flags_2415_);
                    v___x_2416_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2417_ = lean_string_utf8_byte_size(v_name_2414_);
                    leanh::lean_dec_ref(v_name_2414_);
                    v___x_2418_ = lean_nat_dec_eq(v___x_2417_, v___x_2416_);
                    if v___x_2418_ == 0 {
                        leanh::lean_dec_ref(v_flags_2415_);
                        state = 2;
                        continue;
                    } else {
                        v___x_2419_ = lean_nat_dec_eq(v___x_2399_, v___x_2416_);
                        if v___x_2419_ == 0 {
                            v___x_2420_ = lean_array_get_size(v_flags_2415_);
                            leanh::lean_dec_ref(v_flags_2415_);
                            v___x_2421_ = lean_nat_dec_eq(v___x_2420_, v___x_2416_);
                            if v___x_2421_ == 0 {
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_dec_ref(v___x_2411_);
                                v_a_2405_ = v_b_2403_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v_flags_2415_);
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2406_ = 1usize;
                v___x_2407_ = lean_usize_add(v_i_2402_, v___x_2406_);
                v_i_2402_ = v___x_2407_;
                v_b_2403_ = v_a_2405_;
                state = 0;
                continue;
            }
            2 => {
                v___x_2413_ = lean_array_push(v_b_2403_, v___x_2411_);
                v_a_2405_ = v___x_2413_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__5___boxed(
    mut v___x_2422_: *mut leanh::LeanObject,
    mut v_as_2423_: *mut leanh::LeanObject,
    mut v_sz_2424_: *mut leanh::LeanObject,
    mut v_i_2425_: *mut leanh::LeanObject,
    mut v_b_2426_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2427_: usize = 0;
    let mut v_i_boxed_2428_: usize = 0;
    let mut v_res_2429_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2427_ = leanh::lean_unbox_usize(v_sz_2424_);
    leanh::lean_dec(v_sz_2424_);
    v_i_boxed_2428_ = leanh::lean_unbox_usize(v_i_2425_);
    leanh::lean_dec(v_i_2425_);
    v_res_2429_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__5(v___x_2422_, v_as_2423_, v_sz_boxed_2427_, v_i_boxed_2428_, v_b_2426_);
    leanh::lean_dec_ref(v_as_2423_);
    leanh::lean_dec(v___x_2422_);
    return v_res_2429_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__0___redArg(
    mut v___x_2430_: *mut leanh::LeanObject,
    mut v_a_2431_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_snd_2432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2436_: u8 = 0;
    let mut v_fst_2437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2441_: u8 = 0;
    let mut v___x_2444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: u8 = 0;
    let mut v___x_2450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: u8 = 0;
    let mut v___x_2453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: u8 = 0;
    let mut v___x_2461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: u8 = 0;
    let mut v_isSharedCheck_2491_: u8 = 0;
    let mut v_isSharedCheck_2492_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_2432_ = leanh::lean_ctor_get(v_a_2431_, 1);
                v_fst_2433_ = leanh::lean_ctor_get(v_a_2431_, 0);
                v_isSharedCheck_2492_ = (!leanh::lean_is_exclusive(v_a_2431_)) as u8;
                if v_isSharedCheck_2492_ == 0 {
                    v___x_2435_ = v_a_2431_;
                    v_isShared_2436_ = v_isSharedCheck_2492_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_2432_);
                    leanh::lean_inc(v_fst_2433_);
                    leanh::lean_dec(v_a_2431_);
                    v___x_2435_ = leanh::lean_box(0);
                    v_isShared_2436_ = v_isSharedCheck_2492_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_2437_ = leanh::lean_ctor_get(v_snd_2432_, 0);
                v_snd_2438_ = leanh::lean_ctor_get(v_snd_2432_, 1);
                v_isSharedCheck_2491_ = (!leanh::lean_is_exclusive(v_snd_2432_)) as u8;
                if v_isSharedCheck_2491_ == 0 {
                    v___x_2440_ = v_snd_2432_;
                    v_isShared_2441_ = v_isSharedCheck_2491_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_2438_);
                    leanh::lean_inc(v_fst_2437_);
                    leanh::lean_dec(v_snd_2432_);
                    v___x_2440_ = leanh::lean_box(0);
                    v_isShared_2441_ = v_isSharedCheck_2491_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2449_ = (leanh::lean_unbox(v_snd_2438_) as u8);
                if v___x_2449_ == 0 {
                    state = 3;
                    continue;
                } else {
                    v___x_2450_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2451_ = lean_nat_dec_eq(v___x_2430_, v___x_2450_);
                    v___x_2489_ = lean_array_get_size(v_fst_2433_);
                    v___x_2490_ = lean_nat_dec_eq(v___x_2489_, v___x_2450_);
                    if v___x_2490_ == 0 {
                        leanh::lean_del_object(v___x_2440_);
                        leanh::lean_del_object(v___x_2435_);
                        state = 6;
                        continue;
                    } else {
                        if v___x_2451_ == 0 {
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_del_object(v___x_2440_);
                            leanh::lean_del_object(v___x_2435_);
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            3 => {
                if v_isShared_2441_ == 0 {
                    v___x_2444_ = v___x_2440_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2448_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2448_, 0, v_fst_2437_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2448_, 1, v_snd_2438_);
                    v___x_2444_ = v_reuseFailAlloc_2448_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2436_ == 0 {
                    leanh::lean_ctor_set(v___x_2435_, 1, v___x_2444_);
                    v___x_2446_ = v___x_2435_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2447_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2447_, 0, v_fst_2433_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2447_, 1, v___x_2444_);
                    v___x_2446_ = v_reuseFailAlloc_2447_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2446_;
            }
            6 => {
                v___x_2453_ = l_Lean_instInhabitedNamePart_default;
                v___x_2454_ = lean_array_get_size(v_fst_2433_);
                v___x_2455_ = leanh::lean_unsigned_to_nat(1);
                v___x_2456_ = lean_nat_sub(v___x_2454_, v___x_2455_);
                v___x_2457_ = lean_array_get_borrowed(v___x_2453_, v_fst_2433_, v___x_2456_);
                leanh::lean_dec(v___x_2456_);
                leanh::lean_inc(v___x_2457_);
                v___x_2458_ =
                    l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix(
                        v___x_2457_,
                    );
                if leanh::lean_obj_tag(v___x_2458_) == 0 {
                    if leanh::lean_obj_tag(v___x_2457_) == 1 {
                        v___x_2459_ = leanh::lean_unsigned_to_nat(2);
                        v___x_2460_ = lean_nat_dec_le(v___x_2459_, v___x_2454_);
                        if v___x_2460_ == 0 {
                            leanh::lean_dec(v_snd_2438_);
                            v___x_2461_ = leanh::lean_box((v___x_2451_) as usize);
                            v___x_2462_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_2462_, 0, v_fst_2437_);
                            leanh::lean_ctor_set(v___x_2462_, 1, v___x_2461_);
                            v___x_2463_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_2463_, 0, v_fst_2433_);
                            leanh::lean_ctor_set(v___x_2463_, 1, v___x_2462_);
                            v_a_2431_ = v___x_2463_;
                            state = 0;
                            continue;
                        } else {
                            v___x_2465_ = lean_nat_sub(v___x_2454_, v___x_2459_);
                            v___x_2466_ =
                                lean_array_get_borrowed(v___x_2453_, v_fst_2433_, v___x_2465_);
                            leanh::lean_dec(v___x_2465_);
                            leanh::lean_inc(v___x_2466_);
                            v___x_2467_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix(v___x_2466_);
                            if leanh::lean_obj_tag(v___x_2467_) == 0 {
                                leanh::lean_dec(v_snd_2438_);
                                v___x_2468_ = leanh::lean_box((v___x_2451_) as usize);
                                v___x_2469_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_2469_, 0, v_fst_2437_);
                                leanh::lean_ctor_set(v___x_2469_, 1, v___x_2468_);
                                v___x_2470_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_2470_, 0, v_fst_2433_);
                                leanh::lean_ctor_set(v___x_2470_, 1, v___x_2469_);
                                v_a_2431_ = v___x_2470_;
                                state = 0;
                                continue;
                            } else {
                                v_val_2472_ = leanh::lean_ctor_get(v___x_2467_, 0);
                                leanh::lean_inc(v_val_2472_);
                                leanh::lean_dec_ref_known(v___x_2467_, 1);
                                v___x_2473_ = lean_array_push(v_fst_2437_, v_val_2472_);
                                v___x_2474_ = lean_array_pop(v_fst_2433_);
                                v___x_2475_ = lean_array_pop(v___x_2474_);
                                v___x_2476_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_2476_, 0, v___x_2473_);
                                leanh::lean_ctor_set(v___x_2476_, 1, v_snd_2438_);
                                v___x_2477_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_2477_, 0, v___x_2475_);
                                leanh::lean_ctor_set(v___x_2477_, 1, v___x_2476_);
                                v_a_2431_ = v___x_2477_;
                                state = 0;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_snd_2438_);
                        v___x_2479_ = leanh::lean_box((v___x_2451_) as usize);
                        v___x_2480_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2480_, 0, v_fst_2437_);
                        leanh::lean_ctor_set(v___x_2480_, 1, v___x_2479_);
                        v___x_2481_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2481_, 0, v_fst_2433_);
                        leanh::lean_ctor_set(v___x_2481_, 1, v___x_2480_);
                        v_a_2431_ = v___x_2481_;
                        state = 0;
                        continue;
                    }
                } else {
                    v_val_2483_ = leanh::lean_ctor_get(v___x_2458_, 0);
                    leanh::lean_inc(v_val_2483_);
                    leanh::lean_dec_ref_known(v___x_2458_, 1);
                    v___x_2484_ = lean_array_push(v_fst_2437_, v_val_2483_);
                    v___x_2485_ = lean_array_pop(v_fst_2433_);
                    v___x_2486_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2486_, 0, v___x_2484_);
                    leanh::lean_ctor_set(v___x_2486_, 1, v_snd_2438_);
                    v___x_2487_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2487_, 0, v___x_2485_);
                    leanh::lean_ctor_set(v___x_2487_, 1, v___x_2486_);
                    v_a_2431_ = v___x_2487_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__0___redArg___boxed(
    mut v___x_2493_: *mut leanh::LeanObject,
    mut v_a_2494_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2495_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2495_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__0___redArg(v___x_2493_, v_a_2494_);
    leanh::lean_dec(v___x_2493_);
    return v_res_2495_;
}
pub unsafe fn _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2498_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2497_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg___closed__0;
    v___x_2498_ = lean_string_utf8_byte_size(v___x_2497_);
    return v___x_2498_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg(
    mut v___x_2499_: *mut leanh::LeanObject,
    mut v_range_2500_: *mut leanh::LeanObject,
    mut v_b_2501_: *mut leanh::LeanObject,
    mut v_i_2502_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_stop_2503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_step_2504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: u8 = 0;
    let mut v___x_2510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_2512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2515_: u8 = 0;
    let mut v___x_2516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2520_: u8 = 0;
    let mut v___x_2521_: u8 = 0;
    let mut v___x_2522_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stop_2503_ = leanh::lean_ctor_get(v_range_2500_, 1);
                v_step_2504_ = leanh::lean_ctor_get(v_range_2500_, 2);
                v___x_2509_ = lean_nat_dec_lt(v_i_2502_, v_stop_2503_);
                if v___x_2509_ == 0 {
                    leanh::lean_dec(v_i_2502_);
                    leanh::lean_inc_ref(v_b_2501_);
                    return v_b_2501_;
                } else {
                    v___x_2510_ = l_Lean_instInhabitedNamePart_default;
                    v___x_2511_ = lean_array_get_borrowed(v___x_2510_, v_b_2501_, v_i_2502_);
                    if leanh::lean_obj_tag(v___x_2511_) == 0 {
                        v_s_2512_ = leanh::lean_ctor_get(v___x_2511_, 0);
                        v___x_2513_ = leanh::lean_unsigned_to_nat(0);
                        v___x_2517_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg___closed__0;
                        v___x_2518_ = lean_string_utf8_byte_size(v_s_2512_);
                        v___x_2519_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg___closed__1_once), _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg___closed__1);
                        v___x_2520_ = lean_nat_dec_le(v___x_2519_, v___x_2518_);
                        if v___x_2520_ == 0 {
                            v___x_2521_ = lean_nat_dec_eq(v___x_2499_, v___x_2513_);
                            v___y_2515_ = v___x_2521_;
                            state = 2;
                            continue;
                        } else {
                            v___x_2522_ = lean_string_memcmp(
                                v_s_2512_,
                                v___x_2517_,
                                v___x_2513_,
                                v___x_2513_,
                                v___x_2519_,
                            );
                            v___y_2515_ = v___x_2522_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_2506_ = v_b_2501_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2507_ = lean_nat_add(v_i_2502_, v_step_2504_);
                leanh::lean_dec(v_i_2502_);
                v_b_2501_ = v_a_2506_;
                v_i_2502_ = v___x_2507_;
                state = 0;
                continue;
            }
            2 => {
                if v___y_2515_ == 0 {
                    v_a_2506_ = v_b_2501_;
                    state = 1;
                    continue;
                } else {
                    v___x_2516_ = l_Array_extract___redArg(v_b_2501_, v___x_2513_, v_i_2502_);
                    return v___x_2516_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg___boxed(
    mut v___x_2523_: *mut leanh::LeanObject,
    mut v_range_2524_: *mut leanh::LeanObject,
    mut v_b_2525_: *mut leanh::LeanObject,
    mut v_i_2526_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2527_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2527_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg(v___x_2523_, v_range_2524_, v_b_2525_, v_i_2526_);
    leanh::lean_dec_ref(v_b_2525_);
    leanh::lean_dec_ref(v_range_2524_);
    leanh::lean_dec(v___x_2523_);
    return v_res_2527_;
}
pub unsafe fn _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2531_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__0;
    v___x_2532_ = lean_string_utf8_byte_size(v___x_2531_);
    return v___x_2532_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg(
    mut v___x_2535_: *mut leanh::LeanObject,
    mut v___x_2536_: *mut leanh::LeanObject,
    mut v_range_2537_: *mut leanh::LeanObject,
    mut v_b_2538_: *mut leanh::LeanObject,
    mut v_i_2539_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_stop_2540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_step_2541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: u8 = 0;
    let mut v_snd_2547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2552_: u8 = 0;
    let mut v_fst_2553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2556_: u8 = 0;
    let mut v_fst_2557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2561_: u8 = 0;
    let mut v___x_2562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: u8 = 0;
    let mut v___x_2564_: u8 = 0;
    let mut v___x_2565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: u8 = 0;
    let mut v___x_2569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2571_: u8 = 0;
    let mut v___x_2572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2585_: u8 = 0;
    let mut v___x_2586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2599_: u8 = 0;
    let mut v_val_2600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cont_2622_: u8 = 0;
    let mut v_entries_2624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currentCtx_2625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_2630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: u8 = 0;
    let mut v___x_2634_: u8 = 0;
    let mut v_val_2635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_2638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2661_: u8 = 0;
    let mut v_isSharedCheck_2662_: u8 = 0;
    let mut v_unused_2663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2664_: u8 = 0;
    let mut v_unused_2665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stop_2540_ = leanh::lean_ctor_get(v_range_2537_, 1);
                v_step_2541_ = leanh::lean_ctor_get(v_range_2537_, 2);
                v___x_2546_ = lean_nat_dec_lt(v_i_2539_, v_stop_2540_);
                if v___x_2546_ == 0 {
                    leanh::lean_dec(v_i_2539_);
                    return v_b_2538_;
                } else {
                    v_snd_2547_ = leanh::lean_ctor_get(v_b_2538_, 1);
                    leanh::lean_inc(v_snd_2547_);
                    v_snd_2548_ = leanh::lean_ctor_get(v_snd_2547_, 1);
                    leanh::lean_inc(v_snd_2548_);
                    v_fst_2549_ = leanh::lean_ctor_get(v_b_2538_, 0);
                    v_isSharedCheck_2664_ = (!leanh::lean_is_exclusive(v_b_2538_)) as u8;
                    if v_isSharedCheck_2664_ == 0 {
                        v_unused_2665_ = leanh::lean_ctor_get(v_b_2538_, 1);
                        leanh::lean_dec(v_unused_2665_);
                        v___x_2551_ = v_b_2538_;
                        v_isShared_2552_ = v_isSharedCheck_2664_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_fst_2549_);
                        leanh::lean_dec(v_b_2538_);
                        v___x_2551_ = leanh::lean_box(0);
                        v_isShared_2552_ = v_isSharedCheck_2664_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2544_ = lean_nat_add(v_i_2539_, v_step_2541_);
                leanh::lean_dec(v_i_2539_);
                v_b_2538_ = v_a_2543_;
                v_i_2539_ = v___x_2544_;
                state = 0;
                continue;
            }
            2 => {
                v_fst_2553_ = leanh::lean_ctor_get(v_snd_2547_, 0);
                v_isSharedCheck_2662_ = (!leanh::lean_is_exclusive(v_snd_2547_)) as u8;
                if v_isSharedCheck_2662_ == 0 {
                    v_unused_2663_ = leanh::lean_ctor_get(v_snd_2547_, 1);
                    leanh::lean_dec(v_unused_2663_);
                    v___x_2555_ = v_snd_2547_;
                    v_isShared_2556_ = v_isSharedCheck_2662_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_fst_2553_);
                    leanh::lean_dec(v_snd_2547_);
                    v___x_2555_ = leanh::lean_box(0);
                    v_isShared_2556_ = v_isSharedCheck_2662_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_fst_2557_ = leanh::lean_ctor_get(v_snd_2548_, 0);
                v_snd_2558_ = leanh::lean_ctor_get(v_snd_2548_, 1);
                v_isSharedCheck_2661_ = (!leanh::lean_is_exclusive(v_snd_2548_)) as u8;
                if v_isSharedCheck_2661_ == 0 {
                    v___x_2560_ = v_snd_2548_;
                    v_isShared_2561_ = v_isSharedCheck_2661_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_2558_);
                    leanh::lean_inc(v_fst_2557_);
                    leanh::lean_dec(v_snd_2548_);
                    v___x_2560_ = leanh::lean_box(0);
                    v_isShared_2561_ = v_isSharedCheck_2661_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2562_ = leanh::lean_unsigned_to_nat(0);
                v___x_2563_ = lean_nat_dec_eq(v___x_2536_, v___x_2562_);
                v___x_2564_ = (leanh::lean_unbox(v_snd_2558_) as u8);
                if v___x_2564_ == 0 {
                    v___x_2565_ = l_Lean_instInhabitedNamePart_default;
                    v___x_2566_ = lean_array_get_borrowed(v___x_2565_, v___x_2535_, v_i_2539_);
                    v___x_2567_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___redArg___closed__1;
                    v___x_2568_ = l_Lean_instBEqNamePart_beq(v___x_2566_, v___x_2567_);
                    if v___x_2568_ == 0 {
                        v___x_2569_ = leanh::lean_box(0);
                        v___x_2620_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__0;
                        v___x_2621_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__1;
                        v_cont_2622_ = l_Lean_instBEqNamePart_beq(v___x_2566_, v___x_2621_);
                        if v_cont_2622_ == 0 {
                            if leanh::lean_obj_tag(v___x_2566_) == 0 {
                                v_s_2630_ = leanh::lean_ctor_get(v___x_2566_, 0);
                                v___x_2631_ = lean_string_utf8_byte_size(v_s_2630_);
                                v___x_2632_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__2_once), _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__2);
                                v___x_2633_ = lean_nat_dec_le(v___x_2632_, v___x_2631_);
                                if v___x_2633_ == 0 {
                                    v___y_2571_ = v_cont_2622_;
                                    state = 5;
                                    continue;
                                } else {
                                    v___x_2634_ = lean_string_memcmp(
                                        v_s_2630_,
                                        v___x_2620_,
                                        v___x_2562_,
                                        v___x_2562_,
                                        v___x_2632_,
                                    );
                                    v___y_2571_ = v___x_2634_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                v___y_2571_ = v___x_2563_;
                                state = 5;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_2560_);
                            leanh::lean_dec(v_snd_2558_);
                            leanh::lean_del_object(v___x_2555_);
                            leanh::lean_del_object(v___x_2551_);
                            if leanh::lean_obj_tag(v_fst_2553_) == 1 {
                                v_val_2635_ = leanh::lean_ctor_get(v_fst_2553_, 0);
                                leanh::lean_inc(v_val_2635_);
                                leanh::lean_dec_ref_known(v_fst_2553_, 1);
                                v___x_2636_ = lean_array_push(v_fst_2549_, v_val_2635_);
                                v_entries_2624_ = v___x_2636_;
                                v_currentCtx_2625_ = v___x_2569_;
                                state = 20;
                                continue;
                            } else {
                                v_entries_2624_ = v_fst_2549_;
                                v_currentCtx_2625_ = v_fst_2553_;
                                state = 20;
                                continue;
                            }
                        }
                    } else {
                        if leanh::lean_obj_tag(v_fst_2553_) == 1 {
                            v_val_2649_ = leanh::lean_ctor_get(v_fst_2553_, 0);
                            leanh::lean_inc(v_val_2649_);
                            leanh::lean_dec_ref_known(v_fst_2553_, 1);
                            v___x_2650_ = lean_array_push(v_fst_2549_, v_val_2649_);
                            v_entries_2638_ = v___x_2650_;
                            state = 21;
                            continue;
                        } else {
                            leanh::lean_dec(v_fst_2553_);
                            v_entries_2638_ = v_fst_2549_;
                            state = 21;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_snd_2558_);
                    v___x_2651_ = leanh::lean_box((v___x_2563_) as usize);
                    if v_isShared_2561_ == 0 {
                        leanh::lean_ctor_set(v___x_2560_, 1, v___x_2651_);
                        v___x_2653_ = v___x_2560_;
                        state = 25;
                        continue;
                    } else {
                        v_reuseFailAlloc_2660_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2660_, 0, v_fst_2557_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2660_, 1, v___x_2651_);
                        v___x_2653_ = v_reuseFailAlloc_2660_;
                        state = 25;
                        continue;
                    }
                }
            }
            5 => {
                if v___y_2571_ == 0 {
                    if leanh::lean_obj_tag(v_fst_2553_) == 0 {
                        leanh::lean_inc(v___x_2566_);
                        v___x_2572_ = lean_array_push(v_fst_2557_, v___x_2566_);
                        if v_isShared_2561_ == 0 {
                            leanh::lean_ctor_set(v___x_2560_, 0, v___x_2572_);
                            v___x_2574_ = v___x_2560_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_2581_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2581_, 0, v___x_2572_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2581_, 1, v_snd_2558_);
                            v___x_2574_ = v_reuseFailAlloc_2581_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_val_2582_ = leanh::lean_ctor_get(v_fst_2553_, 0);
                        v_isSharedCheck_2599_ =
                            (!leanh::lean_is_exclusive(v_fst_2553_)) as u8;
                        if v_isSharedCheck_2599_ == 0 {
                            v___x_2584_ = v_fst_2553_;
                            v_isShared_2585_ = v_isSharedCheck_2599_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_2582_);
                            leanh::lean_dec(v_fst_2553_);
                            v___x_2584_ = leanh::lean_box(0);
                            v_isShared_2585_ = v_isSharedCheck_2599_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    if leanh::lean_obj_tag(v_fst_2553_) == 1 {
                        v_val_2600_ = leanh::lean_ctor_get(v_fst_2553_, 0);
                        leanh::lean_inc(v_val_2600_);
                        leanh::lean_dec_ref_known(v_fst_2553_, 1);
                        v___x_2601_ = lean_array_push(v_fst_2549_, v_val_2600_);
                        if v_isShared_2561_ == 0 {
                            v___x_2603_ = v___x_2560_;
                            state = 14;
                            continue;
                        } else {
                            v_reuseFailAlloc_2610_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2610_, 0, v_fst_2557_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2610_, 1, v_snd_2558_);
                            v___x_2603_ = v_reuseFailAlloc_2610_;
                            state = 14;
                            continue;
                        }
                    } else {
                        if v_isShared_2561_ == 0 {
                            v___x_2612_ = v___x_2560_;
                            state = 17;
                            continue;
                        } else {
                            v_reuseFailAlloc_2619_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2619_, 0, v_fst_2557_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2619_, 1, v_snd_2558_);
                            v___x_2612_ = v_reuseFailAlloc_2619_;
                            state = 17;
                            continue;
                        }
                    }
                }
            }
            6 => {
                if v_isShared_2556_ == 0 {
                    leanh::lean_ctor_set(v___x_2555_, 1, v___x_2574_);
                    v___x_2576_ = v___x_2555_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2580_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2580_, 0, v_fst_2553_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2580_, 1, v___x_2574_);
                    v___x_2576_ = v_reuseFailAlloc_2580_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2552_ == 0 {
                    leanh::lean_ctor_set(v___x_2551_, 1, v___x_2576_);
                    v___x_2578_ = v___x_2551_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2579_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2579_, 0, v_fst_2549_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2579_, 1, v___x_2576_);
                    v___x_2578_ = v_reuseFailAlloc_2579_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v_a_2543_ = v___x_2578_;
                state = 1;
                continue;
            }
            9 => {
                leanh::lean_inc(v___x_2566_);
                v___x_2586_ = lean_array_push(v_val_2582_, v___x_2566_);
                if v_isShared_2585_ == 0 {
                    leanh::lean_ctor_set(v___x_2584_, 0, v___x_2586_);
                    v___x_2588_ = v___x_2584_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2598_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2598_, 0, v___x_2586_);
                    v___x_2588_ = v_reuseFailAlloc_2598_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_2561_ == 0 {
                    v___x_2590_ = v___x_2560_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2597_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2597_, 0, v_fst_2557_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2597_, 1, v_snd_2558_);
                    v___x_2590_ = v_reuseFailAlloc_2597_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_2556_ == 0 {
                    leanh::lean_ctor_set(v___x_2555_, 1, v___x_2590_);
                    leanh::lean_ctor_set(v___x_2555_, 0, v___x_2588_);
                    v___x_2592_ = v___x_2555_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2596_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2596_, 0, v___x_2588_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2596_, 1, v___x_2590_);
                    v___x_2592_ = v_reuseFailAlloc_2596_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_2552_ == 0 {
                    leanh::lean_ctor_set(v___x_2551_, 1, v___x_2592_);
                    v___x_2594_ = v___x_2551_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2595_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2595_, 0, v_fst_2549_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2595_, 1, v___x_2592_);
                    v___x_2594_ = v_reuseFailAlloc_2595_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v_a_2543_ = v___x_2594_;
                state = 1;
                continue;
            }
            14 => {
                if v_isShared_2556_ == 0 {
                    leanh::lean_ctor_set(v___x_2555_, 1, v___x_2603_);
                    leanh::lean_ctor_set(v___x_2555_, 0, v___x_2569_);
                    v___x_2605_ = v___x_2555_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2609_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2609_, 0, v___x_2569_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2609_, 1, v___x_2603_);
                    v___x_2605_ = v_reuseFailAlloc_2609_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_2552_ == 0 {
                    leanh::lean_ctor_set(v___x_2551_, 1, v___x_2605_);
                    leanh::lean_ctor_set(v___x_2551_, 0, v___x_2601_);
                    v___x_2607_ = v___x_2551_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2608_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2608_, 0, v___x_2601_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2608_, 1, v___x_2605_);
                    v___x_2607_ = v_reuseFailAlloc_2608_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v_a_2543_ = v___x_2607_;
                state = 1;
                continue;
            }
            17 => {
                if v_isShared_2556_ == 0 {
                    leanh::lean_ctor_set(v___x_2555_, 1, v___x_2612_);
                    v___x_2614_ = v___x_2555_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2618_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2618_, 0, v_fst_2553_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2618_, 1, v___x_2612_);
                    v___x_2614_ = v_reuseFailAlloc_2618_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_2552_ == 0 {
                    leanh::lean_ctor_set(v___x_2551_, 1, v___x_2614_);
                    v___x_2616_ = v___x_2551_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_2617_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2617_, 0, v_fst_2549_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2617_, 1, v___x_2614_);
                    v___x_2616_ = v_reuseFailAlloc_2617_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                v_a_2543_ = v___x_2616_;
                state = 1;
                continue;
            }
            20 => {
                v___x_2626_ = leanh::lean_box((v_cont_2622_) as usize);
                v___x_2627_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2627_, 0, v_fst_2557_);
                leanh::lean_ctor_set(v___x_2627_, 1, v___x_2626_);
                v___x_2628_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2628_, 0, v_currentCtx_2625_);
                leanh::lean_ctor_set(v___x_2628_, 1, v___x_2627_);
                v___x_2629_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2629_, 0, v_entries_2624_);
                leanh::lean_ctor_set(v___x_2629_, 1, v___x_2628_);
                v_a_2543_ = v___x_2629_;
                state = 1;
                continue;
            }
            21 => {
                v___x_2639_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__3;
                if v_isShared_2561_ == 0 {
                    v___x_2641_ = v___x_2560_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_2648_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2648_, 0, v_fst_2557_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2648_, 1, v_snd_2558_);
                    v___x_2641_ = v_reuseFailAlloc_2648_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                if v_isShared_2556_ == 0 {
                    leanh::lean_ctor_set(v___x_2555_, 1, v___x_2641_);
                    leanh::lean_ctor_set(v___x_2555_, 0, v___x_2639_);
                    v___x_2643_ = v___x_2555_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_2647_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2647_, 0, v___x_2639_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2647_, 1, v___x_2641_);
                    v___x_2643_ = v_reuseFailAlloc_2647_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                if v_isShared_2552_ == 0 {
                    leanh::lean_ctor_set(v___x_2551_, 1, v___x_2643_);
                    leanh::lean_ctor_set(v___x_2551_, 0, v_entries_2638_);
                    v___x_2645_ = v___x_2551_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_2646_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2646_, 0, v_entries_2638_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2646_, 1, v___x_2643_);
                    v___x_2645_ = v_reuseFailAlloc_2646_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                v_a_2543_ = v___x_2645_;
                state = 1;
                continue;
            }
            25 => {
                if v_isShared_2556_ == 0 {
                    leanh::lean_ctor_set(v___x_2555_, 1, v___x_2653_);
                    v___x_2655_ = v___x_2555_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_2659_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2659_, 0, v_fst_2553_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2659_, 1, v___x_2653_);
                    v___x_2655_ = v_reuseFailAlloc_2659_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                if v_isShared_2552_ == 0 {
                    leanh::lean_ctor_set(v___x_2551_, 1, v___x_2655_);
                    v___x_2657_ = v___x_2551_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_2658_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2658_, 0, v_fst_2549_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2658_, 1, v___x_2655_);
                    v___x_2657_ = v_reuseFailAlloc_2658_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                v_a_2543_ = v___x_2657_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___boxed(
    mut v___x_2666_: *mut leanh::LeanObject,
    mut v___x_2667_: *mut leanh::LeanObject,
    mut v_range_2668_: *mut leanh::LeanObject,
    mut v_b_2669_: *mut leanh::LeanObject,
    mut v_i_2670_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2671_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2671_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg(v___x_2666_, v___x_2667_, v_range_2668_, v_b_2669_, v_i_2670_);
    leanh::lean_dec_ref(v_range_2668_);
    leanh::lean_dec(v___x_2667_);
    leanh::lean_dec_ref(v___x_2666_);
    return v_res_2671_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1(
    mut v___x_2677_: *mut leanh::LeanObject,
    mut v_as_2678_: *mut leanh::LeanObject,
    mut v_sz_2679_: usize,
    mut v_i_2680_: usize,
    mut v_b_2681_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: usize = 0;
    let mut v___x_2685_: usize = 0;
    let mut v___y_2688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: u8 = 0;
    let mut v_a_2702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: u8 = 0;
    let mut v___y_2707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_flags_2708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: u8 = 0;
    let mut v___x_2711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2715_: u8 = 0;
    let mut v___x_2716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2701_ = lean_usize_dec_lt(v_i_2680_, v_sz_2679_);
                if v___x_2701_ == 0 {
                    return v_b_2681_;
                } else {
                    v_a_2702_ = lean_array_uget_borrowed(v_as_2678_, v_i_2680_);
                    v_name_2703_ = leanh::lean_ctor_get(v_a_2702_, 0);
                    v___x_2704_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2705_ = lean_nat_dec_eq(v___x_2677_, v___x_2704_);
                    v___x_2714_ = lean_string_utf8_byte_size(v_name_2703_);
                    v___x_2715_ = lean_nat_dec_eq(v___x_2714_, v___x_2704_);
                    if v___x_2715_ == 0 {
                        leanh::lean_inc_ref(v_name_2703_);
                        v___y_2707_ = v_name_2703_;
                        state = 3;
                        continue;
                    } else {
                        v___x_2716_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__4;
                        v___y_2707_ = v___x_2716_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2684_ = 1usize;
                v___x_2685_ = lean_usize_add(v_i_2680_, v___x_2684_);
                v_i_2680_ = v___x_2685_;
                v_b_2681_ = v_a_2683_;
                state = 0;
                continue;
            }
            2 => {
                v___x_2690_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__0;
                v___x_2691_ = lean_string_append(v_b_2681_, v___x_2690_);
                v___x_2692_ = lean_string_append(v___x_2691_, v___y_2689_);
                leanh::lean_dec_ref(v___y_2689_);
                v___x_2693_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__1;
                v___x_2694_ = lean_string_append(v___x_2692_, v___x_2693_);
                v___x_2695_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__2;
                v___x_2696_ = lean_array_to_list(v___y_2688_);
                v___x_2697_ = l_String_intercalate(v___x_2695_, v___x_2696_);
                v___x_2698_ = lean_string_append(v___x_2694_, v___x_2697_);
                leanh::lean_dec_ref(v___x_2697_);
                v___x_2699_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__3;
                v___x_2700_ = lean_string_append(v___x_2698_, v___x_2699_);
                v_a_2683_ = v___x_2700_;
                state = 1;
                continue;
            }
            3 => {
                v_flags_2708_ = leanh::lean_ctor_get(v_a_2702_, 1);
                v___x_2709_ = lean_array_get_size(v_flags_2708_);
                v___x_2710_ = lean_nat_dec_eq(v___x_2709_, v___x_2704_);
                if v___x_2710_ == 0 {
                    leanh::lean_inc_ref(v_flags_2708_);
                    v___y_2688_ = v_flags_2708_;
                    v___y_2689_ = v___y_2707_;
                    state = 2;
                    continue;
                } else {
                    if v___x_2705_ == 0 {
                        v___x_2711_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__0;
                        v___x_2712_ = lean_string_append(v_b_2681_, v___x_2711_);
                        v___x_2713_ = lean_string_append(v___x_2712_, v___y_2707_);
                        leanh::lean_dec_ref(v___y_2707_);
                        v_a_2683_ = v___x_2713_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc_ref(v_flags_2708_);
                        v___y_2688_ = v_flags_2708_;
                        v___y_2689_ = v___y_2707_;
                        state = 2;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___boxed(
    mut v___x_2717_: *mut leanh::LeanObject,
    mut v_as_2718_: *mut leanh::LeanObject,
    mut v_sz_2719_: *mut leanh::LeanObject,
    mut v_i_2720_: *mut leanh::LeanObject,
    mut v_b_2721_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2722_: usize = 0;
    let mut v_i_boxed_2723_: usize = 0;
    let mut v_res_2724_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2722_ = leanh::lean_unbox_usize(v_sz_2719_);
    leanh::lean_dec(v_sz_2719_);
    v_i_boxed_2723_ = leanh::lean_unbox_usize(v_i_2720_);
    leanh::lean_dec(v_i_2720_);
    v_res_2724_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1(v___x_2717_, v_as_2718_, v_sz_boxed_2722_, v_i_boxed_2723_, v_b_2721_);
    leanh::lean_dec_ref(v_as_2718_);
    leanh::lean_dec(v___x_2717_);
    return v_res_2724_;
}
pub unsafe fn l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts(
    mut v_components_2733_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_2737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2738_: usize = 0;
    let mut v___x_2739_: usize = 0;
    let mut v___x_2740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: u8 = 0;
    let mut v___y_2756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: u8 = 0;
    let mut v___y_2762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_parts_2763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_specEntries_2764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: u8 = 0;
    let mut v___x_2767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_2774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2775_: usize = 0;
    let mut v___x_2776_: usize = 0;
    let mut v___x_2777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2792_: u8 = 0;
    let mut v_parts_2793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_flags_2794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2803_: u8 = 0;
    let mut v_flags_2805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: u8 = 0;
    let mut v_fst_2833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: u8 = 0;
    let mut v_fst_2837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2841_: u8 = 0;
    let mut v_reuseFailAlloc_2842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2843_: u8 = 0;
    let mut v___x_2844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2734_ = lean_array_get_size(v_components_2733_);
                v___x_2753_ = leanh::lean_unsigned_to_nat(0);
                v___x_2754_ = lean_nat_dec_eq(v___x_2734_, v___x_2753_);
                if v___x_2754_ == 0 {
                    v___x_2787_ =
                        l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate(
                            v_components_2733_,
                            v___x_2753_,
                            v___x_2734_,
                        );
                    v_fst_2788_ = leanh::lean_ctor_get(v___x_2787_, 0);
                    v_snd_2789_ = leanh::lean_ctor_get(v___x_2787_, 1);
                    v_isSharedCheck_2843_ = (!leanh::lean_is_exclusive(v___x_2787_)) as u8;
                    if v_isSharedCheck_2843_ == 0 {
                        v___x_2791_ = v___x_2787_;
                        v_isShared_2792_ = v_isSharedCheck_2843_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2789_);
                        leanh::lean_inc(v_fst_2788_);
                        leanh::lean_dec(v___x_2787_);
                        v___x_2791_ = leanh::lean_box(0);
                        v_isShared_2792_ = v_isSharedCheck_2843_;
                        state = 7;
                        continue;
                    }
                } else {
                    v___x_2844_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts___closed__0;
                    return v___x_2844_;
                }
            }
            1 => {
                v_sz_2738_ = lean_array_size(v___y_2736_);
                v___x_2739_ = 0usize;
                v___x_2740_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1(v___x_2734_, v___y_2736_, v_sz_2738_, v___x_2739_, v_result_2737_);
                leanh::lean_dec_ref(v___y_2736_);
                return v___x_2740_;
            }
            2 => {
                v___x_2745_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts___closed__0;
                v___x_2746_ = lean_string_append(v___y_2742_, v___x_2745_);
                v___x_2747_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__2;
                v___x_2748_ = lean_array_to_list(v___y_2743_);
                v___x_2749_ = l_String_intercalate(v___x_2747_, v___x_2748_);
                v___x_2750_ = lean_string_append(v___x_2746_, v___x_2749_);
                leanh::lean_dec_ref(v___x_2749_);
                v___x_2751_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__3;
                v___x_2752_ = lean_string_append(v___x_2750_, v___x_2751_);
                v___y_2736_ = v___y_2744_;
                v_result_2737_ = v___x_2752_;
                state = 1;
                continue;
            }
            3 => {
                v___x_2759_ = lean_array_get_size(v___y_2756_);
                v___x_2760_ = lean_nat_dec_eq(v___x_2759_, v___x_2753_);
                if v___x_2760_ == 0 {
                    v___y_2742_ = v___y_2758_;
                    v___y_2743_ = v___y_2756_;
                    v___y_2744_ = v___y_2757_;
                    state = 2;
                    continue;
                } else {
                    if v___x_2754_ == 0 {
                        leanh::lean_dec_ref(v___y_2756_);
                        v___y_2736_ = v___y_2757_;
                        v_result_2737_ = v___y_2758_;
                        state = 1;
                        continue;
                    } else {
                        v___y_2742_ = v___y_2758_;
                        v___y_2743_ = v___y_2756_;
                        v___y_2744_ = v___y_2757_;
                        state = 2;
                        continue;
                    }
                }
            }
            4 => {
                v___x_2765_ = lean_array_get_size(v_parts_2763_);
                v___x_2766_ = lean_nat_dec_eq(v___x_2765_, v___x_2753_);
                if v___x_2766_ == 0 {
                    v___x_2767_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts(v_parts_2763_);
                    leanh::lean_dec_ref(v_parts_2763_);
                    v___y_2756_ = v___y_2762_;
                    v___y_2757_ = v_specEntries_2764_;
                    v___y_2758_ = v___x_2767_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_parts_2763_);
                    v___x_2768_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__4;
                    v___y_2756_ = v___y_2762_;
                    v___y_2757_ = v_specEntries_2764_;
                    v___y_2758_ = v___x_2768_;
                    state = 3;
                    continue;
                }
            }
            5 => {
                v_sz_2775_ = lean_array_size(v_entries_2774_);
                v___x_2776_ = 0usize;
                v___x_2777_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__5(v___x_2734_, v_entries_2774_, v_sz_2775_, v___x_2776_, v___y_2771_);
                leanh::lean_dec_ref(v_entries_2774_);
                v___x_2778_ = l_Array_append___redArg(v___y_2770_, v___y_2773_);
                leanh::lean_dec(v___y_2773_);
                v___y_2762_ = v___y_2772_;
                v_parts_2763_ = v___x_2778_;
                v_specEntries_2764_ = v___x_2777_;
                state = 4;
                continue;
            }
            6 => {
                v___x_2786_ = lean_array_push(v___y_2785_, v___y_2780_);
                v___y_2770_ = v___y_2782_;
                v___y_2771_ = v___y_2781_;
                v___y_2772_ = v___y_2784_;
                v___y_2773_ = v___y_2783_;
                v_entries_2774_ = v___x_2786_;
                state = 5;
                continue;
            }
            7 => {
                v_parts_2793_ =
                    l_Array_extract___redArg(v_components_2733_, v_fst_2788_, v___x_2734_);
                v_flags_2794_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts___closed__1;
                v___x_2795_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts___closed__2;
                if v_isShared_2792_ == 0 {
                    leanh::lean_ctor_set(v___x_2791_, 1, v___x_2795_);
                    leanh::lean_ctor_set(v___x_2791_, 0, v_parts_2793_);
                    v___x_2797_ = v___x_2791_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2842_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2842_, 0, v_parts_2793_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2842_, 1, v___x_2795_);
                    v___x_2797_ = v_reuseFailAlloc_2842_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2798_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__0___redArg(v___x_2734_, v___x_2797_);
                v_fst_2799_ = leanh::lean_ctor_get(v___x_2798_, 0);
                v_snd_2800_ = leanh::lean_ctor_get(v___x_2798_, 1);
                v_isSharedCheck_2841_ = (!leanh::lean_is_exclusive(v___x_2798_)) as u8;
                if v_isSharedCheck_2841_ == 0 {
                    v___x_2802_ = v___x_2798_;
                    v_isShared_2803_ = v_isSharedCheck_2841_;
                    state = 9;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_2800_);
                    leanh::lean_inc(v_fst_2799_);
                    leanh::lean_dec(v___x_2798_);
                    v___x_2802_ = leanh::lean_box(0);
                    v_isShared_2803_ = v_isSharedCheck_2841_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_2836_ = (leanh::lean_unbox(v_snd_2789_) as u8);
                leanh::lean_dec(v_snd_2789_);
                if v___x_2836_ == 0 {
                    v_fst_2837_ = leanh::lean_ctor_get(v_snd_2800_, 0);
                    leanh::lean_inc(v_fst_2837_);
                    leanh::lean_dec(v_snd_2800_);
                    v_flags_2805_ = v_fst_2837_;
                    state = 10;
                    continue;
                } else {
                    v_fst_2838_ = leanh::lean_ctor_get(v_snd_2800_, 0);
                    leanh::lean_inc(v_fst_2838_);
                    leanh::lean_dec(v_snd_2800_);
                    v___x_2839_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts___closed__3;
                    v___x_2840_ = lean_array_push(v_fst_2838_, v___x_2839_);
                    v_flags_2805_ = v___x_2840_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_2806_ = lean_array_get_size(v_fst_2799_);
                v___x_2807_ = leanh::lean_unsigned_to_nat(1);
                v___x_2808_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2808_, 0, v___x_2753_);
                leanh::lean_ctor_set(v___x_2808_, 1, v___x_2806_);
                leanh::lean_ctor_set(v___x_2808_, 2, v___x_2807_);
                v___x_2809_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg(v___x_2734_, v___x_2808_, v_fst_2799_, v___x_2753_);
                leanh::lean_dec(v_fst_2799_);
                leanh::lean_dec_ref_known(v___x_2808_, 3);
                v___x_2810_ = leanh::lean_box(0);
                v___x_2811_ = lean_array_get_size(v___x_2809_);
                v___x_2812_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2812_, 0, v___x_2753_);
                leanh::lean_ctor_set(v___x_2812_, 1, v___x_2811_);
                leanh::lean_ctor_set(v___x_2812_, 2, v___x_2807_);
                v___x_2813_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___redArg(v___x_2809_, v___x_2812_, v___x_2810_, v___x_2753_);
                leanh::lean_dec_ref_known(v___x_2812_, 3);
                if leanh::lean_obj_tag(v___x_2813_) == 1 {
                    v_val_2814_ = leanh::lean_ctor_get(v___x_2813_, 0);
                    leanh::lean_inc_n(v_val_2814_, 2);
                    leanh::lean_dec_ref_known(v___x_2813_, 1);
                    v___x_2815_ = l_Array_extract___redArg(v___x_2809_, v___x_2753_, v_val_2814_);
                    v___x_2816_ = l_Array_extract___redArg(v___x_2809_, v_val_2814_, v___x_2811_);
                    leanh::lean_dec_ref(v___x_2809_);
                    v___x_2817_ = lean_array_get_size(v___x_2816_);
                    v___x_2818_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_2818_, 0, v___x_2753_);
                    leanh::lean_ctor_set(v___x_2818_, 1, v___x_2817_);
                    leanh::lean_ctor_set(v___x_2818_, 2, v___x_2807_);
                    v___x_2819_ = leanh::lean_box((v___x_2754_) as usize);
                    if v_isShared_2803_ == 0 {
                        leanh::lean_ctor_set(v___x_2802_, 1, v___x_2819_);
                        leanh::lean_ctor_set(v___x_2802_, 0, v_flags_2794_);
                        v___x_2821_ = v___x_2802_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_2835_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2835_, 0, v_flags_2794_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2835_, 1, v___x_2819_);
                        v___x_2821_ = v_reuseFailAlloc_2835_;
                        state = 11;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_2813_);
                    leanh::lean_del_object(v___x_2802_);
                    v___y_2762_ = v_flags_2805_;
                    v_parts_2763_ = v___x_2809_;
                    v_specEntries_2764_ = v_flags_2794_;
                    state = 4;
                    continue;
                }
            }
            11 => {
                v___x_2822_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2822_, 0, v___x_2810_);
                leanh::lean_ctor_set(v___x_2822_, 1, v___x_2821_);
                v___x_2823_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2823_, 0, v_flags_2794_);
                leanh::lean_ctor_set(v___x_2823_, 1, v___x_2822_);
                v___x_2824_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg(v___x_2816_, v___x_2734_, v___x_2818_, v___x_2823_, v___x_2753_);
                leanh::lean_dec_ref_known(v___x_2818_, 3);
                leanh::lean_dec_ref(v___x_2816_);
                v_snd_2825_ = leanh::lean_ctor_get(v___x_2824_, 1);
                leanh::lean_inc(v_snd_2825_);
                v_snd_2826_ = leanh::lean_ctor_get(v_snd_2825_, 1);
                leanh::lean_inc(v_snd_2826_);
                v_fst_2827_ = leanh::lean_ctor_get(v_snd_2825_, 0);
                leanh::lean_inc(v_fst_2827_);
                leanh::lean_dec(v_snd_2825_);
                if leanh::lean_obj_tag(v_fst_2827_) == 1 {
                    v_fst_2828_ = leanh::lean_ctor_get(v___x_2824_, 0);
                    leanh::lean_inc(v_fst_2828_);
                    leanh::lean_dec_ref(v___x_2824_);
                    v_fst_2829_ = leanh::lean_ctor_get(v_snd_2826_, 0);
                    leanh::lean_inc(v_fst_2829_);
                    leanh::lean_dec(v_snd_2826_);
                    v_val_2830_ = leanh::lean_ctor_get(v_fst_2827_, 0);
                    leanh::lean_inc(v_val_2830_);
                    leanh::lean_dec_ref_known(v_fst_2827_, 1);
                    v___x_2831_ = lean_array_get_size(v_val_2830_);
                    v___x_2832_ = lean_nat_dec_eq(v___x_2831_, v___x_2753_);
                    if v___x_2832_ == 0 {
                        v___y_2780_ = v_val_2830_;
                        v___y_2781_ = v_flags_2794_;
                        v___y_2782_ = v___x_2815_;
                        v___y_2783_ = v_fst_2829_;
                        v___y_2784_ = v_flags_2805_;
                        v___y_2785_ = v_fst_2828_;
                        state = 6;
                        continue;
                    } else {
                        if v___x_2754_ == 0 {
                            leanh::lean_dec(v_val_2830_);
                            v___y_2770_ = v___x_2815_;
                            v___y_2771_ = v_flags_2794_;
                            v___y_2772_ = v_flags_2805_;
                            v___y_2773_ = v_fst_2829_;
                            v_entries_2774_ = v_fst_2828_;
                            state = 5;
                            continue;
                        } else {
                            v___y_2780_ = v_val_2830_;
                            v___y_2781_ = v_flags_2794_;
                            v___y_2782_ = v___x_2815_;
                            v___y_2783_ = v_fst_2829_;
                            v___y_2784_ = v_flags_2805_;
                            v___y_2785_ = v_fst_2828_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_fst_2827_);
                    v_fst_2833_ = leanh::lean_ctor_get(v___x_2824_, 0);
                    leanh::lean_inc(v_fst_2833_);
                    leanh::lean_dec_ref(v___x_2824_);
                    v_fst_2834_ = leanh::lean_ctor_get(v_snd_2826_, 0);
                    leanh::lean_inc(v_fst_2834_);
                    leanh::lean_dec(v_snd_2826_);
                    v___y_2770_ = v___x_2815_;
                    v___y_2771_ = v_flags_2794_;
                    v___y_2772_ = v_flags_2805_;
                    v___y_2773_ = v_fst_2834_;
                    v_entries_2774_ = v_fst_2833_;
                    state = 5;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts___boxed(
    mut v_components_2845_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2846_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2846_ =
        l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts(
            v_components_2845_,
        );
    leanh::lean_dec_ref(v_components_2845_);
    return v_res_2846_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__0(
    mut v___x_2847_: *mut leanh::LeanObject,
    mut v_inst_2848_: *mut leanh::LeanObject,
    mut v_a_2849_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2850_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2850_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__0___redArg(v___x_2847_, v_a_2849_);
    return v___x_2850_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__0___boxed(
    mut v___x_2851_: *mut leanh::LeanObject,
    mut v_inst_2852_: *mut leanh::LeanObject,
    mut v_a_2853_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2854_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2854_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__0(v___x_2851_, v_inst_2852_, v_a_2853_);
    leanh::lean_dec(v___x_2851_);
    return v_res_2854_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2(
    mut v___x_2855_: *mut leanh::LeanObject,
    mut v_range_2856_: *mut leanh::LeanObject,
    mut v_b_2857_: *mut leanh::LeanObject,
    mut v_i_2858_: *mut leanh::LeanObject,
    mut v_hs_2859_: *mut leanh::LeanObject,
    mut v_hl_2860_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2861_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2861_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg(v___x_2855_, v_range_2856_, v_b_2857_, v_i_2858_);
    return v___x_2861_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___boxed(
    mut v___x_2862_: *mut leanh::LeanObject,
    mut v_range_2863_: *mut leanh::LeanObject,
    mut v_b_2864_: *mut leanh::LeanObject,
    mut v_i_2865_: *mut leanh::LeanObject,
    mut v_hs_2866_: *mut leanh::LeanObject,
    mut v_hl_2867_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2868_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2868_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2(v___x_2862_, v_range_2863_, v_b_2864_, v_i_2865_, v_hs_2866_, v_hl_2867_);
    leanh::lean_dec_ref(v_b_2864_);
    leanh::lean_dec_ref(v_range_2863_);
    leanh::lean_dec(v___x_2862_);
    return v_res_2868_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3(
    mut v___x_2869_: *mut leanh::LeanObject,
    mut v_range_2870_: *mut leanh::LeanObject,
    mut v_b_2871_: *mut leanh::LeanObject,
    mut v_i_2872_: *mut leanh::LeanObject,
    mut v_hs_2873_: *mut leanh::LeanObject,
    mut v_hl_2874_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2875_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2875_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___redArg(v___x_2869_, v_range_2870_, v_b_2871_, v_i_2872_);
    return v___x_2875_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___boxed(
    mut v___x_2876_: *mut leanh::LeanObject,
    mut v_range_2877_: *mut leanh::LeanObject,
    mut v_b_2878_: *mut leanh::LeanObject,
    mut v_i_2879_: *mut leanh::LeanObject,
    mut v_hs_2880_: *mut leanh::LeanObject,
    mut v_hl_2881_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2882_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2882_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3(v___x_2876_, v_range_2877_, v_b_2878_, v_i_2879_, v_hs_2880_, v_hl_2881_);
    leanh::lean_dec(v_b_2878_);
    leanh::lean_dec_ref(v_range_2877_);
    leanh::lean_dec_ref(v___x_2876_);
    return v_res_2882_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4(
    mut v___x_2883_: *mut leanh::LeanObject,
    mut v___x_2884_: *mut leanh::LeanObject,
    mut v_range_2885_: *mut leanh::LeanObject,
    mut v_b_2886_: *mut leanh::LeanObject,
    mut v_i_2887_: *mut leanh::LeanObject,
    mut v_hs_2888_: *mut leanh::LeanObject,
    mut v_hl_2889_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2890_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2890_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg(v___x_2883_, v___x_2884_, v_range_2885_, v_b_2886_, v_i_2887_);
    return v___x_2890_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___boxed(
    mut v___x_2891_: *mut leanh::LeanObject,
    mut v___x_2892_: *mut leanh::LeanObject,
    mut v_range_2893_: *mut leanh::LeanObject,
    mut v_b_2894_: *mut leanh::LeanObject,
    mut v_i_2895_: *mut leanh::LeanObject,
    mut v_hs_2896_: *mut leanh::LeanObject,
    mut v_hl_2897_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2898_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2898_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4(v___x_2891_, v___x_2892_, v_range_2893_, v_b_2894_, v_i_2895_, v_hs_2896_, v_hl_2897_);
    leanh::lean_dec_ref(v_range_2893_);
    leanh::lean_dec(v___x_2892_);
    leanh::lean_dec_ref(v___x_2891_);
    return v_res_2898_;
}
pub unsafe fn l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody(
    mut v_body_2899_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_name_2900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_2900_ = l_Lean_Name_demangle(v_body_2899_);
    v___x_2901_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_nameToNameParts(
        v_name_2900_,
    );
    leanh::lean_dec(v_name_2900_);
    v___x_2902_ =
        l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts(
            v___x_2901_,
        );
    leanh::lean_dec_ref(v___x_2901_);
    return v___x_2902_;
}
pub unsafe fn l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody___boxed(
    mut v_body_2903_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2904_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2904_ =
        l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody(v_body_2903_);
    leanh::lean_dec_ref(v_body_2903_);
    return v_res_2904_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___redArg(
    mut v_s_2908_: *mut leanh::LeanObject,
    mut v___x_2909_: *mut leanh::LeanObject,
    mut v_a_2910_: *mut leanh::LeanObject,
    mut v_b_2911_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_startInclusive_2912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2915_: u8 = 0;
    let mut v___x_2916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_2929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_2930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2936_: u8 = 0;
    let mut v___x_2937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2942_: u8 = 0;
    let mut v___y_2943_: u8 = 0;
    let mut v___y_2946_: u8 = 0;
    let mut v___x_2948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2949_: u8 = 0;
    let mut v___x_2950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_2955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: u32 = 0;
    let mut v___x_2958_: u32 = 0;
    let mut v___x_2959_: u8 = 0;
    let mut v___x_2960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2961_: u8 = 0;
    let mut v___x_2963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_startInclusive_2912_ = leanh::lean_ctor_get(v___x_2909_, 1);
                v_endExclusive_2913_ = leanh::lean_ctor_get(v___x_2909_, 2);
                v___x_2914_ = lean_nat_sub(v_endExclusive_2913_, v_startInclusive_2912_);
                v___x_2915_ = lean_nat_dec_eq(v_a_2910_, v___x_2914_);
                leanh::lean_dec(v___x_2914_);
                if v___x_2915_ == 0 {
                    leanh::lean_dec_ref(v_b_2911_);
                    v___x_2916_ = leanh::lean_box(0);
                    v___x_2931_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___redArg___closed__0;
                    v___x_2932_ = lean_string_utf8_next_fast(v_s_2908_, v_a_2910_);
                    v___x_2957_ = lean_string_utf8_get_fast(v_s_2908_, v_a_2910_);
                    v___x_2958_ = 95;
                    v___x_2959_ = lean_uint32_dec_eq(v___x_2957_, v___x_2958_);
                    if v___x_2959_ == 0 {
                        v___y_2946_ = v___x_2959_;
                        state = 5;
                        continue;
                    } else {
                        v___x_2960_ = leanh::lean_unsigned_to_nat(0);
                        v___x_2961_ = lean_nat_dec_eq(v_a_2910_, v___x_2960_);
                        if v___x_2961_ == 0 {
                            v___y_2946_ = v___x_2959_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_dec(v_a_2910_);
                            v_a_2910_ = v___x_2932_;
                            v_b_2911_ = v___x_2931_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_2910_);
                    v___x_2963_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2963_, 0, v_b_2911_);
                    return v___x_2963_;
                }
            }
            1 => {
                v___x_2920_ =
                    l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody(
                        v___y_2918_,
                    );
                leanh::lean_dec_ref(v___y_2918_);
                v___x_2921_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2921_, 0, v___x_2920_);
                leanh::lean_ctor_set(v___x_2921_, 1, v___y_2919_);
                v___x_2922_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2922_, 0, v___x_2921_);
                v___x_2923_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2923_, 0, v___x_2922_);
                leanh::lean_ctor_set(v___x_2923_, 1, v___x_2916_);
                v___x_2924_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2924_, 0, v___x_2923_);
                return v___x_2924_;
            }
            2 => {
                v___x_2928_ = l_Lean_Name_demangle(v___y_2926_);
                if leanh::lean_obj_tag(v___x_2928_) == 1 {
                    v_pre_2929_ = leanh::lean_ctor_get(v___x_2928_, 0);
                    leanh::lean_inc(v_pre_2929_);
                    if leanh::lean_obj_tag(v_pre_2929_) == 0 {
                        leanh::lean_dec_ref(v___y_2926_);
                        v_str_2930_ = leanh::lean_ctor_get(v___x_2928_, 1);
                        leanh::lean_inc_ref(v_str_2930_);
                        leanh::lean_dec_ref_known(v___x_2928_, 2);
                        v___y_2918_ = v___y_2927_;
                        v___y_2919_ = v_str_2930_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_pre_2929_);
                        leanh::lean_dec_ref_known(v___x_2928_, 2);
                        v___y_2918_ = v___y_2927_;
                        v___y_2919_ = v___y_2926_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_2928_);
                    v___y_2918_ = v___y_2927_;
                    v___y_2919_ = v___y_2926_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_2937_ = l_Lean_Name_demangle_x3f(v___y_2935_);
                if leanh::lean_obj_tag(v___x_2937_) == 0 {
                    if v___y_2936_ == 0 {
                        leanh::lean_dec_ref(v___y_2935_);
                        leanh::lean_dec_ref(v___y_2934_);
                        v_a_2910_ = v___x_2932_;
                        v_b_2911_ = v___x_2931_;
                        state = 0;
                        continue;
                    } else {
                        v___y_2926_ = v___y_2934_;
                        v___y_2927_ = v___y_2935_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref_known(v___x_2937_, 1);
                    v___y_2926_ = v___y_2934_;
                    v___y_2927_ = v___y_2935_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                if v___y_2943_ == 0 {
                    leanh::lean_dec_ref(v___y_2941_);
                    leanh::lean_dec_ref(v___y_2940_);
                    v_a_2910_ = v___x_2932_;
                    v_b_2911_ = v___x_2931_;
                    state = 0;
                    continue;
                } else {
                    v___y_2934_ = v___y_2940_;
                    v___y_2935_ = v___y_2941_;
                    v___y_2936_ = v___y_2942_;
                    state = 3;
                    continue;
                }
            }
            5 => {
                if v___y_2946_ == 0 {
                    leanh::lean_dec(v_a_2910_);
                    v_a_2910_ = v___x_2932_;
                    v_b_2911_ = v___x_2931_;
                    state = 0;
                    continue;
                } else {
                    v___x_2948_ = lean_string_utf8_byte_size(v_s_2908_);
                    v___x_2949_ = lean_nat_dec_eq(v___x_2932_, v___x_2948_);
                    if v___x_2949_ == 0 {
                        v___x_2950_ = leanh::lean_unsigned_to_nat(0);
                        v___x_2951_ = lean_string_utf8_extract(v_s_2908_, v___x_2950_, v_a_2910_);
                        leanh::lean_dec(v_a_2910_);
                        v___x_2952_ = lean_string_utf8_extract(v_s_2908_, v___x_2932_, v___x_2948_);
                        v___x_2953_ = l_Lean_Name_demangle_x3f(v___x_2951_);
                        if leanh::lean_obj_tag(v___x_2953_) == 1 {
                            v_val_2954_ = leanh::lean_ctor_get(v___x_2953_, 0);
                            leanh::lean_inc(v_val_2954_);
                            leanh::lean_dec_ref_known(v___x_2953_, 1);
                            if leanh::lean_obj_tag(v_val_2954_) == 1 {
                                v_pre_2955_ = leanh::lean_ctor_get(v_val_2954_, 0);
                                leanh::lean_inc(v_pre_2955_);
                                leanh::lean_dec_ref_known(v_val_2954_, 2);
                                if leanh::lean_obj_tag(v_pre_2955_) == 0 {
                                    v___y_2934_ = v___x_2951_;
                                    v___y_2935_ = v___x_2952_;
                                    v___y_2936_ = v___x_2949_;
                                    state = 3;
                                    continue;
                                } else {
                                    leanh::lean_dec(v_pre_2955_);
                                    v___y_2940_ = v___x_2951_;
                                    v___y_2941_ = v___x_2952_;
                                    v___y_2942_ = v___x_2949_;
                                    v___y_2943_ = v___x_2949_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_val_2954_);
                                v___y_2940_ = v___x_2951_;
                                v___y_2941_ = v___x_2952_;
                                v___y_2942_ = v___x_2949_;
                                v___y_2943_ = v___x_2949_;
                                state = 4;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v___x_2953_);
                            v___y_2940_ = v___x_2951_;
                            v___y_2941_ = v___x_2952_;
                            v___y_2942_ = v___x_2949_;
                            v___y_2943_ = v___x_2949_;
                            state = 4;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_2910_);
                        v_a_2910_ = v___x_2932_;
                        v_b_2911_ = v___x_2931_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___redArg___boxed(
    mut v_s_2964_: *mut leanh::LeanObject,
    mut v___x_2965_: *mut leanh::LeanObject,
    mut v_a_2966_: *mut leanh::LeanObject,
    mut v_b_2967_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2968_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2968_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___redArg(v_s_2964_, v___x_2965_, v_a_2966_, v_b_2967_);
    leanh::lean_dec_ref(v___x_2965_);
    leanh::lean_dec_ref(v_s_2964_);
    return v_res_2968_;
}
pub unsafe fn l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg(
    mut v_s_2969_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2970_ = leanh::lean_unsigned_to_nat(0);
    v___x_2971_ = lean_string_utf8_byte_size(v_s_2969_);
    leanh::lean_inc_ref(v_s_2969_);
    v___x_2972_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2972_, 0, v_s_2969_);
    leanh::lean_ctor_set(v___x_2972_, 1, v___x_2970_);
    leanh::lean_ctor_set(v___x_2972_, 2, v___x_2971_);
    v___x_2973_ = leanh::lean_box(0);
    v___x_2974_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___redArg___closed__0;
    v___x_2975_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___redArg(v_s_2969_, v___x_2972_, v___x_2970_, v___x_2974_);
    leanh::lean_dec_ref_known(v___x_2972_, 3);
    leanh::lean_dec_ref(v_s_2969_);
    if leanh::lean_obj_tag(v___x_2975_) == 0 {
        return v___x_2973_;
    } else {
        let mut v_val_2976_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_2977_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2976_ = leanh::lean_ctor_get(v___x_2975_, 0);
        leanh::lean_inc(v_val_2976_);
        leanh::lean_dec_ref_known(v___x_2975_, 1);
        v_fst_2977_ = leanh::lean_ctor_get(v_val_2976_, 0);
        leanh::lean_inc(v_fst_2977_);
        leanh::lean_dec(v_val_2976_);
        if leanh::lean_obj_tag(v_fst_2977_) == 0 {
            return v___x_2973_;
        } else {
            return v_fst_2977_;
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0(
    mut v_s_2978_: *mut leanh::LeanObject,
    mut v___x_2979_: *mut leanh::LeanObject,
    mut v_inst_2980_: *mut leanh::LeanObject,
    mut v_R_2981_: *mut leanh::LeanObject,
    mut v_a_2982_: *mut leanh::LeanObject,
    mut v_b_2983_: *mut leanh::LeanObject,
    mut v_c_2984_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2985_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2985_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___redArg(v_s_2978_, v___x_2979_, v_a_2982_, v_b_2983_);
    return v___x_2985_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___boxed(
    mut v_s_2986_: *mut leanh::LeanObject,
    mut v___x_2987_: *mut leanh::LeanObject,
    mut v_inst_2988_: *mut leanh::LeanObject,
    mut v_R_2989_: *mut leanh::LeanObject,
    mut v_a_2990_: *mut leanh::LeanObject,
    mut v_b_2991_: *mut leanh::LeanObject,
    mut v_c_2992_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2993_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2993_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0(v_s_2986_, v___x_2987_, v_inst_2988_, v_R_2989_, v_a_2990_, v_b_2991_, v_c_2992_);
    leanh::lean_dec_ref(v___x_2987_);
    leanh::lean_dec_ref(v_s_2986_);
    return v_res_2993_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0___redArg(
    mut v_s_2994_: *mut leanh::LeanObject,
    mut v___x_2995_: *mut leanh::LeanObject,
    mut v___x_2996_: *mut leanh::LeanObject,
    mut v_a_2997_: *mut leanh::LeanObject,
    mut v_b_2998_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3005_: u8 = 0;
    let mut v___x_3006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3011_: u8 = 0;
    let mut v_needle_3012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_table_3013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stackPos_3014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_needlePos_3015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3018_: u8 = 0;
    let mut v_str_3019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_3020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_3021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_basePos_3022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: u8 = 0;
    let mut v___x_3026_: u8 = 0;
    let mut v___x_3027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stackByte_3029_: u8 = 0;
    let mut v___x_3030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_patByte_3031_: u8 = 0;
    let mut v___x_3032_: u8 = 0;
    let mut v___x_3033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: u8 = 0;
    let mut v___x_3035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNeedlePos_3037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: u8 = 0;
    let mut v___x_3040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextStackPos_3043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextStackPos_3050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextStackPos_3056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextNeedlePos_3057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: u8 = 0;
    let mut v___x_3060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3066_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2999_ = leanh::lean_box(0);
                match leanh::lean_obj_tag(v_a_2997_) {
                    0 => {
                        v_pos_3000_ = leanh::lean_ctor_get(v_a_2997_, 0);
                        leanh::lean_inc(v_pos_3000_);
                        leanh::lean_dec_ref_known(v_a_2997_, 1);
                        v___x_3001_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3001_, 0, v_pos_3000_);
                        return v___x_3001_;
                    }
                    1 => {
                        v_pos_3002_ = leanh::lean_ctor_get(v_a_2997_, 0);
                        v_isSharedCheck_3011_ = (!leanh::lean_is_exclusive(v_a_2997_)) as u8;
                        if v_isSharedCheck_3011_ == 0 {
                            v___x_3004_ = v_a_2997_;
                            v_isShared_3005_ = v_isSharedCheck_3011_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_pos_3002_);
                            leanh::lean_dec(v_a_2997_);
                            v___x_3004_ = leanh::lean_box(0);
                            v_isShared_3005_ = v_isSharedCheck_3011_;
                            state = 1;
                            continue;
                        }
                    }
                    2 => {
                        v_needle_3012_ = leanh::lean_ctor_get(v_a_2997_, 0);
                        v_table_3013_ = leanh::lean_ctor_get(v_a_2997_, 1);
                        v_stackPos_3014_ = leanh::lean_ctor_get(v_a_2997_, 2);
                        v_needlePos_3015_ = leanh::lean_ctor_get(v_a_2997_, 3);
                        v_isSharedCheck_3066_ = (!leanh::lean_is_exclusive(v_a_2997_)) as u8;
                        if v_isSharedCheck_3066_ == 0 {
                            v___x_3017_ = v_a_2997_;
                            v_isShared_3018_ = v_isSharedCheck_3066_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_needlePos_3015_);
                            leanh::lean_inc(v_stackPos_3014_);
                            leanh::lean_inc(v_table_3013_);
                            leanh::lean_inc(v_needle_3012_);
                            leanh::lean_dec(v_a_2997_);
                            v___x_3017_ = leanh::lean_box(0);
                            v_isShared_3018_ = v_isSharedCheck_3066_;
                            state = 3;
                            continue;
                        }
                    }
                    _ => {
                        leanh::lean_inc(v_b_2998_);
                        return v_b_2998_;
                    }
                }
            }
            1 => {
                v___x_3006_ = lean_string_utf8_next_fast(v_s_2994_, v_pos_3002_);
                leanh::lean_dec(v_pos_3002_);
                if v_isShared_3005_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3004_, 0);
                    leanh::lean_ctor_set(v___x_3004_, 0, v___x_3006_);
                    v___x_3008_ = v___x_3004_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3010_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3010_, 0, v___x_3006_);
                    v___x_3008_ = v_reuseFailAlloc_3010_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_2997_ = v___x_3008_;
                v_b_2998_ = v___x_2999_;
                state = 0;
                continue;
            }
            3 => {
                v_str_3019_ = leanh::lean_ctor_get(v_needle_3012_, 0);
                v_startInclusive_3020_ = leanh::lean_ctor_get(v_needle_3012_, 1);
                v_endExclusive_3021_ = leanh::lean_ctor_get(v_needle_3012_, 2);
                v_basePos_3022_ = lean_nat_sub(v_stackPos_3014_, v_needlePos_3015_);
                v___x_3023_ = lean_nat_sub(v_endExclusive_3021_, v_startInclusive_3020_);
                v___x_3024_ = lean_nat_add(v_basePos_3022_, v___x_3023_);
                v___x_3025_ = lean_nat_dec_le(v___x_3024_, v___x_2996_);
                leanh::lean_dec(v___x_3024_);
                if v___x_3025_ == 0 {
                    leanh::lean_dec(v___x_3023_);
                    leanh::lean_del_object(v___x_3017_);
                    leanh::lean_dec(v_needlePos_3015_);
                    leanh::lean_dec(v_stackPos_3014_);
                    leanh::lean_dec_ref(v_table_3013_);
                    leanh::lean_dec_ref(v_needle_3012_);
                    v___x_3026_ = lean_nat_dec_lt(v_basePos_3022_, v___x_2996_);
                    leanh::lean_dec(v_basePos_3022_);
                    if v___x_3026_ == 0 {
                        leanh::lean_inc(v_b_2998_);
                        return v_b_2998_;
                    } else {
                        v___x_3027_ = leanh::lean_box(3);
                        v_a_2997_ = v___x_3027_;
                        v_b_2998_ = v___x_2999_;
                        state = 0;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_basePos_3022_);
                    leanh::lean_inc(v_stackPos_3014_);
                    v_stackByte_3029_ = lean_string_get_byte_fast(v_s_2994_, v_stackPos_3014_);
                    v___x_3030_ = lean_nat_add(v_startInclusive_3020_, v_needlePos_3015_);
                    v_patByte_3031_ = lean_string_get_byte_fast(v_str_3019_, v___x_3030_);
                    v___x_3032_ = lean_uint8_dec_eq(v_stackByte_3029_, v_patByte_3031_);
                    if v___x_3032_ == 0 {
                        leanh::lean_dec(v___x_3023_);
                        v___x_3033_ = leanh::lean_unsigned_to_nat(0);
                        v___x_3034_ = lean_nat_dec_eq(v_needlePos_3015_, v___x_3033_);
                        if v___x_3034_ == 0 {
                            v___x_3035_ = leanh::lean_unsigned_to_nat(1);
                            v___x_3036_ = lean_nat_sub(v_needlePos_3015_, v___x_3035_);
                            leanh::lean_dec(v_needlePos_3015_);
                            v_newNeedlePos_3037_ =
                                lean_array_fget_borrowed(v_table_3013_, v___x_3036_);
                            leanh::lean_dec(v___x_3036_);
                            v___x_3038_ = lean_nat_dec_eq(v_newNeedlePos_3037_, v___x_3033_);
                            if v___x_3038_ == 0 {
                                leanh::lean_inc(v_newNeedlePos_3037_);
                                if v_isShared_3018_ == 0 {
                                    leanh::lean_ctor_set(
                                        v___x_3017_,
                                        3,
                                        v_newNeedlePos_3037_,
                                    );
                                    v___x_3040_ = v___x_3017_;
                                    state = 4;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3042_ =
                                        leanh::lean_alloc_ctor(2, 4, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3042_,
                                        0,
                                        v_needle_3012_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3042_,
                                        1,
                                        v_table_3013_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3042_,
                                        2,
                                        v_stackPos_3014_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3042_,
                                        3,
                                        v_newNeedlePos_3037_,
                                    );
                                    v___x_3040_ = v_reuseFailAlloc_3042_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                v_nextStackPos_3043_ =
                                    l_String_Slice_posGE___redArg(v___x_2995_, v_stackPos_3014_);
                                if v_isShared_3018_ == 0 {
                                    leanh::lean_ctor_set(v___x_3017_, 3, v___x_3033_);
                                    leanh::lean_ctor_set(
                                        v___x_3017_,
                                        2,
                                        v_nextStackPos_3043_,
                                    );
                                    v___x_3045_ = v___x_3017_;
                                    state = 5;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3047_ =
                                        leanh::lean_alloc_ctor(2, 4, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3047_,
                                        0,
                                        v_needle_3012_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3047_,
                                        1,
                                        v_table_3013_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3047_,
                                        2,
                                        v_nextStackPos_3043_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3047_,
                                        3,
                                        v___x_3033_,
                                    );
                                    v___x_3045_ = v_reuseFailAlloc_3047_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_needlePos_3015_);
                            v___x_3048_ = leanh::lean_unsigned_to_nat(1);
                            v___x_3049_ = lean_nat_add(v_stackPos_3014_, v___x_3048_);
                            leanh::lean_dec(v_stackPos_3014_);
                            v_nextStackPos_3050_ =
                                l_String_Slice_posGE___redArg(v___x_2995_, v___x_3049_);
                            if v_isShared_3018_ == 0 {
                                leanh::lean_ctor_set(v___x_3017_, 3, v___x_3033_);
                                leanh::lean_ctor_set(v___x_3017_, 2, v_nextStackPos_3050_);
                                v___x_3052_ = v___x_3017_;
                                state = 6;
                                continue;
                            } else {
                                v_reuseFailAlloc_3054_ =
                                    leanh::lean_alloc_ctor(2, 4, (0) as u32);
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_3054_,
                                    0,
                                    v_needle_3012_,
                                );
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_3054_,
                                    1,
                                    v_table_3013_,
                                );
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_3054_,
                                    2,
                                    v_nextStackPos_3050_,
                                );
                                leanh::lean_ctor_set(v_reuseFailAlloc_3054_, 3, v___x_3033_);
                                v___x_3052_ = v_reuseFailAlloc_3054_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        v___x_3055_ = leanh::lean_unsigned_to_nat(1);
                        v_nextStackPos_3056_ = lean_nat_add(v_stackPos_3014_, v___x_3055_);
                        leanh::lean_dec(v_stackPos_3014_);
                        v_nextNeedlePos_3057_ = lean_nat_add(v_needlePos_3015_, v___x_3055_);
                        leanh::lean_dec(v_needlePos_3015_);
                        v___x_3058_ = lean_nat_dec_eq(v_nextNeedlePos_3057_, v___x_3023_);
                        leanh::lean_dec(v___x_3023_);
                        if v___x_3058_ == 0 {
                            if v_isShared_3018_ == 0 {
                                leanh::lean_ctor_set(v___x_3017_, 3, v_nextNeedlePos_3057_);
                                leanh::lean_ctor_set(v___x_3017_, 2, v_nextStackPos_3056_);
                                v___x_3060_ = v___x_3017_;
                                state = 7;
                                continue;
                            } else {
                                v_reuseFailAlloc_3062_ =
                                    leanh::lean_alloc_ctor(2, 4, (0) as u32);
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_3062_,
                                    0,
                                    v_needle_3012_,
                                );
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_3062_,
                                    1,
                                    v_table_3013_,
                                );
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_3062_,
                                    2,
                                    v_nextStackPos_3056_,
                                );
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_3062_,
                                    3,
                                    v_nextNeedlePos_3057_,
                                );
                                v___x_3060_ = v_reuseFailAlloc_3062_;
                                state = 7;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_3017_);
                            leanh::lean_dec_ref(v_table_3013_);
                            leanh::lean_dec_ref(v_needle_3012_);
                            v___x_3063_ = lean_nat_sub(v_nextStackPos_3056_, v_nextNeedlePos_3057_);
                            leanh::lean_dec(v_nextNeedlePos_3057_);
                            leanh::lean_dec(v_nextStackPos_3056_);
                            v___x_3064_ = l_String_Slice_pos_x21(v___x_2995_, v___x_3063_);
                            leanh::lean_dec(v___x_3063_);
                            v___x_3065_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_3065_, 0, v___x_3064_);
                            return v___x_3065_;
                        }
                    }
                }
            }
            4 => {
                v_a_2997_ = v___x_3040_;
                v_b_2998_ = v___x_2999_;
                state = 0;
                continue;
            }
            5 => {
                v_a_2997_ = v___x_3045_;
                v_b_2998_ = v___x_2999_;
                state = 0;
                continue;
            }
            6 => {
                v_a_2997_ = v___x_3052_;
                v_b_2998_ = v___x_2999_;
                state = 0;
                continue;
            }
            7 => {
                v_a_2997_ = v___x_3060_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0___redArg___boxed(
    mut v_s_3067_: *mut leanh::LeanObject,
    mut v___x_3068_: *mut leanh::LeanObject,
    mut v___x_3069_: *mut leanh::LeanObject,
    mut v_a_3070_: *mut leanh::LeanObject,
    mut v_b_3071_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3072_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3072_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0___redArg(v_s_3067_, v___x_3068_, v___x_3069_, v_a_3070_, v_b_3071_);
    leanh::lean_dec(v_b_3071_);
    leanh::lean_dec(v___x_3069_);
    leanh::lean_dec_ref(v___x_3068_);
    leanh::lean_dec_ref(v_s_3067_);
    return v_res_3072_;
}
pub unsafe fn _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3074_ =
        l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__0;
    v___x_3075_ = lean_string_utf8_byte_size(v___x_3074_);
    return v___x_3075_;
}
pub unsafe fn _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__2()
-> u8 {
    let mut v___x_3076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: u8 = 0;
    v___x_3076_ = leanh::lean_unsigned_to_nat(0);
    v___x_3077_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__1_once), _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__1);
    v___x_3078_ = lean_nat_dec_eq(v___x_3077_, v___x_3076_);
    return v___x_3078_;
}
pub unsafe fn _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3079_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__1_once), _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__1);
    v___x_3080_ = leanh::lean_unsigned_to_nat(0);
    v___x_3081_ =
        l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__0;
    v___x_3082_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_3082_, 0, v___x_3081_);
    leanh::lean_ctor_set(v___x_3082_, 1, v___x_3080_);
    leanh::lean_ctor_set(v___x_3082_, 2, v___x_3079_);
    return v___x_3082_;
}
pub unsafe fn _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_3083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3083_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__3_once), _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__3);
    v___x_3084_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_3083_);
    return v___x_3084_;
}
pub unsafe fn _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_3085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3088_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3085_ = leanh::lean_unsigned_to_nat(0);
    v___x_3086_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__4_once), _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__4);
    v___x_3087_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__3_once), _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__3);
    v___x_3088_ = leanh::lean_alloc_ctor(2, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_3088_, 0, v___x_3087_);
    leanh::lean_ctor_set(v___x_3088_, 1, v___x_3086_);
    leanh::lean_ctor_set(v___x_3088_, 2, v___x_3085_);
    leanh::lean_ctor_set(v___x_3088_, 3, v___x_3085_);
    return v___x_3088_;
}
pub unsafe fn l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix(
    mut v_s_3091_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: u8 = 0;
    let mut v___x_3106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3092_ = leanh::lean_unsigned_to_nat(0);
                v___x_3093_ = lean_string_utf8_byte_size(v_s_3091_);
                leanh::lean_inc_ref(v_s_3091_);
                v___x_3094_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3094_, 0, v_s_3091_);
                leanh::lean_ctor_set(v___x_3094_, 1, v___x_3092_);
                leanh::lean_ctor_set(v___x_3094_, 2, v___x_3093_);
                v___x_3105_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__2_once), _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__2);
                if v___x_3105_ == 0 {
                    v___x_3106_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__5_once), _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__5);
                    v___y_3096_ = v___x_3106_;
                    state = 1;
                    continue;
                } else {
                    v___x_3107_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__6;
                    v___y_3096_ = v___x_3107_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3097_ = leanh::lean_box(0);
                leanh::lean_inc(v___y_3096_);
                v___x_3098_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0___redArg(v_s_3091_, v___x_3094_, v___x_3093_, v___y_3096_, v___x_3097_);
                leanh::lean_dec_ref_known(v___x_3094_, 3);
                if leanh::lean_obj_tag(v___x_3098_) == 0 {
                    v___x_3099_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts___closed__0;
                    v___x_3100_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3100_, 0, v_s_3091_);
                    leanh::lean_ctor_set(v___x_3100_, 1, v___x_3099_);
                    return v___x_3100_;
                } else {
                    v_val_3101_ = leanh::lean_ctor_get(v___x_3098_, 0);
                    leanh::lean_inc(v_val_3101_);
                    leanh::lean_dec_ref_known(v___x_3098_, 1);
                    v___x_3102_ = lean_string_utf8_extract(v_s_3091_, v___x_3092_, v_val_3101_);
                    v___x_3103_ = lean_string_utf8_extract(v_s_3091_, v_val_3101_, v___x_3093_);
                    leanh::lean_dec(v_val_3101_);
                    leanh::lean_dec_ref(v_s_3091_);
                    v___x_3104_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3104_, 0, v___x_3102_);
                    leanh::lean_ctor_set(v___x_3104_, 1, v___x_3103_);
                    return v___x_3104_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0(
    mut v_s_3108_: *mut leanh::LeanObject,
    mut v___x_3109_: *mut leanh::LeanObject,
    mut v___x_3110_: *mut leanh::LeanObject,
    mut v_inst_3111_: *mut leanh::LeanObject,
    mut v_R_3112_: *mut leanh::LeanObject,
    mut v_a_3113_: *mut leanh::LeanObject,
    mut v_b_3114_: *mut leanh::LeanObject,
    mut v_c_3115_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3116_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3116_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0___redArg(v_s_3108_, v___x_3109_, v___x_3110_, v_a_3113_, v_b_3114_);
    return v___x_3116_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0___boxed(
    mut v_s_3117_: *mut leanh::LeanObject,
    mut v___x_3118_: *mut leanh::LeanObject,
    mut v___x_3119_: *mut leanh::LeanObject,
    mut v_inst_3120_: *mut leanh::LeanObject,
    mut v_R_3121_: *mut leanh::LeanObject,
    mut v_a_3122_: *mut leanh::LeanObject,
    mut v_b_3123_: *mut leanh::LeanObject,
    mut v_c_3124_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3125_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3125_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0(v_s_3117_, v___x_3118_, v___x_3119_, v_inst_3120_, v_R_3121_, v_a_3122_, v_b_3123_, v_c_3124_);
    leanh::lean_dec(v_b_3123_);
    leanh::lean_dec(v___x_3119_);
    leanh::lean_dec_ref(v___x_3118_);
    leanh::lean_dec_ref(v_s_3117_);
    return v_res_3125_;
}
pub unsafe fn l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore(
    mut v_s_3137_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3146_: u8 = 0;
    let mut v_fst_3147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3157_: u8 = 0;
    let mut v___x_3158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3166_: u8 = 0;
    let mut v___x_3167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3169_: u8 = 0;
    let mut v___x_3170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3174_: u8 = 0;
    let mut v___x_3176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3181_: u8 = 0;
    let mut v___x_3182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: u8 = 0;
    let mut v___x_3185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3191_: u8 = 0;
    let mut v___x_3193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3200_: u8 = 0;
    let mut v_fst_3201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3213_: u8 = 0;
    let mut v___x_3215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3220_: u8 = 0;
    let mut v___x_3221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: u8 = 0;
    let mut v___x_3224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3230_: u8 = 0;
    let mut v___x_3232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3239_: u8 = 0;
    let mut v_fst_3240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3252_: u8 = 0;
    let mut v___x_3253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3258_: u8 = 0;
    let mut v___x_3259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: u8 = 0;
    let mut v___x_3262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3268_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3253_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__10;
                leanh::lean_inc_ref(v_s_3137_);
                v___x_3254_ =
                    l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(
                        v_s_3137_,
                        v___x_3253_,
                    );
                if leanh::lean_obj_tag(v___x_3254_) == 1 {
                    v_val_3255_ = leanh::lean_ctor_get(v___x_3254_, 0);
                    v_isSharedCheck_3268_ = (!leanh::lean_is_exclusive(v___x_3254_)) as u8;
                    if v_isSharedCheck_3268_ == 0 {
                        v___x_3257_ = v___x_3254_;
                        v_isShared_3258_ = v_isSharedCheck_3268_;
                        state = 19;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_3255_);
                        leanh::lean_dec(v___x_3254_);
                        v___x_3257_ = leanh::lean_box(0);
                        v_isShared_3258_ = v_isSharedCheck_3268_;
                        state = 19;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_3254_);
                    state = 16;
                    continue;
                }
            }
            1 => {
                v___x_3139_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__0;
                v___x_3140_ =
                    l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(
                        v_s_3137_,
                        v___x_3139_,
                    );
                if leanh::lean_obj_tag(v___x_3140_) == 1 {
                    v_val_3141_ = leanh::lean_ctor_get(v___x_3140_, 0);
                    leanh::lean_inc(v_val_3141_);
                    leanh::lean_dec_ref_known(v___x_3140_, 1);
                    v___x_3142_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg(v_val_3141_);
                    if leanh::lean_obj_tag(v___x_3142_) == 1 {
                        v_val_3143_ = leanh::lean_ctor_get(v___x_3142_, 0);
                        v_isSharedCheck_3157_ =
                            (!leanh::lean_is_exclusive(v___x_3142_)) as u8;
                        if v_isSharedCheck_3157_ == 0 {
                            v___x_3145_ = v___x_3142_;
                            v_isShared_3146_ = v_isSharedCheck_3157_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_3143_);
                            leanh::lean_dec(v___x_3142_);
                            v___x_3145_ = leanh::lean_box(0);
                            v_isShared_3146_ = v_isSharedCheck_3157_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_3142_);
                        v___x_3158_ = leanh::lean_box(0);
                        return v___x_3158_;
                    }
                } else {
                    leanh::lean_dec(v___x_3140_);
                    v___x_3159_ = leanh::lean_box(0);
                    return v___x_3159_;
                }
            }
            2 => {
                v_fst_3147_ = leanh::lean_ctor_get(v_val_3143_, 0);
                leanh::lean_inc(v_fst_3147_);
                v_snd_3148_ = leanh::lean_ctor_get(v_val_3143_, 1);
                leanh::lean_inc(v_snd_3148_);
                leanh::lean_dec(v_val_3143_);
                v___x_3149_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__1;
                v___x_3150_ = lean_string_append(v_fst_3147_, v___x_3149_);
                v___x_3151_ = lean_string_append(v___x_3150_, v_snd_3148_);
                leanh::lean_dec(v_snd_3148_);
                v___x_3152_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__2;
                v___x_3153_ = lean_string_append(v___x_3151_, v___x_3152_);
                if v_isShared_3146_ == 0 {
                    leanh::lean_ctor_set(v___x_3145_, 0, v___x_3153_);
                    v___x_3155_ = v___x_3145_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3156_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3156_, 0, v___x_3153_);
                    v___x_3155_ = v_reuseFailAlloc_3156_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3155_;
            }
            4 => {
                v___x_3161_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__3;
                leanh::lean_inc_ref(v_s_3137_);
                v___x_3162_ =
                    l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(
                        v_s_3137_,
                        v___x_3161_,
                    );
                if leanh::lean_obj_tag(v___x_3162_) == 1 {
                    v_val_3163_ = leanh::lean_ctor_get(v___x_3162_, 0);
                    v_isSharedCheck_3174_ = (!leanh::lean_is_exclusive(v___x_3162_)) as u8;
                    if v_isSharedCheck_3174_ == 0 {
                        v___x_3165_ = v___x_3162_;
                        v_isShared_3166_ = v_isSharedCheck_3174_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_3163_);
                        leanh::lean_dec(v___x_3162_);
                        v___x_3165_ = leanh::lean_box(0);
                        v_isShared_3166_ = v_isSharedCheck_3174_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_3162_);
                    state = 1;
                    continue;
                }
            }
            5 => {
                v___x_3167_ = lean_string_utf8_byte_size(v_val_3163_);
                v___x_3168_ = leanh::lean_unsigned_to_nat(0);
                v___x_3169_ = lean_nat_dec_eq(v___x_3167_, v___x_3168_);
                if v___x_3169_ == 0 {
                    leanh::lean_dec_ref(v_s_3137_);
                    v___x_3170_ =
                        l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody(
                            v_val_3163_,
                        );
                    leanh::lean_dec(v_val_3163_);
                    if v_isShared_3166_ == 0 {
                        leanh::lean_ctor_set(v___x_3165_, 0, v___x_3170_);
                        v___x_3172_ = v___x_3165_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3173_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3173_, 0, v___x_3170_);
                        v___x_3172_ = v_reuseFailAlloc_3173_;
                        state = 6;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3165_);
                    leanh::lean_dec(v_val_3163_);
                    state = 1;
                    continue;
                }
            }
            6 => {
                return v___x_3172_;
            }
            7 => {
                v___x_3176_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__4;
                leanh::lean_inc_ref(v_s_3137_);
                v___x_3177_ =
                    l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(
                        v_s_3137_,
                        v___x_3176_,
                    );
                if leanh::lean_obj_tag(v___x_3177_) == 1 {
                    v_val_3178_ = leanh::lean_ctor_get(v___x_3177_, 0);
                    v_isSharedCheck_3191_ = (!leanh::lean_is_exclusive(v___x_3177_)) as u8;
                    if v_isSharedCheck_3191_ == 0 {
                        v___x_3180_ = v___x_3177_;
                        v_isShared_3181_ = v_isSharedCheck_3191_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_3178_);
                        leanh::lean_dec(v___x_3177_);
                        v___x_3180_ = leanh::lean_box(0);
                        v_isShared_3181_ = v_isSharedCheck_3191_;
                        state = 8;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_3177_);
                    state = 4;
                    continue;
                }
            }
            8 => {
                v___x_3182_ = lean_string_utf8_byte_size(v_val_3178_);
                v___x_3183_ = leanh::lean_unsigned_to_nat(0);
                v___x_3184_ = lean_nat_dec_eq(v___x_3182_, v___x_3183_);
                if v___x_3184_ == 0 {
                    leanh::lean_dec_ref(v_s_3137_);
                    v___x_3185_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__5;
                    v___x_3186_ =
                        l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody(
                            v_val_3178_,
                        );
                    leanh::lean_dec(v_val_3178_);
                    v___x_3187_ = lean_string_append(v___x_3185_, v___x_3186_);
                    leanh::lean_dec_ref(v___x_3186_);
                    if v_isShared_3181_ == 0 {
                        leanh::lean_ctor_set(v___x_3180_, 0, v___x_3187_);
                        v___x_3189_ = v___x_3180_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_3190_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3190_, 0, v___x_3187_);
                        v___x_3189_ = v_reuseFailAlloc_3190_;
                        state = 9;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3180_);
                    leanh::lean_dec(v_val_3178_);
                    state = 4;
                    continue;
                }
            }
            9 => {
                return v___x_3189_;
            }
            10 => {
                v___x_3193_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__6;
                leanh::lean_inc_ref(v_s_3137_);
                v___x_3194_ =
                    l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(
                        v_s_3137_,
                        v___x_3193_,
                    );
                if leanh::lean_obj_tag(v___x_3194_) == 1 {
                    v_val_3195_ = leanh::lean_ctor_get(v___x_3194_, 0);
                    leanh::lean_inc(v_val_3195_);
                    leanh::lean_dec_ref_known(v___x_3194_, 1);
                    v___x_3196_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg(v_val_3195_);
                    if leanh::lean_obj_tag(v___x_3196_) == 1 {
                        leanh::lean_dec_ref(v_s_3137_);
                        v_val_3197_ = leanh::lean_ctor_get(v___x_3196_, 0);
                        v_isSharedCheck_3213_ =
                            (!leanh::lean_is_exclusive(v___x_3196_)) as u8;
                        if v_isSharedCheck_3213_ == 0 {
                            v___x_3199_ = v___x_3196_;
                            v_isShared_3200_ = v_isSharedCheck_3213_;
                            state = 11;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_3197_);
                            leanh::lean_dec(v___x_3196_);
                            v___x_3199_ = leanh::lean_box(0);
                            v_isShared_3200_ = v_isSharedCheck_3213_;
                            state = 11;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_3196_);
                        state = 7;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_3194_);
                    state = 7;
                    continue;
                }
            }
            11 => {
                v_fst_3201_ = leanh::lean_ctor_get(v_val_3197_, 0);
                leanh::lean_inc(v_fst_3201_);
                v_snd_3202_ = leanh::lean_ctor_get(v_val_3197_, 1);
                leanh::lean_inc(v_snd_3202_);
                leanh::lean_dec(v_val_3197_);
                v___x_3203_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__5;
                v___x_3204_ = lean_string_append(v___x_3203_, v_fst_3201_);
                leanh::lean_dec(v_fst_3201_);
                v___x_3205_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__1;
                v___x_3206_ = lean_string_append(v___x_3204_, v___x_3205_);
                v___x_3207_ = lean_string_append(v___x_3206_, v_snd_3202_);
                leanh::lean_dec(v_snd_3202_);
                v___x_3208_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__2;
                v___x_3209_ = lean_string_append(v___x_3207_, v___x_3208_);
                if v_isShared_3200_ == 0 {
                    leanh::lean_ctor_set(v___x_3199_, 0, v___x_3209_);
                    v___x_3211_ = v___x_3199_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3212_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3212_, 0, v___x_3209_);
                    v___x_3211_ = v_reuseFailAlloc_3212_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3211_;
            }
            13 => {
                v___x_3215_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__7;
                leanh::lean_inc_ref(v_s_3137_);
                v___x_3216_ =
                    l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(
                        v_s_3137_,
                        v___x_3215_,
                    );
                if leanh::lean_obj_tag(v___x_3216_) == 1 {
                    v_val_3217_ = leanh::lean_ctor_get(v___x_3216_, 0);
                    v_isSharedCheck_3230_ = (!leanh::lean_is_exclusive(v___x_3216_)) as u8;
                    if v_isSharedCheck_3230_ == 0 {
                        v___x_3219_ = v___x_3216_;
                        v_isShared_3220_ = v_isSharedCheck_3230_;
                        state = 14;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_3217_);
                        leanh::lean_dec(v___x_3216_);
                        v___x_3219_ = leanh::lean_box(0);
                        v_isShared_3220_ = v_isSharedCheck_3230_;
                        state = 14;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_3216_);
                    state = 10;
                    continue;
                }
            }
            14 => {
                v___x_3221_ = lean_string_utf8_byte_size(v_val_3217_);
                v___x_3222_ = leanh::lean_unsigned_to_nat(0);
                v___x_3223_ = lean_nat_dec_eq(v___x_3221_, v___x_3222_);
                if v___x_3223_ == 0 {
                    leanh::lean_dec_ref(v_s_3137_);
                    v___x_3224_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__5;
                    v___x_3225_ =
                        l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody(
                            v_val_3217_,
                        );
                    leanh::lean_dec(v_val_3217_);
                    v___x_3226_ = lean_string_append(v___x_3224_, v___x_3225_);
                    leanh::lean_dec_ref(v___x_3225_);
                    if v_isShared_3220_ == 0 {
                        leanh::lean_ctor_set(v___x_3219_, 0, v___x_3226_);
                        v___x_3228_ = v___x_3219_;
                        state = 15;
                        continue;
                    } else {
                        v_reuseFailAlloc_3229_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3229_, 0, v___x_3226_);
                        v___x_3228_ = v_reuseFailAlloc_3229_;
                        state = 15;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3219_);
                    leanh::lean_dec(v_val_3217_);
                    state = 10;
                    continue;
                }
            }
            15 => {
                return v___x_3228_;
            }
            16 => {
                v___x_3232_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__8;
                leanh::lean_inc_ref(v_s_3137_);
                v___x_3233_ =
                    l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(
                        v_s_3137_,
                        v___x_3232_,
                    );
                if leanh::lean_obj_tag(v___x_3233_) == 1 {
                    v_val_3234_ = leanh::lean_ctor_get(v___x_3233_, 0);
                    leanh::lean_inc(v_val_3234_);
                    leanh::lean_dec_ref_known(v___x_3233_, 1);
                    v___x_3235_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg(v_val_3234_);
                    if leanh::lean_obj_tag(v___x_3235_) == 1 {
                        leanh::lean_dec_ref(v_s_3137_);
                        v_val_3236_ = leanh::lean_ctor_get(v___x_3235_, 0);
                        v_isSharedCheck_3252_ =
                            (!leanh::lean_is_exclusive(v___x_3235_)) as u8;
                        if v_isSharedCheck_3252_ == 0 {
                            v___x_3238_ = v___x_3235_;
                            v_isShared_3239_ = v_isSharedCheck_3252_;
                            state = 17;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_3236_);
                            leanh::lean_dec(v___x_3235_);
                            v___x_3238_ = leanh::lean_box(0);
                            v_isShared_3239_ = v_isSharedCheck_3252_;
                            state = 17;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_3235_);
                        state = 13;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_3233_);
                    state = 13;
                    continue;
                }
            }
            17 => {
                v_fst_3240_ = leanh::lean_ctor_get(v_val_3236_, 0);
                leanh::lean_inc(v_fst_3240_);
                v_snd_3241_ = leanh::lean_ctor_get(v_val_3236_, 1);
                leanh::lean_inc(v_snd_3241_);
                leanh::lean_dec(v_val_3236_);
                v___x_3242_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__9;
                v___x_3243_ = lean_string_append(v___x_3242_, v_fst_3240_);
                leanh::lean_dec(v_fst_3240_);
                v___x_3244_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__1;
                v___x_3245_ = lean_string_append(v___x_3243_, v___x_3244_);
                v___x_3246_ = lean_string_append(v___x_3245_, v_snd_3241_);
                leanh::lean_dec(v_snd_3241_);
                v___x_3247_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__2;
                v___x_3248_ = lean_string_append(v___x_3246_, v___x_3247_);
                if v_isShared_3239_ == 0 {
                    leanh::lean_ctor_set(v___x_3238_, 0, v___x_3248_);
                    v___x_3250_ = v___x_3238_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3251_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3251_, 0, v___x_3248_);
                    v___x_3250_ = v_reuseFailAlloc_3251_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_3250_;
            }
            19 => {
                v___x_3259_ = lean_string_utf8_byte_size(v_val_3255_);
                v___x_3260_ = leanh::lean_unsigned_to_nat(0);
                v___x_3261_ = lean_nat_dec_eq(v___x_3259_, v___x_3260_);
                if v___x_3261_ == 0 {
                    leanh::lean_dec_ref(v_s_3137_);
                    v___x_3262_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__9;
                    v___x_3263_ =
                        l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody(
                            v_val_3255_,
                        );
                    leanh::lean_dec(v_val_3255_);
                    v___x_3264_ = lean_string_append(v___x_3262_, v___x_3263_);
                    leanh::lean_dec_ref(v___x_3263_);
                    if v_isShared_3258_ == 0 {
                        leanh::lean_ctor_set(v___x_3257_, 0, v___x_3264_);
                        v___x_3266_ = v___x_3257_;
                        state = 20;
                        continue;
                    } else {
                        v_reuseFailAlloc_3267_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3267_, 0, v___x_3264_);
                        v___x_3266_ = v_reuseFailAlloc_3267_;
                        state = 20;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3257_);
                    leanh::lean_dec(v_val_3255_);
                    state = 16;
                    continue;
                }
            }
            20 => {
                return v___x_3266_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Name_Demangle_demangleSymbol(
    mut v_symbol_3278_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3281_: u8 = 0;
    let mut v___x_3282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3287_: u8 = 0;
    let mut v___x_3288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: u8 = 0;
    let mut v___x_3293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3294_: u8 = 0;
    let mut v___x_3295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3301_: u8 = 0;
    let mut v_unused_3302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: u8 = 0;
    let mut v___x_3305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3314_: u8 = 0;
    let mut v___x_3315_: u8 = 0;
    let mut v___x_3316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: u8 = 0;
    let mut v___x_3322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3331_: u8 = 0;
    let mut v___x_3332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3279_ = lean_string_utf8_byte_size(v_symbol_3278_);
                v___x_3280_ = leanh::lean_unsigned_to_nat(0);
                v___x_3281_ = lean_nat_dec_eq(v___x_3279_, v___x_3280_);
                if v___x_3281_ == 0 {
                    v___x_3282_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix(v_symbol_3278_);
                    v_fst_3283_ = leanh::lean_ctor_get(v___x_3282_, 0);
                    leanh::lean_inc_n(v_fst_3283_, 2);
                    v_snd_3284_ = leanh::lean_ctor_get(v___x_3282_, 1);
                    leanh::lean_inc(v_snd_3284_);
                    leanh::lean_dec_ref(v___x_3282_);
                    v___x_3309_ = l_Lean_Name_Demangle_demangleSymbol___closed__5;
                    v___x_3310_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_fst_3283_, v___x_3309_);
                    if leanh::lean_obj_tag(v___x_3310_) == 1 {
                        v_val_3311_ = leanh::lean_ctor_get(v___x_3310_, 0);
                        v_isSharedCheck_3331_ =
                            (!leanh::lean_is_exclusive(v___x_3310_)) as u8;
                        if v_isSharedCheck_3331_ == 0 {
                            v___x_3313_ = v___x_3310_;
                            v_isShared_3314_ = v_isSharedCheck_3331_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_3311_);
                            leanh::lean_dec(v___x_3310_);
                            v___x_3313_ = leanh::lean_box(0);
                            v_isShared_3314_ = v_isSharedCheck_3331_;
                            state = 4;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_3310_);
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_symbol_3278_);
                    v___x_3332_ = leanh::lean_box(0);
                    return v___x_3332_;
                }
            }
            1 => {
                v___x_3286_ = l_Lean_Name_Demangle_demangleSymbol___closed__0;
                v___x_3287_ = lean_string_dec_eq(v_fst_3283_, v___x_3286_);
                if v___x_3287_ == 0 {
                    v___x_3288_ =
                        l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore(
                            v_fst_3283_,
                        );
                    if leanh::lean_obj_tag(v___x_3288_) == 0 {
                        leanh::lean_dec(v_snd_3284_);
                        return v___x_3288_;
                    } else {
                        v_val_3289_ = leanh::lean_ctor_get(v___x_3288_, 0);
                        leanh::lean_inc(v_val_3289_);
                        v___x_3290_ = lean_string_utf8_byte_size(v_snd_3284_);
                        v___x_3291_ = lean_nat_dec_eq(v___x_3290_, v___x_3280_);
                        if v___x_3291_ == 0 {
                            v_isSharedCheck_3301_ =
                                (!leanh::lean_is_exclusive(v___x_3288_)) as u8;
                            if v_isSharedCheck_3301_ == 0 {
                                v_unused_3302_ = leanh::lean_ctor_get(v___x_3288_, 0);
                                leanh::lean_dec(v_unused_3302_);
                                v___x_3293_ = v___x_3288_;
                                v_isShared_3294_ = v_isSharedCheck_3301_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_3288_);
                                v___x_3293_ = leanh::lean_box(0);
                                v_isShared_3294_ = v_isSharedCheck_3301_;
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_val_3289_);
                            leanh::lean_dec(v_snd_3284_);
                            return v___x_3288_;
                        }
                    }
                } else {
                    leanh::lean_dec(v_fst_3283_);
                    v___x_3303_ = lean_string_utf8_byte_size(v_snd_3284_);
                    v___x_3304_ = lean_nat_dec_eq(v___x_3303_, v___x_3280_);
                    if v___x_3304_ == 0 {
                        v___x_3305_ = l_Lean_Name_Demangle_demangleSymbol___closed__2;
                        v___x_3306_ = lean_string_append(v___x_3305_, v_snd_3284_);
                        leanh::lean_dec(v_snd_3284_);
                        v___x_3307_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3307_, 0, v___x_3306_);
                        return v___x_3307_;
                    } else {
                        leanh::lean_dec(v_snd_3284_);
                        v___x_3308_ = l_Lean_Name_Demangle_demangleSymbol___closed__4;
                        return v___x_3308_;
                    }
                }
            }
            2 => {
                v___x_3295_ = l_Lean_Name_Demangle_demangleSymbol___closed__1;
                v___x_3296_ = lean_string_append(v_val_3289_, v___x_3295_);
                v___x_3297_ = lean_string_append(v___x_3296_, v_snd_3284_);
                leanh::lean_dec(v_snd_3284_);
                if v_isShared_3294_ == 0 {
                    leanh::lean_ctor_set(v___x_3293_, 0, v___x_3297_);
                    v___x_3299_ = v___x_3293_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3300_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3300_, 0, v___x_3297_);
                    v___x_3299_ = v_reuseFailAlloc_3300_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3299_;
            }
            4 => {
                leanh::lean_inc(v_val_3311_);
                v___x_3315_ =
                    l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isAllDigits(
                        v_val_3311_,
                    );
                if v___x_3315_ == 0 {
                    leanh::lean_del_object(v___x_3313_);
                    leanh::lean_dec(v_val_3311_);
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v_fst_3283_);
                    v___x_3316_ = l_Lean_Name_Demangle_demangleSymbol___closed__6;
                    v___x_3317_ = lean_string_append(v___x_3316_, v_val_3311_);
                    leanh::lean_dec(v_val_3311_);
                    v___x_3318_ = l_Lean_Name_Demangle_demangleSymbol___closed__7;
                    v_r_3319_ = lean_string_append(v___x_3317_, v___x_3318_);
                    v___x_3320_ = lean_string_utf8_byte_size(v_snd_3284_);
                    v___x_3321_ = lean_nat_dec_eq(v___x_3320_, v___x_3280_);
                    if v___x_3321_ == 0 {
                        v___x_3322_ = l_Lean_Name_Demangle_demangleSymbol___closed__1;
                        v___x_3323_ = lean_string_append(v_r_3319_, v___x_3322_);
                        v___x_3324_ = lean_string_append(v___x_3323_, v_snd_3284_);
                        leanh::lean_dec(v_snd_3284_);
                        if v_isShared_3314_ == 0 {
                            leanh::lean_ctor_set(v___x_3313_, 0, v___x_3324_);
                            v___x_3326_ = v___x_3313_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_3327_ =
                                leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3327_, 0, v___x_3324_);
                            v___x_3326_ = v_reuseFailAlloc_3327_;
                            state = 5;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_snd_3284_);
                        if v_isShared_3314_ == 0 {
                            leanh::lean_ctor_set(v___x_3313_, 0, v_r_3319_);
                            v___x_3329_ = v___x_3313_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_3330_ =
                                leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3330_, 0, v_r_3319_);
                            v___x_3329_ = v_reuseFailAlloc_3330_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            5 => {
                return v___x_3326_;
            }
            6 => {
                return v___x_3329_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_skipWhile(
    mut v_s_3333_: *mut leanh::LeanObject,
    mut v_pos_3334_: *mut leanh::LeanObject,
    mut v_pred_3335_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3337_: u8 = 0;
    let mut v___x_3338_: u32 = 0;
    let mut v___x_3339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3341_: u8 = 0;
    let mut v___x_3342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3336_ = lean_string_utf8_byte_size(v_s_3333_);
                v___x_3337_ = lean_nat_dec_eq(v_pos_3334_, v___x_3336_);
                if v___x_3337_ == 0 {
                    v___x_3338_ = lean_string_utf8_get_fast(v_s_3333_, v_pos_3334_);
                    v___x_3339_ = leanh::lean_box_uint32(v___x_3338_);
                    leanh::lean_inc_ref(v_pred_3335_);
                    v___x_3340_ = leanh::lean_apply_1(v_pred_3335_, v___x_3339_);
                    v___x_3341_ = (leanh::lean_unbox(v___x_3340_) as u8);
                    if v___x_3341_ == 0 {
                        leanh::lean_dec_ref(v_pred_3335_);
                        return v_pos_3334_;
                    } else {
                        v___x_3342_ = lean_string_utf8_next_fast(v_s_3333_, v_pos_3334_);
                        leanh::lean_dec(v_pos_3334_);
                        v_pos_3334_ = v___x_3342_;
                        state = 0;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_pred_3335_);
                    return v_pos_3334_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_skipWhile___boxed(
    mut v_s_3344_: *mut leanh::LeanObject,
    mut v_pos_3345_: *mut leanh::LeanObject,
    mut v_pred_3346_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3347_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3347_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_skipWhile(
        v_s_3344_,
        v_pos_3345_,
        v_pred_3346_,
    );
    leanh::lean_dec_ref(v_s_3344_);
    return v_res_3347_;
}
pub unsafe fn l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_splitAt_u2082(
    mut v_s_3348_: *mut leanh::LeanObject,
    mut v_p_u2081_3349_: *mut leanh::LeanObject,
    mut v_p_u2082_3350_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3351_ = leanh::lean_unsigned_to_nat(0);
    v___x_3352_ = lean_string_utf8_extract(v_s_3348_, v___x_3351_, v_p_u2081_3349_);
    v___x_3353_ = lean_string_utf8_extract(v_s_3348_, v_p_u2081_3349_, v_p_u2082_3350_);
    v___x_3354_ = lean_string_utf8_byte_size(v_s_3348_);
    v___x_3355_ = lean_string_utf8_extract(v_s_3348_, v_p_u2082_3350_, v___x_3354_);
    v___x_3356_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3356_, 0, v___x_3353_);
    leanh::lean_ctor_set(v___x_3356_, 1, v___x_3355_);
    v___x_3357_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3357_, 0, v___x_3352_);
    leanh::lean_ctor_set(v___x_3357_, 1, v___x_3356_);
    return v___x_3357_;
}
pub unsafe fn l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_splitAt_u2082___boxed(
    mut v_s_3358_: *mut leanh::LeanObject,
    mut v_p_u2081_3359_: *mut leanh::LeanObject,
    mut v_p_u2082_3360_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3361_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3361_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_splitAt_u2082(
        v_s_3358_,
        v_p_u2081_3359_,
        v_p_u2082_3360_,
    );
    leanh::lean_dec(v_p_u2082_3360_);
    leanh::lean_dec(v_p_u2081_3359_);
    leanh::lean_dec_ref(v_s_3358_);
    return v_res_3361_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1___redArg(
    mut v___x_3362_: *mut leanh::LeanObject,
    mut v___x_3363_: *mut leanh::LeanObject,
    mut v_line_3364_: *mut leanh::LeanObject,
    mut v_a_3365_: *mut leanh::LeanObject,
    mut v_b_3366_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_startInclusive_3367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_3368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3370_: u8 = 0;
    let mut v___x_3371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3374_: u8 = 0;
    let mut v___x_3375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: u32 = 0;
    let mut v___x_3380_: u32 = 0;
    let mut v___x_3381_: u8 = 0;
    let mut v___x_3382_: u32 = 0;
    let mut v___x_3383_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_startInclusive_3367_ = leanh::lean_ctor_get(v___x_3362_, 1);
                v_endExclusive_3368_ = leanh::lean_ctor_get(v___x_3362_, 2);
                v___x_3369_ = lean_nat_sub(v_endExclusive_3368_, v_startInclusive_3367_);
                v___x_3370_ = lean_nat_dec_eq(v_a_3365_, v___x_3369_);
                leanh::lean_dec(v___x_3369_);
                if v___x_3370_ == 0 {
                    v___x_3371_ = leanh::lean_box(0);
                    v___x_3372_ = lean_nat_add(v___x_3363_, v_a_3365_);
                    v___x_3379_ = lean_string_utf8_get_fast(v_line_3364_, v___x_3372_);
                    v___x_3380_ = 43;
                    v___x_3381_ = lean_uint32_dec_eq(v___x_3379_, v___x_3380_);
                    if v___x_3381_ == 0 {
                        v___x_3382_ = 41;
                        v___x_3383_ = lean_uint32_dec_eq(v___x_3379_, v___x_3382_);
                        v___y_3374_ = v___x_3383_;
                        state = 1;
                        continue;
                    } else {
                        v___y_3374_ = v___x_3381_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_3365_);
                    leanh::lean_inc(v_b_3366_);
                    return v_b_3366_;
                }
            }
            1 => {
                if v___y_3374_ == 0 {
                    leanh::lean_dec(v_a_3365_);
                    v___x_3375_ = lean_string_utf8_next_fast(v_line_3364_, v___x_3372_);
                    leanh::lean_dec(v___x_3372_);
                    v___x_3376_ = lean_nat_sub(v___x_3375_, v___x_3363_);
                    v_a_3365_ = v___x_3376_;
                    v_b_3366_ = v___x_3371_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v___x_3372_);
                    v___x_3378_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3378_, 0, v_a_3365_);
                    return v___x_3378_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1___redArg___boxed(
    mut v___x_3384_: *mut leanh::LeanObject,
    mut v___x_3385_: *mut leanh::LeanObject,
    mut v_line_3386_: *mut leanh::LeanObject,
    mut v_a_3387_: *mut leanh::LeanObject,
    mut v_b_3388_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3389_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3389_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1___redArg(v___x_3384_, v___x_3385_, v_line_3386_, v_a_3387_, v_b_3388_);
    leanh::lean_dec(v_b_3388_);
    leanh::lean_dec_ref(v_line_3386_);
    leanh::lean_dec(v___x_3385_);
    leanh::lean_dec_ref(v___x_3384_);
    return v_res_3389_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0___redArg(
    mut v___x_3390_: *mut leanh::LeanObject,
    mut v_line_3391_: *mut leanh::LeanObject,
    mut v_a_3392_: *mut leanh::LeanObject,
    mut v_b_3393_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_startInclusive_3394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_3395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3397_: u8 = 0;
    let mut v___x_3398_: u32 = 0;
    let mut v___x_3399_: u32 = 0;
    let mut v___x_3400_: u8 = 0;
    let mut v___x_3401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_startInclusive_3394_ = leanh::lean_ctor_get(v___x_3390_, 1);
                v_endExclusive_3395_ = leanh::lean_ctor_get(v___x_3390_, 2);
                v___x_3396_ = lean_nat_sub(v_endExclusive_3395_, v_startInclusive_3394_);
                v___x_3397_ = lean_nat_dec_eq(v_a_3392_, v___x_3396_);
                leanh::lean_dec(v___x_3396_);
                if v___x_3397_ == 0 {
                    v___x_3398_ = lean_string_utf8_get_fast(v_line_3391_, v_a_3392_);
                    v___x_3399_ = 40;
                    v___x_3400_ = lean_uint32_dec_eq(v___x_3398_, v___x_3399_);
                    if v___x_3400_ == 0 {
                        v___x_3401_ = leanh::lean_box(0);
                        v___x_3402_ = lean_string_utf8_next_fast(v_line_3391_, v_a_3392_);
                        leanh::lean_dec(v_a_3392_);
                        v_a_3392_ = v___x_3402_;
                        v_b_3393_ = v___x_3401_;
                        state = 0;
                        continue;
                    } else {
                        v___x_3404_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3404_, 0, v_a_3392_);
                        return v___x_3404_;
                    }
                } else {
                    leanh::lean_dec(v_a_3392_);
                    leanh::lean_inc(v_b_3393_);
                    return v_b_3393_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0___redArg___boxed(
    mut v___x_3405_: *mut leanh::LeanObject,
    mut v_line_3406_: *mut leanh::LeanObject,
    mut v_a_3407_: *mut leanh::LeanObject,
    mut v_b_3408_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3409_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3409_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0___redArg(v___x_3405_, v_line_3406_, v_a_3407_, v_b_3408_);
    leanh::lean_dec(v_b_3408_);
    leanh::lean_dec_ref(v_line_3406_);
    leanh::lean_dec_ref(v___x_3405_);
    return v_res_3409_;
}
pub unsafe fn l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux(
    mut v_line_3410_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_searcher_3411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3417_: u8 = 0;
    let mut v___x_3418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3424_: u8 = 0;
    let mut v___x_3425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: u8 = 0;
    let mut v___x_3427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3431_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_searcher_3411_ = leanh::lean_unsigned_to_nat(0);
                v___x_3412_ = lean_string_utf8_byte_size(v_line_3410_);
                leanh::lean_inc_ref(v_line_3410_);
                v___x_3413_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3413_, 0, v_line_3410_);
                leanh::lean_ctor_set(v___x_3413_, 1, v_searcher_3411_);
                leanh::lean_ctor_set(v___x_3413_, 2, v___x_3412_);
                v___x_3414_ = leanh::lean_box(0);
                v___x_3415_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0___redArg(v___x_3413_, v_line_3410_, v_searcher_3411_, v___x_3414_);
                leanh::lean_dec_ref_known(v___x_3413_, 3);
                if leanh::lean_obj_tag(v___x_3415_) == 0 {
                    leanh::lean_dec_ref(v_line_3410_);
                    return v___x_3414_;
                } else {
                    v_val_3416_ = leanh::lean_ctor_get(v___x_3415_, 0);
                    leanh::lean_inc(v_val_3416_);
                    leanh::lean_dec_ref_known(v___x_3415_, 1);
                    v___x_3417_ = lean_nat_dec_eq(v_val_3416_, v___x_3412_);
                    if v___x_3417_ == 0 {
                        v___x_3418_ = lean_string_utf8_next_fast(v_line_3410_, v_val_3416_);
                        leanh::lean_dec(v_val_3416_);
                        leanh::lean_inc_ref(v_line_3410_);
                        v___x_3419_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        leanh::lean_ctor_set(v___x_3419_, 0, v_line_3410_);
                        leanh::lean_ctor_set(v___x_3419_, 1, v___x_3418_);
                        leanh::lean_ctor_set(v___x_3419_, 2, v___x_3412_);
                        v___x_3420_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1___redArg(v___x_3419_, v___x_3418_, v_line_3410_, v_searcher_3411_, v___x_3414_);
                        leanh::lean_dec_ref_known(v___x_3419_, 3);
                        if leanh::lean_obj_tag(v___x_3420_) == 0 {
                            leanh::lean_dec_ref(v_line_3410_);
                            return v___x_3414_;
                        } else {
                            v_val_3421_ = leanh::lean_ctor_get(v___x_3420_, 0);
                            v_isSharedCheck_3431_ =
                                (!leanh::lean_is_exclusive(v___x_3420_)) as u8;
                            if v_isSharedCheck_3431_ == 0 {
                                v___x_3423_ = v___x_3420_;
                                v_isShared_3424_ = v_isSharedCheck_3431_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_val_3421_);
                                leanh::lean_dec(v___x_3420_);
                                v___x_3423_ = leanh::lean_box(0);
                                v_isShared_3424_ = v_isSharedCheck_3431_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_val_3416_);
                        leanh::lean_dec_ref(v_line_3410_);
                        return v___x_3414_;
                    }
                }
            }
            1 => {
                v___x_3425_ = lean_nat_add(v___x_3418_, v_val_3421_);
                leanh::lean_dec(v_val_3421_);
                v___x_3426_ = lean_nat_dec_eq(v___x_3425_, v___x_3418_);
                if v___x_3426_ == 0 {
                    v___x_3427_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_splitAt_u2082(v_line_3410_, v___x_3418_, v___x_3425_);
                    leanh::lean_dec(v___x_3425_);
                    leanh::lean_dec_ref(v_line_3410_);
                    if v_isShared_3424_ == 0 {
                        leanh::lean_ctor_set(v___x_3423_, 0, v___x_3427_);
                        v___x_3429_ = v___x_3423_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3430_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3430_, 0, v___x_3427_);
                        v___x_3429_ = v_reuseFailAlloc_3430_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_3425_);
                    leanh::lean_del_object(v___x_3423_);
                    leanh::lean_dec_ref(v_line_3410_);
                    return v___x_3414_;
                }
            }
            2 => {
                return v___x_3429_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0(
    mut v___x_3432_: *mut leanh::LeanObject,
    mut v_line_3433_: *mut leanh::LeanObject,
    mut v_inst_3434_: *mut leanh::LeanObject,
    mut v_R_3435_: *mut leanh::LeanObject,
    mut v_a_3436_: *mut leanh::LeanObject,
    mut v_b_3437_: *mut leanh::LeanObject,
    mut v_c_3438_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3439_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3439_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0___redArg(v___x_3432_, v_line_3433_, v_a_3436_, v_b_3437_);
    return v___x_3439_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0___boxed(
    mut v___x_3440_: *mut leanh::LeanObject,
    mut v_line_3441_: *mut leanh::LeanObject,
    mut v_inst_3442_: *mut leanh::LeanObject,
    mut v_R_3443_: *mut leanh::LeanObject,
    mut v_a_3444_: *mut leanh::LeanObject,
    mut v_b_3445_: *mut leanh::LeanObject,
    mut v_c_3446_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3447_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3447_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0(v___x_3440_, v_line_3441_, v_inst_3442_, v_R_3443_, v_a_3444_, v_b_3445_, v_c_3446_);
    leanh::lean_dec(v_b_3445_);
    leanh::lean_dec_ref(v_line_3441_);
    leanh::lean_dec_ref(v___x_3440_);
    return v_res_3447_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1(
    mut v___x_3448_: *mut leanh::LeanObject,
    mut v___x_3449_: *mut leanh::LeanObject,
    mut v_line_3450_: *mut leanh::LeanObject,
    mut v_inst_3451_: *mut leanh::LeanObject,
    mut v_R_3452_: *mut leanh::LeanObject,
    mut v_a_3453_: *mut leanh::LeanObject,
    mut v_b_3454_: *mut leanh::LeanObject,
    mut v_c_3455_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3456_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3456_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1___redArg(v___x_3448_, v___x_3449_, v_line_3450_, v_a_3453_, v_b_3454_);
    return v___x_3456_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1___boxed(
    mut v___x_3457_: *mut leanh::LeanObject,
    mut v___x_3458_: *mut leanh::LeanObject,
    mut v_line_3459_: *mut leanh::LeanObject,
    mut v_inst_3460_: *mut leanh::LeanObject,
    mut v_R_3461_: *mut leanh::LeanObject,
    mut v_a_3462_: *mut leanh::LeanObject,
    mut v_b_3463_: *mut leanh::LeanObject,
    mut v_c_3464_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3465_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3465_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1(v___x_3457_, v___x_3458_, v_line_3459_, v_inst_3460_, v_R_3461_, v_a_3462_, v_b_3463_, v_c_3464_);
    leanh::lean_dec(v_b_3463_);
    leanh::lean_dec_ref(v_line_3459_);
    leanh::lean_dec(v___x_3458_);
    leanh::lean_dec_ref(v___x_3457_);
    return v_res_3465_;
}
pub unsafe fn l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___lam__0(
    mut v_x_3466_: u32,
) -> u8 {
    let mut v___x_3467_: u32 = 0;
    let mut v___x_3468_: u8 = 0;
    v___x_3467_ = 32;
    v___x_3468_ = lean_uint32_dec_eq(v_x_3466_, v___x_3467_);
    return v___x_3468_;
}
pub unsafe fn l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___lam__0___boxed(
    mut v_x_3469_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_2608__boxed_3470_: u32 = 0;
    let mut v_res_3471_: u8 = 0;
    let mut v_r_3472_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_2608__boxed_3470_ = leanh::lean_unbox_uint32(v_x_3469_);
    leanh::lean_dec(v_x_3469_);
    v_res_3471_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___lam__0(v_x_2608__boxed_3470_);
    v_r_3472_ = leanh::lean_box((v_res_3471_) as usize);
    return v_r_3472_;
}
pub unsafe fn l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___lam__1(
    mut v_x_3473_: u32,
) -> u8 {
    let mut v___y_3475_: u8 = 0;
    let mut v___x_3476_: u32 = 0;
    let mut v___x_3477_: u8 = 0;
    let mut v___x_3478_: u32 = 0;
    let mut v___x_3479_: u8 = 0;
    let mut v___y_3481_: u8 = 0;
    let mut v___x_3482_: u32 = 0;
    let mut v___x_3483_: u8 = 0;
    let mut v___x_3484_: u32 = 0;
    let mut v___x_3485_: u8 = 0;
    let mut v___x_3486_: u32 = 0;
    let mut v___x_3487_: u8 = 0;
    let mut v___x_3488_: u32 = 0;
    let mut v___x_3489_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3486_ = 48;
                v___x_3487_ = lean_uint32_dec_le(v___x_3486_, v_x_3473_);
                if v___x_3487_ == 0 {
                    v___y_3481_ = v___x_3487_;
                    state = 2;
                    continue;
                } else {
                    v___x_3488_ = 57;
                    v___x_3489_ = lean_uint32_dec_le(v_x_3473_, v___x_3488_);
                    v___y_3481_ = v___x_3489_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                if v___y_3475_ == 0 {
                    v___x_3476_ = 65;
                    v___x_3477_ = lean_uint32_dec_le(v___x_3476_, v_x_3473_);
                    if v___x_3477_ == 0 {
                        return v___x_3477_;
                    } else {
                        v___x_3478_ = 70;
                        v___x_3479_ = lean_uint32_dec_le(v_x_3473_, v___x_3478_);
                        return v___x_3479_;
                    }
                } else {
                    return v___y_3475_;
                }
            }
            2 => {
                if v___y_3481_ == 0 {
                    v___x_3482_ = 97;
                    v___x_3483_ = lean_uint32_dec_le(v___x_3482_, v_x_3473_);
                    if v___x_3483_ == 0 {
                        v___y_3475_ = v___x_3483_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3484_ = 102;
                        v___x_3485_ = lean_uint32_dec_le(v_x_3473_, v___x_3484_);
                        v___y_3475_ = v___x_3485_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___y_3481_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___lam__1___boxed(
    mut v_x_3490_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_2615__boxed_3491_: u32 = 0;
    let mut v_res_3492_: u8 = 0;
    let mut v_r_3493_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_2615__boxed_3491_ = leanh::lean_unbox_uint32(v_x_3490_);
    leanh::lean_dec(v_x_3490_);
    v_res_3492_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___lam__1(v_x_2615__boxed_3491_);
    v_r_3493_ = leanh::lean_box((v_res_3492_) as usize);
    return v_r_3493_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0___redArg(
    mut v___x_3494_: *mut leanh::LeanObject,
    mut v_line_3495_: *mut leanh::LeanObject,
    mut v___x_3496_: *mut leanh::LeanObject,
    mut v___x_3497_: *mut leanh::LeanObject,
    mut v_a_3498_: *mut leanh::LeanObject,
    mut v_b_3499_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3506_: u8 = 0;
    let mut v___x_3507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3514_: u8 = 0;
    let mut v_needle_3515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_table_3516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stackPos_3517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_needlePos_3518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3521_: u8 = 0;
    let mut v_str_3522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_3523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_3524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_basePos_3525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3529_: u8 = 0;
    let mut v___x_3530_: u8 = 0;
    let mut v___x_3531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stackByte_3534_: u8 = 0;
    let mut v___x_3535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_patByte_3536_: u8 = 0;
    let mut v___x_3537_: u8 = 0;
    let mut v___x_3538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3539_: u8 = 0;
    let mut v___x_3540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNeedlePos_3542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: u8 = 0;
    let mut v___x_3545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextStackPos_3548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextStackPos_3555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextStackPos_3561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextNeedlePos_3562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3563_: u8 = 0;
    let mut v___x_3565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3571_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3500_ = leanh::lean_box(0);
                match leanh::lean_obj_tag(v_a_3498_) {
                    0 => {
                        v_pos_3501_ = leanh::lean_ctor_get(v_a_3498_, 0);
                        leanh::lean_inc(v_pos_3501_);
                        leanh::lean_dec_ref_known(v_a_3498_, 1);
                        v___x_3502_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3502_, 0, v_pos_3501_);
                        return v___x_3502_;
                    }
                    1 => {
                        v_pos_3503_ = leanh::lean_ctor_get(v_a_3498_, 0);
                        v_isSharedCheck_3514_ = (!leanh::lean_is_exclusive(v_a_3498_)) as u8;
                        if v_isSharedCheck_3514_ == 0 {
                            v___x_3505_ = v_a_3498_;
                            v_isShared_3506_ = v_isSharedCheck_3514_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_pos_3503_);
                            leanh::lean_dec(v_a_3498_);
                            v___x_3505_ = leanh::lean_box(0);
                            v_isShared_3506_ = v_isSharedCheck_3514_;
                            state = 1;
                            continue;
                        }
                    }
                    2 => {
                        v_needle_3515_ = leanh::lean_ctor_get(v_a_3498_, 0);
                        v_table_3516_ = leanh::lean_ctor_get(v_a_3498_, 1);
                        v_stackPos_3517_ = leanh::lean_ctor_get(v_a_3498_, 2);
                        v_needlePos_3518_ = leanh::lean_ctor_get(v_a_3498_, 3);
                        v_isSharedCheck_3571_ = (!leanh::lean_is_exclusive(v_a_3498_)) as u8;
                        if v_isSharedCheck_3571_ == 0 {
                            v___x_3520_ = v_a_3498_;
                            v_isShared_3521_ = v_isSharedCheck_3571_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_needlePos_3518_);
                            leanh::lean_inc(v_stackPos_3517_);
                            leanh::lean_inc(v_table_3516_);
                            leanh::lean_inc(v_needle_3515_);
                            leanh::lean_dec(v_a_3498_);
                            v___x_3520_ = leanh::lean_box(0);
                            v_isShared_3521_ = v_isSharedCheck_3571_;
                            state = 3;
                            continue;
                        }
                    }
                    _ => {
                        leanh::lean_inc(v_b_3499_);
                        return v_b_3499_;
                    }
                }
            }
            1 => {
                v___x_3507_ = lean_nat_add(v___x_3494_, v_pos_3503_);
                leanh::lean_dec(v_pos_3503_);
                v___x_3508_ = lean_string_utf8_next_fast(v_line_3495_, v___x_3507_);
                leanh::lean_dec(v___x_3507_);
                v___x_3509_ = lean_nat_sub(v___x_3508_, v___x_3494_);
                if v_isShared_3506_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3505_, 0);
                    leanh::lean_ctor_set(v___x_3505_, 0, v___x_3509_);
                    v___x_3511_ = v___x_3505_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3513_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3513_, 0, v___x_3509_);
                    v___x_3511_ = v_reuseFailAlloc_3513_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_3498_ = v___x_3511_;
                v_b_3499_ = v___x_3500_;
                state = 0;
                continue;
            }
            3 => {
                v_str_3522_ = leanh::lean_ctor_get(v_needle_3515_, 0);
                v_startInclusive_3523_ = leanh::lean_ctor_get(v_needle_3515_, 1);
                v_endExclusive_3524_ = leanh::lean_ctor_get(v_needle_3515_, 2);
                v_basePos_3525_ = lean_nat_sub(v_stackPos_3517_, v_needlePos_3518_);
                v___x_3526_ = lean_nat_sub(v_endExclusive_3524_, v_startInclusive_3523_);
                v___x_3527_ = lean_nat_add(v_basePos_3525_, v___x_3526_);
                v___x_3528_ = lean_nat_sub(v___x_3497_, v___x_3494_);
                v___x_3529_ = lean_nat_dec_le(v___x_3527_, v___x_3528_);
                leanh::lean_dec(v___x_3527_);
                if v___x_3529_ == 0 {
                    leanh::lean_dec(v___x_3526_);
                    leanh::lean_del_object(v___x_3520_);
                    leanh::lean_dec(v_needlePos_3518_);
                    leanh::lean_dec(v_stackPos_3517_);
                    leanh::lean_dec_ref(v_table_3516_);
                    leanh::lean_dec_ref(v_needle_3515_);
                    v___x_3530_ = lean_nat_dec_lt(v_basePos_3525_, v___x_3528_);
                    leanh::lean_dec(v___x_3528_);
                    leanh::lean_dec(v_basePos_3525_);
                    if v___x_3530_ == 0 {
                        leanh::lean_inc(v_b_3499_);
                        return v_b_3499_;
                    } else {
                        v___x_3531_ = leanh::lean_box(3);
                        v_a_3498_ = v___x_3531_;
                        v_b_3499_ = v___x_3500_;
                        state = 0;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_3528_);
                    leanh::lean_dec(v_basePos_3525_);
                    v___x_3533_ = lean_nat_add(v___x_3494_, v_stackPos_3517_);
                    v_stackByte_3534_ = lean_string_get_byte_fast(v_line_3495_, v___x_3533_);
                    v___x_3535_ = lean_nat_add(v_startInclusive_3523_, v_needlePos_3518_);
                    v_patByte_3536_ = lean_string_get_byte_fast(v_str_3522_, v___x_3535_);
                    v___x_3537_ = lean_uint8_dec_eq(v_stackByte_3534_, v_patByte_3536_);
                    if v___x_3537_ == 0 {
                        leanh::lean_dec(v___x_3526_);
                        v___x_3538_ = leanh::lean_unsigned_to_nat(0);
                        v___x_3539_ = lean_nat_dec_eq(v_needlePos_3518_, v___x_3538_);
                        if v___x_3539_ == 0 {
                            v___x_3540_ = leanh::lean_unsigned_to_nat(1);
                            v___x_3541_ = lean_nat_sub(v_needlePos_3518_, v___x_3540_);
                            leanh::lean_dec(v_needlePos_3518_);
                            v_newNeedlePos_3542_ =
                                lean_array_fget_borrowed(v_table_3516_, v___x_3541_);
                            leanh::lean_dec(v___x_3541_);
                            v___x_3543_ = lean_nat_dec_eq(v_newNeedlePos_3542_, v___x_3538_);
                            if v___x_3543_ == 0 {
                                leanh::lean_inc(v_newNeedlePos_3542_);
                                if v_isShared_3521_ == 0 {
                                    leanh::lean_ctor_set(
                                        v___x_3520_,
                                        3,
                                        v_newNeedlePos_3542_,
                                    );
                                    v___x_3545_ = v___x_3520_;
                                    state = 4;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3547_ =
                                        leanh::lean_alloc_ctor(2, 4, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3547_,
                                        0,
                                        v_needle_3515_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3547_,
                                        1,
                                        v_table_3516_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3547_,
                                        2,
                                        v_stackPos_3517_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3547_,
                                        3,
                                        v_newNeedlePos_3542_,
                                    );
                                    v___x_3545_ = v_reuseFailAlloc_3547_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                v_nextStackPos_3548_ =
                                    l_String_Slice_posGE___redArg(v___x_3496_, v_stackPos_3517_);
                                if v_isShared_3521_ == 0 {
                                    leanh::lean_ctor_set(v___x_3520_, 3, v___x_3538_);
                                    leanh::lean_ctor_set(
                                        v___x_3520_,
                                        2,
                                        v_nextStackPos_3548_,
                                    );
                                    v___x_3550_ = v___x_3520_;
                                    state = 5;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3552_ =
                                        leanh::lean_alloc_ctor(2, 4, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3552_,
                                        0,
                                        v_needle_3515_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3552_,
                                        1,
                                        v_table_3516_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3552_,
                                        2,
                                        v_nextStackPos_3548_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3552_,
                                        3,
                                        v___x_3538_,
                                    );
                                    v___x_3550_ = v_reuseFailAlloc_3552_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_needlePos_3518_);
                            v___x_3553_ = leanh::lean_unsigned_to_nat(1);
                            v___x_3554_ = lean_nat_add(v_stackPos_3517_, v___x_3553_);
                            leanh::lean_dec(v_stackPos_3517_);
                            v_nextStackPos_3555_ =
                                l_String_Slice_posGE___redArg(v___x_3496_, v___x_3554_);
                            if v_isShared_3521_ == 0 {
                                leanh::lean_ctor_set(v___x_3520_, 3, v___x_3538_);
                                leanh::lean_ctor_set(v___x_3520_, 2, v_nextStackPos_3555_);
                                v___x_3557_ = v___x_3520_;
                                state = 6;
                                continue;
                            } else {
                                v_reuseFailAlloc_3559_ =
                                    leanh::lean_alloc_ctor(2, 4, (0) as u32);
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_3559_,
                                    0,
                                    v_needle_3515_,
                                );
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_3559_,
                                    1,
                                    v_table_3516_,
                                );
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_3559_,
                                    2,
                                    v_nextStackPos_3555_,
                                );
                                leanh::lean_ctor_set(v_reuseFailAlloc_3559_, 3, v___x_3538_);
                                v___x_3557_ = v_reuseFailAlloc_3559_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        v___x_3560_ = leanh::lean_unsigned_to_nat(1);
                        v_nextStackPos_3561_ = lean_nat_add(v_stackPos_3517_, v___x_3560_);
                        leanh::lean_dec(v_stackPos_3517_);
                        v_nextNeedlePos_3562_ = lean_nat_add(v_needlePos_3518_, v___x_3560_);
                        leanh::lean_dec(v_needlePos_3518_);
                        v___x_3563_ = lean_nat_dec_eq(v_nextNeedlePos_3562_, v___x_3526_);
                        leanh::lean_dec(v___x_3526_);
                        if v___x_3563_ == 0 {
                            if v_isShared_3521_ == 0 {
                                leanh::lean_ctor_set(v___x_3520_, 3, v_nextNeedlePos_3562_);
                                leanh::lean_ctor_set(v___x_3520_, 2, v_nextStackPos_3561_);
                                v___x_3565_ = v___x_3520_;
                                state = 7;
                                continue;
                            } else {
                                v_reuseFailAlloc_3567_ =
                                    leanh::lean_alloc_ctor(2, 4, (0) as u32);
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_3567_,
                                    0,
                                    v_needle_3515_,
                                );
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_3567_,
                                    1,
                                    v_table_3516_,
                                );
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_3567_,
                                    2,
                                    v_nextStackPos_3561_,
                                );
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_3567_,
                                    3,
                                    v_nextNeedlePos_3562_,
                                );
                                v___x_3565_ = v_reuseFailAlloc_3567_;
                                state = 7;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_3520_);
                            leanh::lean_dec_ref(v_table_3516_);
                            leanh::lean_dec_ref(v_needle_3515_);
                            v___x_3568_ = lean_nat_sub(v_nextStackPos_3561_, v_nextNeedlePos_3562_);
                            leanh::lean_dec(v_nextNeedlePos_3562_);
                            leanh::lean_dec(v_nextStackPos_3561_);
                            v___x_3569_ = l_String_Slice_pos_x21(v___x_3496_, v___x_3568_);
                            leanh::lean_dec(v___x_3568_);
                            v___x_3570_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_3570_, 0, v___x_3569_);
                            return v___x_3570_;
                        }
                    }
                }
            }
            4 => {
                v_a_3498_ = v___x_3545_;
                v_b_3499_ = v___x_3500_;
                state = 0;
                continue;
            }
            5 => {
                v_a_3498_ = v___x_3550_;
                v_b_3499_ = v___x_3500_;
                state = 0;
                continue;
            }
            6 => {
                v_a_3498_ = v___x_3557_;
                v_b_3499_ = v___x_3500_;
                state = 0;
                continue;
            }
            7 => {
                v_a_3498_ = v___x_3565_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0___redArg___boxed(
    mut v___x_3572_: *mut leanh::LeanObject,
    mut v_line_3573_: *mut leanh::LeanObject,
    mut v___x_3574_: *mut leanh::LeanObject,
    mut v___x_3575_: *mut leanh::LeanObject,
    mut v_a_3576_: *mut leanh::LeanObject,
    mut v_b_3577_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3578_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3578_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0___redArg(v___x_3572_, v_line_3573_, v___x_3574_, v___x_3575_, v_a_3576_, v_b_3577_);
    leanh::lean_dec(v_b_3577_);
    leanh::lean_dec(v___x_3575_);
    leanh::lean_dec_ref(v___x_3574_);
    leanh::lean_dec_ref(v_line_3573_);
    leanh::lean_dec(v___x_3572_);
    return v_res_3578_;
}
pub unsafe fn _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_3583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3584_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3583_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__3;
    v___x_3584_ = lean_string_utf8_byte_size(v___x_3583_);
    return v___x_3584_;
}
pub unsafe fn _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__5()
-> u8 {
    let mut v___x_3585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3587_: u8 = 0;
    v___x_3585_ = leanh::lean_unsigned_to_nat(0);
    v___x_3586_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__4_once), _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__4);
    v___x_3587_ = lean_nat_dec_eq(v___x_3586_, v___x_3585_);
    return v___x_3587_;
}
pub unsafe fn _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_3588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3591_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3588_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__4_once), _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__4);
    v___x_3589_ = leanh::lean_unsigned_to_nat(0);
    v___x_3590_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__3;
    v___x_3591_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_3591_, 0, v___x_3590_);
    leanh::lean_ctor_set(v___x_3591_, 1, v___x_3589_);
    leanh::lean_ctor_set(v___x_3591_, 2, v___x_3588_);
    return v___x_3591_;
}
pub unsafe fn _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_3592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3593_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3592_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__6_once), _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__6);
    v___x_3593_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_3592_);
    return v___x_3593_;
}
pub unsafe fn _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_3594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3594_ = leanh::lean_unsigned_to_nat(0);
    v___x_3595_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__7_once), _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__7);
    v___x_3596_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__6_once), _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__6);
    v___x_3597_ = leanh::lean_alloc_ctor(2, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_3597_, 0, v___x_3596_);
    leanh::lean_ctor_set(v___x_3597_, 1, v___x_3595_);
    leanh::lean_ctor_set(v___x_3597_, 2, v___x_3594_);
    leanh::lean_ctor_set(v___x_3597_, 3, v___x_3594_);
    return v___x_3597_;
}
pub unsafe fn _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_3598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3598_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__2;
    v___x_3599_ = lean_string_utf8_byte_size(v___x_3598_);
    return v___x_3599_;
}
pub unsafe fn _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__10()
-> u8 {
    let mut v___x_3600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3602_: u8 = 0;
    v___x_3600_ = leanh::lean_unsigned_to_nat(0);
    v___x_3601_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__9_once), _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__9);
    v___x_3602_ = lean_nat_dec_eq(v___x_3601_, v___x_3600_);
    return v___x_3602_;
}
pub unsafe fn _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_3603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3603_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__9_once), _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__9);
    v___x_3604_ = leanh::lean_unsigned_to_nat(0);
    v___x_3605_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__2;
    v___x_3606_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_3606_, 0, v___x_3605_);
    leanh::lean_ctor_set(v___x_3606_, 1, v___x_3604_);
    leanh::lean_ctor_set(v___x_3606_, 2, v___x_3603_);
    return v___x_3606_;
}
pub unsafe fn _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_3607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3608_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3607_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__11_once), _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__11);
    v___x_3608_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_3607_);
    return v___x_3608_;
}
pub unsafe fn _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_3609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3609_ = leanh::lean_unsigned_to_nat(0);
    v___x_3610_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__12), core::ptr::addr_of_mut!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__12_once), _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__12);
    v___x_3611_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__11_once), _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__11);
    v___x_3612_ = leanh::lean_alloc_ctor(2, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_3612_, 0, v___x_3611_);
    leanh::lean_ctor_set(v___x_3612_, 1, v___x_3610_);
    leanh::lean_ctor_set(v___x_3612_, 2, v___x_3609_);
    leanh::lean_ctor_set(v___x_3612_, 3, v___x_3609_);
    return v___x_3612_;
}
pub unsafe fn l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS(
    mut v_line_3613_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3617_: u8 = 0;
    let mut v___x_3618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3639_: u8 = 0;
    let mut v___x_3640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: u8 = 0;
    let mut v___x_3642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: u8 = 0;
    let mut v___x_3646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: u8 = 0;
    let mut v___x_3648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: u8 = 0;
    let mut v___x_3651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_3621_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__0;
                v___f_3622_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__1;
                v___x_3623_ = leanh::lean_unsigned_to_nat(0);
                v___x_3624_ = lean_string_utf8_byte_size(v_line_3613_);
                leanh::lean_inc_ref(v_line_3613_);
                v___x_3633_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3633_, 0, v_line_3613_);
                leanh::lean_ctor_set(v___x_3633_, 1, v___x_3623_);
                leanh::lean_ctor_set(v___x_3633_, 2, v___x_3624_);
                v___x_3650_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__10_once), _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__10);
                if v___x_3650_ == 0 {
                    v___x_3651_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__13), core::ptr::addr_of_mut!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__13_once), _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__13);
                    v___y_3635_ = v___x_3651_;
                    state = 3;
                    continue;
                } else {
                    v___x_3652_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__6;
                    v___y_3635_ = v___x_3652_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                v___x_3617_ = lean_nat_dec_eq(v___y_3616_, v___y_3615_);
                if v___x_3617_ == 0 {
                    v___x_3618_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_splitAt_u2082(v_line_3613_, v___y_3615_, v___y_3616_);
                    leanh::lean_dec(v___y_3616_);
                    leanh::lean_dec(v___y_3615_);
                    leanh::lean_dec_ref(v_line_3613_);
                    v___x_3619_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3619_, 0, v___x_3618_);
                    return v___x_3619_;
                } else {
                    leanh::lean_dec(v___y_3616_);
                    leanh::lean_dec(v___y_3615_);
                    leanh::lean_dec_ref(v_line_3613_);
                    v___x_3620_ = leanh::lean_box(0);
                    return v___x_3620_;
                }
            }
            2 => {
                leanh::lean_inc(v___y_3629_);
                v___x_3630_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0___redArg(v___y_3627_, v_line_3613_, v___y_3626_, v___x_3624_, v___y_3629_, v___y_3628_);
                leanh::lean_dec_ref(v___y_3626_);
                if leanh::lean_obj_tag(v___x_3630_) == 0 {
                    v___y_3615_ = v___y_3627_;
                    v___y_3616_ = v___x_3624_;
                    state = 1;
                    continue;
                } else {
                    v_val_3631_ = leanh::lean_ctor_get(v___x_3630_, 0);
                    leanh::lean_inc(v_val_3631_);
                    leanh::lean_dec_ref_known(v___x_3630_, 1);
                    v___x_3632_ = lean_nat_add(v___y_3627_, v_val_3631_);
                    leanh::lean_dec(v_val_3631_);
                    v___y_3615_ = v___y_3627_;
                    v___y_3616_ = v___x_3632_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_3636_ = leanh::lean_box(0);
                leanh::lean_inc(v___y_3635_);
                v___x_3637_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0___redArg(v_line_3613_, v___x_3633_, v___x_3624_, v___y_3635_, v___x_3636_);
                leanh::lean_dec_ref_known(v___x_3633_, 3);
                if leanh::lean_obj_tag(v___x_3637_) == 0 {
                    leanh::lean_dec_ref(v_line_3613_);
                    return v___x_3636_;
                } else {
                    v_val_3638_ = leanh::lean_ctor_get(v___x_3637_, 0);
                    leanh::lean_inc(v_val_3638_);
                    leanh::lean_dec_ref_known(v___x_3637_, 1);
                    v___x_3639_ = lean_nat_dec_eq(v_val_3638_, v___x_3624_);
                    if v___x_3639_ == 0 {
                        v___x_3640_ = lean_string_utf8_next_fast(v_line_3613_, v_val_3638_);
                        leanh::lean_dec(v_val_3638_);
                        v___x_3641_ = lean_nat_dec_eq(v___x_3640_, v___x_3624_);
                        if v___x_3641_ == 0 {
                            v___x_3642_ = lean_string_utf8_next_fast(v_line_3613_, v___x_3640_);
                            v___x_3643_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_skipWhile(v_line_3613_, v___x_3642_, v___f_3622_);
                            v___x_3644_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_skipWhile(v_line_3613_, v___x_3643_, v___f_3621_);
                            v___x_3645_ = lean_nat_dec_eq(v___x_3644_, v___x_3624_);
                            if v___x_3645_ == 0 {
                                leanh::lean_inc(v___x_3644_);
                                leanh::lean_inc_ref(v_line_3613_);
                                v___x_3646_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                                leanh::lean_ctor_set(v___x_3646_, 0, v_line_3613_);
                                leanh::lean_ctor_set(v___x_3646_, 1, v___x_3644_);
                                leanh::lean_ctor_set(v___x_3646_, 2, v___x_3624_);
                                v___x_3647_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__5_once), _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__5);
                                if v___x_3647_ == 0 {
                                    v___x_3648_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__8_once), _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__8);
                                    v___y_3626_ = v___x_3646_;
                                    v___y_3627_ = v___x_3644_;
                                    v___y_3628_ = v___x_3636_;
                                    v___y_3629_ = v___x_3648_;
                                    state = 2;
                                    continue;
                                } else {
                                    v___x_3649_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__6;
                                    v___y_3626_ = v___x_3646_;
                                    v___y_3627_ = v___x_3644_;
                                    v___y_3628_ = v___x_3636_;
                                    v___y_3629_ = v___x_3649_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v___x_3644_);
                                leanh::lean_dec_ref(v_line_3613_);
                                return v___x_3636_;
                            }
                        } else {
                            leanh::lean_dec_ref(v_line_3613_);
                            return v___x_3636_;
                        }
                    } else {
                        leanh::lean_dec(v_val_3638_);
                        leanh::lean_dec_ref(v_line_3613_);
                        return v___x_3636_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0(
    mut v___x_3653_: *mut leanh::LeanObject,
    mut v_line_3654_: *mut leanh::LeanObject,
    mut v___x_3655_: *mut leanh::LeanObject,
    mut v___x_3656_: *mut leanh::LeanObject,
    mut v_inst_3657_: *mut leanh::LeanObject,
    mut v_R_3658_: *mut leanh::LeanObject,
    mut v_a_3659_: *mut leanh::LeanObject,
    mut v_b_3660_: *mut leanh::LeanObject,
    mut v_c_3661_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3662_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3662_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0___redArg(v___x_3653_, v_line_3654_, v___x_3655_, v___x_3656_, v_a_3659_, v_b_3660_);
    return v___x_3662_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0___boxed(
    mut v___x_3663_: *mut leanh::LeanObject,
    mut v_line_3664_: *mut leanh::LeanObject,
    mut v___x_3665_: *mut leanh::LeanObject,
    mut v___x_3666_: *mut leanh::LeanObject,
    mut v_inst_3667_: *mut leanh::LeanObject,
    mut v_R_3668_: *mut leanh::LeanObject,
    mut v_a_3669_: *mut leanh::LeanObject,
    mut v_b_3670_: *mut leanh::LeanObject,
    mut v_c_3671_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3672_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3672_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0(v___x_3663_, v_line_3664_, v___x_3665_, v___x_3666_, v_inst_3667_, v_R_3668_, v_a_3669_, v_b_3670_, v_c_3671_);
    leanh::lean_dec(v_b_3670_);
    leanh::lean_dec(v___x_3666_);
    leanh::lean_dec_ref(v___x_3665_);
    leanh::lean_dec_ref(v_line_3664_);
    leanh::lean_dec(v___x_3663_);
    return v_res_3672_;
}
pub unsafe fn l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol(
    mut v_line_3673_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3674_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_line_3673_);
    v___x_3674_ =
        l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux(
            v_line_3673_,
        );
    if leanh::lean_obj_tag(v___x_3674_) == 0 {
        let mut v___x_3675_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3675_ =
            l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS(
                v_line_3673_,
            );
        return v___x_3675_;
    } else {
        leanh::lean_dec_ref(v_line_3673_);
        return v___x_3674_;
    }
}
pub unsafe fn l_Lean_Name_Demangle_demangleBtLine(
    mut v_line_3676_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3688_: u8 = 0;
    let mut v___x_3689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3694_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3677_ =
                    l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol(
                        v_line_3676_,
                    );
                if leanh::lean_obj_tag(v___x_3677_) == 0 {
                    v___x_3678_ = leanh::lean_box(0);
                    return v___x_3678_;
                } else {
                    v_val_3679_ = leanh::lean_ctor_get(v___x_3677_, 0);
                    leanh::lean_inc(v_val_3679_);
                    leanh::lean_dec_ref_known(v___x_3677_, 1);
                    v_snd_3680_ = leanh::lean_ctor_get(v_val_3679_, 1);
                    leanh::lean_inc(v_snd_3680_);
                    v_fst_3681_ = leanh::lean_ctor_get(v_val_3679_, 0);
                    leanh::lean_inc(v_fst_3681_);
                    leanh::lean_dec(v_val_3679_);
                    v_fst_3682_ = leanh::lean_ctor_get(v_snd_3680_, 0);
                    leanh::lean_inc(v_fst_3682_);
                    v_snd_3683_ = leanh::lean_ctor_get(v_snd_3680_, 1);
                    leanh::lean_inc(v_snd_3683_);
                    leanh::lean_dec(v_snd_3680_);
                    v___x_3684_ = l_Lean_Name_Demangle_demangleSymbol(v_fst_3682_);
                    if leanh::lean_obj_tag(v___x_3684_) == 0 {
                        leanh::lean_dec(v_snd_3683_);
                        leanh::lean_dec(v_fst_3681_);
                        return v___x_3684_;
                    } else {
                        v_val_3685_ = leanh::lean_ctor_get(v___x_3684_, 0);
                        v_isSharedCheck_3694_ =
                            (!leanh::lean_is_exclusive(v___x_3684_)) as u8;
                        if v_isSharedCheck_3694_ == 0 {
                            v___x_3687_ = v___x_3684_;
                            v_isShared_3688_ = v_isSharedCheck_3694_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_3685_);
                            leanh::lean_dec(v___x_3684_);
                            v___x_3687_ = leanh::lean_box(0);
                            v_isShared_3688_ = v_isSharedCheck_3694_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3689_ = lean_string_append(v_fst_3681_, v_val_3685_);
                leanh::lean_dec(v_val_3685_);
                v___x_3690_ = lean_string_append(v___x_3689_, v_snd_3683_);
                leanh::lean_dec(v_snd_3683_);
                if v_isShared_3688_ == 0 {
                    leanh::lean_ctor_set(v___x_3687_, 0, v___x_3690_);
                    v___x_3692_ = v___x_3687_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3693_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3693_, 0, v___x_3690_);
                    v___x_3692_ = v_reuseFailAlloc_3693_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3692_;
            }
            _ => {}
        }
    }
}
pub unsafe fn lean_demangle_bt_line_cstr(
    mut v_line_3695_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3696_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3696_ = l_Lean_Name_Demangle_demangleBtLine(v_line_3695_);
    if leanh::lean_obj_tag(v___x_3696_) == 0 {
        let mut v___x_3697_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3697_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts___closed__0;
        return v___x_3697_;
    } else {
        let mut v_val_3698_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_3698_ = leanh::lean_ctor_get(v___x_3696_, 0);
        leanh::lean_inc(v_val_3698_);
        leanh::lean_dec_ref_known(v___x_3696_, 1);
        return v_val_3698_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_NameDemangling(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_While(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Search(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Iterate(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_NameTrie(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_NameMangling(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_NameDemangling(
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
pub unsafe fn initialize_Lean_Compiler_NameDemangling(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_While(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_TakeDrop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Search(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Iterate(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Data_NameTrie(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_NameMangling(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_NameDemangling(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_NameDemangling(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_NameDemangling(builtin);
}