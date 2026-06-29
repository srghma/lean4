// Lean compiler output
// Module: Lake.DSL.Key
// Imports: Lake.Build.Key Lake.DSL.Syntax Lake.Util.Name
use crate::r#gen::Init::Meta::Defs::{l_Lean_Syntax_isNone, l_Lean_TSyntax_getId};
use crate::r#gen::Init::Prelude::{
    l_Lean_Macro_throwError___redArg, l_Lean_Macro_throwUnsupported___redArg,
    l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs, l_Lean_Syntax_getId,
    l_Lean_Syntax_getOptional_x3f, l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesNull,
    l_Lean_Syntax_node1, l_Lean_Syntax_node2, l_Lean_addMacroScope, l_Lean_replaceRef,
    l_String_toRawSubstring_x27,
};
use crate::r#gen::Lake::Build::Key::{
    initialize_Lake_Build_Key, runtime_initialize_Lake_Build_Key,
};
use crate::r#gen::Lake::DSL::Syntax::{
    initialize_Lake_DSL_Syntax, runtime_initialize_Lake_DSL_Syntax,
};
use crate::r#gen::Lake::Util::Name::{
    initialize_Lake_Util_Name, l_Lake_Name_quoteFrom, runtime_initialize_Lake_Util_Name,
};
use crate::r#gen::Lean::Elab::Util::l_Lean_Elab_macroAttribute;
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_nat_dec_le, lean_nat_dec_lt, lean_usize_dec_eq,
};
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__2_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__3_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__3_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__4_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__3_value) as *mut crate::leanh::LeanObject,12966880221525079621 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__5_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [66, 117, 105, 108, 100, 75, 101, 121, 46, 102, 97, 99, 101, 116, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__5_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__7_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [66, 117, 105, 108, 100, 75, 101, 121, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__8_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [102, 97, 99, 101, 116, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__8_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__9_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__7_value) as *mut crate::leanh::LeanObject,661846266477681541 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__9_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__9_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__8_value) as *mut crate::leanh::LeanObject,16926147430352571313 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__10_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 97, 107, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__10_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__11_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__10_value) as *mut crate::leanh::LeanObject,13012506173997729135 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__11_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__11_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__7_value) as *mut crate::leanh::LeanObject,12711648237237404489 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__11_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__11_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__8_value) as *mut crate::leanh::LeanObject,17900683711374498677 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__12_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__11_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__13_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__11_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__14_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__13_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__15_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__12_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__14_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__16_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__16_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__17_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__16_value) as *mut crate::leanh::LeanObject,9855511589286918680 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__17_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__0_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        66, 117, 105, 108, 100, 75, 101, 121, 46, 112, 97, 99, 107, 97, 103, 101, 84, 97, 114, 103,
        101, 116, 0,
    ],
};
static mut l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__2_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        112, 97, 99, 107, 97, 103, 101, 84, 97, 114, 103, 101, 116, 0,
    ],
};
static mut l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__2_value
) as *mut crate::leanh::LeanObject;
static l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__7_value) as *mut crate::leanh::LeanObject,661846266477681541 as *mut crate::leanh::LeanObject] };
pub static l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__3_value:
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
            l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__3_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        7900444931174272106 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__3_value
) as *mut crate::leanh::LeanObject;
static l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__10_value) as *mut crate::leanh::LeanObject,13012506173997729135 as *mut crate::leanh::LeanObject] };
static l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__7_value) as *mut crate::leanh::LeanObject,12711648237237404489 as *mut crate::leanh::LeanObject] };
pub static l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__4_value:
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
            l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__4_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        9160959534390598822 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__5_value:
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
        core::ptr::addr_of!(
            l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__4_value
        ) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__6_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__4_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__6_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__7_value:
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
        core::ptr::addr_of!(
            l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__6_value
        ) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__7_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__8_value:
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
        core::ptr::addr_of!(
            l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__5_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__7_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__8_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__9_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        66, 117, 105, 108, 100, 75, 101, 121, 46, 112, 97, 99, 107, 97, 103, 101, 77, 111, 100,
        117, 108, 101, 0,
    ],
};
static mut l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__9_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__10_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__11_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        112, 97, 99, 107, 97, 103, 101, 77, 111, 100, 117, 108, 101, 0,
    ],
};
static mut l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__11_value
) as *mut crate::leanh::LeanObject;
static l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__12_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__7_value) as *mut crate::leanh::LeanObject,661846266477681541 as *mut crate::leanh::LeanObject] };
pub static l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__12_value:
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
            l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__12_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__11_value
        ) as *mut crate::leanh::LeanObject,
        5744928602254182130 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__12_value
) as *mut crate::leanh::LeanObject;
static l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__13_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__10_value) as *mut crate::leanh::LeanObject,13012506173997729135 as *mut crate::leanh::LeanObject] };
static l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__13_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__13_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__7_value) as *mut crate::leanh::LeanObject,12711648237237404489 as *mut crate::leanh::LeanObject] };
pub static l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__13_value:
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
            l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__13_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__11_value
        ) as *mut crate::leanh::LeanObject,
        12153807471519003486 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__13_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__14_value:
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
        core::ptr::addr_of!(
            l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__13_value
        ) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__14:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__14_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__15_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__13_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__15_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__16_value:
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
        core::ptr::addr_of!(
            l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__15_value
        ) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__16:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__16_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__17_value:
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
        core::ptr::addr_of!(
            l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__14_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__16_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__17:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__17_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__18_value:
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
    m_data: [68, 83, 76, 0],
};
static mut l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__18:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__18_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__19_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 17,
    m_capacity: 17,
    m_length: 16,
    m_data: [
        112, 97, 99, 107, 97, 103, 101, 84, 97, 114, 103, 101, 116, 76, 105, 116, 0,
    ],
};
static mut l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__19:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__19_value
) as *mut crate::leanh::LeanObject;
static l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__20_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__10_value) as *mut crate::leanh::LeanObject,13012506173997729135 as *mut crate::leanh::LeanObject] };
static l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__20_value_aux_1:
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
            l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__20_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__18_value
        ) as *mut crate::leanh::LeanObject,
        5901868804703194544 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__20_value:
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
            l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__20_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__19_value
        ) as *mut crate::leanh::LeanObject,
        6142289428472292793 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__20:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__20_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__21_value:
    crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 34,
    m_capacity: 34,
    m_length: 33,
    m_data: [
        105, 108, 108, 45, 102, 111, 114, 109, 101, 100, 32, 112, 97, 99, 107, 97, 103, 101, 32,
        116, 97, 114, 103, 101, 116, 32, 108, 105, 116, 101, 114, 97, 108, 0,
    ],
};
static mut l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__21:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__21_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit_spec__0___closed__0_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [102, 97, 99, 101, 116, 83, 117, 102, 102, 105, 120, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit_spec__0___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__10_value) as *mut crate::leanh::LeanObject,13012506173997729135 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit_spec__0___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit_spec__0___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__18_value) as *mut crate::leanh::LeanObject,5901868804703194544 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit_spec__0___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit_spec__0___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,7856869693164098343 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit_spec__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__0_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 19,
    m_capacity: 19,
    m_length: 18,
    m_data: [
        109, 111, 100, 117, 108, 101, 84, 97, 114, 103, 101, 116, 75, 101, 121, 76, 105, 116, 0,
    ],
};
static mut l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__0_value
) as *mut crate::leanh::LeanObject;
static l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__10_value) as *mut crate::leanh::LeanObject,13012506173997729135 as *mut crate::leanh::LeanObject] };
static l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__1_value_aux_1:
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
            l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__1_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__18_value
        ) as *mut crate::leanh::LeanObject,
        5901868804703194544 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__1_value:
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
            l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__1_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        4666197752279438947 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__2_value:
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
        66, 117, 105, 108, 100, 75, 101, 121, 46, 109, 111, 100, 117, 108, 101, 0,
    ],
};
static mut l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__2_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__4_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [109, 111, 100, 117, 108, 101, 0],
};
static mut l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__4_value
) as *mut crate::leanh::LeanObject;
static l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__7_value) as *mut crate::leanh::LeanObject,661846266477681541 as *mut crate::leanh::LeanObject] };
pub static l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__5_value:
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
            l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__5_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__4_value
        ) as *mut crate::leanh::LeanObject,
        99763445462658121 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__5_value
) as *mut crate::leanh::LeanObject;
static l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__10_value) as *mut crate::leanh::LeanObject,13012506173997729135 as *mut crate::leanh::LeanObject] };
static l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__6_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__6_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__7_value) as *mut crate::leanh::LeanObject,12711648237237404489 as *mut crate::leanh::LeanObject] };
pub static l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__6_value:
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
            l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__6_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__4_value
        ) as *mut crate::leanh::LeanObject,
        2592653373651761885 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__6_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__7_value:
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
        core::ptr::addr_of!(
            l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__6_value
        ) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__7_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__8_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__6_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__8_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__9_value:
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
        core::ptr::addr_of!(
            l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__8_value
        ) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__9_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__10_value:
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
        core::ptr::addr_of!(
            l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__7_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__9_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__10_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__11_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 19,
    m_capacity: 19,
    m_length: 18,
    m_data: [
        80, 97, 114, 116, 105, 97, 108, 66, 117, 105, 108, 100, 75, 101, 121, 46, 109, 107, 0,
    ],
};
static mut l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__11_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__12_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__13_value:
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
        80, 97, 114, 116, 105, 97, 108, 66, 117, 105, 108, 100, 75, 101, 121, 0,
    ],
};
static mut l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__13_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__14_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [109, 107, 0],
};
static mut l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__14:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__14_value
) as *mut crate::leanh::LeanObject;
static l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__15_value_aux_0:
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
        core::ptr::addr_of!(
            l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__13_value
        ) as *mut crate::leanh::LeanObject,
        4972482464510784692 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__15_value:
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
            l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__15_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__14_value
        ) as *mut crate::leanh::LeanObject,
        11671259761654687516 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__15_value
) as *mut crate::leanh::LeanObject;
static l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__16_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__10_value) as *mut crate::leanh::LeanObject,13012506173997729135 as *mut crate::leanh::LeanObject] };
static l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__16_value_aux_1:
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
            l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__16_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__13_value
        ) as *mut crate::leanh::LeanObject,
        6151512426196465392 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__16_value:
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
            l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__16_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__14_value
        ) as *mut crate::leanh::LeanObject,
        3542652886112287752 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__16:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__16_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__17_value:
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
        core::ptr::addr_of!(
            l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__16_value
        ) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__17:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__17_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__18_value:
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
        core::ptr::addr_of!(
            l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__17_value
        ) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__18:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__18_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__0_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__0_value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__1_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__10_value) as *mut crate::leanh::LeanObject,12997130533650095963 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__18_value) as *mut crate::leanh::LeanObject,11286550318989764116 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__4_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [75, 101, 121, 0]};
static mut l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__3_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__4_value) as *mut crate::leanh::LeanObject,2083957185687871411 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__5_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,15811393401256516126 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__7_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__6_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__10_value) as *mut crate::leanh::LeanObject,13238148510488060174 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__7_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__18_value) as *mut crate::leanh::LeanObject,10343394633205535589 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__9_value: crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [101, 120, 112, 97, 110, 100, 77, 111, 100, 117, 108, 101, 84, 97, 114, 103, 101, 116, 75, 101, 121, 76, 105, 116, 0]};
static mut l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__10_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__8_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__9_value) as *mut crate::leanh::LeanObject,17738257744241279649 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__0_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        112, 97, 99, 107, 97, 103, 101, 84, 97, 114, 103, 101, 116, 75, 101, 121, 76, 105, 116, 0,
    ],
};
static mut l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__0_value
) as *mut crate::leanh::LeanObject;
static l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__10_value) as *mut crate::leanh::LeanObject,13012506173997729135 as *mut crate::leanh::LeanObject] };
static l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__1_value_aux_1:
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
            l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__1_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__18_value
        ) as *mut crate::leanh::LeanObject,
        5901868804703194544 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__1_value:
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
            l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__1_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        17001465581052579529 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__2_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 17,
    m_capacity: 17,
    m_length: 16,
    m_data: [
        66, 117, 105, 108, 100, 75, 101, 121, 46, 112, 97, 99, 107, 97, 103, 101, 0,
    ],
};
static mut l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__2_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__4_value:
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
    m_data: [112, 97, 99, 107, 97, 103, 101, 0],
};
static mut l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__4_value
) as *mut crate::leanh::LeanObject;
static l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__7_value) as *mut crate::leanh::LeanObject,661846266477681541 as *mut crate::leanh::LeanObject] };
pub static l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__5_value:
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
            l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__5_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__4_value
        ) as *mut crate::leanh::LeanObject,
        9559191325857101169 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__5_value
) as *mut crate::leanh::LeanObject;
static l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__10_value) as *mut crate::leanh::LeanObject,13012506173997729135 as *mut crate::leanh::LeanObject] };
static l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__6_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__6_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__7_value) as *mut crate::leanh::LeanObject,12711648237237404489 as *mut crate::leanh::LeanObject] };
pub static l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__6_value:
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
            l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__6_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__4_value
        ) as *mut crate::leanh::LeanObject,
        14226970315624165301 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__6_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__7_value:
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
        core::ptr::addr_of!(
            l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__6_value
        ) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__7_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__8_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__6_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__8_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__9_value:
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
        core::ptr::addr_of!(
            l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__8_value
        ) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__9_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__10_value:
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
        core::ptr::addr_of!(
            l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__7_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__9_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__10_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit__1___closed__0_value: crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [101, 120, 112, 97, 110, 100, 80, 97, 99, 107, 97, 103, 101, 84, 97, 114, 103, 101, 116, 75, 101, 121, 76, 105, 116, 0]};
static mut l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__8_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit__1___closed__0_value) as *mut crate::leanh::LeanObject,9290527682391885814 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_576_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__5;
    v___x_577_ = l_String_toRawSubstring_x27(v___x_576_);
    return v___x_577_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1(
    mut v_as_602_: *mut crate::leanh::LeanObject,
    mut v_i_603_: usize,
    mut v_stop_604_: usize,
    mut v_b_605_: *mut crate::leanh::LeanObject,
    mut v___y_606_: *mut crate::leanh::LeanObject,
    mut v___y_607_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_608_: u8 = 0;
    let mut v_quotContext_609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_623_: usize = 0;
    let mut v___x_624_: usize = 0;
    let mut v___x_626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_608_ = lean_usize_dec_eq(v_i_603_, v_stop_604_);
                if v___x_608_ == 0 {
                    v_quotContext_609_ = crate::leanh::lean_ctor_get(v___y_606_, 1);
                    v_currMacroScope_610_ = crate::leanh::lean_ctor_get(v___y_606_, 2);
                    v_ref_611_ = crate::leanh::lean_ctor_get(v___y_606_, 5);
                    v___x_612_ = lean_array_uget_borrowed(v_as_602_, v_i_603_);
                    v___x_613_ = l_Lean_SourceInfo_fromRef(v_ref_611_, v___x_608_);
                    v___x_614_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__4;
                    v___x_615_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__6), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__6_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__6);
                    v___x_616_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__9;
                    crate::leanh::lean_inc(v_currMacroScope_610_);
                    crate::leanh::lean_inc(v_quotContext_609_);
                    v___x_617_ =
                        l_Lean_addMacroScope(v_quotContext_609_, v___x_616_, v_currMacroScope_610_);
                    v___x_618_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__15;
                    crate::leanh::lean_inc_n(v___x_613_, 2);
                    v___x_619_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_619_, 0, v___x_613_);
                    crate::leanh::lean_ctor_set(v___x_619_, 1, v___x_615_);
                    crate::leanh::lean_ctor_set(v___x_619_, 2, v___x_617_);
                    crate::leanh::lean_ctor_set(v___x_619_, 3, v___x_618_);
                    v___x_620_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__17;
                    crate::leanh::lean_inc(v___x_612_);
                    v___x_621_ = l_Lean_Syntax_node2(v___x_613_, v___x_620_, v_b_605_, v___x_612_);
                    v___x_622_ =
                        l_Lean_Syntax_node2(v___x_613_, v___x_614_, v___x_619_, v___x_621_);
                    v___x_623_ = 1usize;
                    v___x_624_ = lean_usize_add(v_i_603_, v___x_623_);
                    v_i_603_ = v___x_624_;
                    v_b_605_ = v___x_622_;
                    state = 0;
                    continue;
                } else {
                    v___x_626_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_626_, 0, v_b_605_);
                    crate::leanh::lean_ctor_set(v___x_626_, 1, v___y_607_);
                    return v___x_626_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___boxed(
    mut v_as_627_: *mut crate::leanh::LeanObject,
    mut v_i_628_: *mut crate::leanh::LeanObject,
    mut v_stop_629_: *mut crate::leanh::LeanObject,
    mut v_b_630_: *mut crate::leanh::LeanObject,
    mut v___y_631_: *mut crate::leanh::LeanObject,
    mut v___y_632_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_633_: usize = 0;
    let mut v_stop_boxed_634_: usize = 0;
    let mut v_res_635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_633_ = crate::leanh::lean_unbox_usize(v_i_628_);
    crate::leanh::lean_dec(v_i_628_);
    v_stop_boxed_634_ = crate::leanh::lean_unbox_usize(v_stop_629_);
    crate::leanh::lean_dec(v_stop_629_);
    v_res_635_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1(v_as_627_, v_i_boxed_633_, v_stop_boxed_634_, v_b_630_, v___y_631_, v___y_632_);
    crate::leanh::lean_dec_ref(v___y_631_);
    crate::leanh::lean_dec_ref(v_as_627_);
    return v_res_635_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__0(
    mut v_sz_636_: usize,
    mut v_i_637_: usize,
    mut v_bs_638_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_639_: u8 = 0;
    let mut v_v_640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_644_: u8 = 0;
    let mut v___x_645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_646_: usize = 0;
    let mut v___x_647_: usize = 0;
    let mut v___x_648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_639_ = lean_usize_dec_lt(v_i_637_, v_sz_636_);
                if v___x_639_ == 0 {
                    return v_bs_638_;
                } else {
                    v_v_640_ = lean_array_uget(v_bs_638_, v_i_637_);
                    v___x_641_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_642_ = lean_array_uset(v_bs_638_, v_i_637_, v___x_641_);
                    v___x_643_ = l_Lean_Syntax_getId(v_v_640_);
                    v___x_644_ = 0;
                    v___x_645_ = l_Lake_Name_quoteFrom(v_v_640_, v___x_643_, v___x_644_);
                    v___x_646_ = 1usize;
                    v___x_647_ = lean_usize_add(v_i_637_, v___x_646_);
                    v___x_648_ = lean_array_uset(v_bs_x27_642_, v_i_637_, v___x_645_);
                    v_i_637_ = v___x_647_;
                    v_bs_638_ = v___x_648_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__0___boxed(
    mut v_sz_650_: *mut crate::leanh::LeanObject,
    mut v_i_651_: *mut crate::leanh::LeanObject,
    mut v_bs_652_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_653_: usize = 0;
    let mut v_i_boxed_654_: usize = 0;
    let mut v_res_655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_653_ = crate::leanh::lean_unbox_usize(v_sz_650_);
    crate::leanh::lean_dec(v_sz_650_);
    v_i_boxed_654_ = crate::leanh::lean_unbox_usize(v_i_651_);
    crate::leanh::lean_dec(v_i_651_);
    v_res_655_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__0(v_sz_boxed_653_, v_i_boxed_654_, v_bs_652_);
    return v_res_655_;
}
pub unsafe fn l___private_Lake_DSL_Key_0__Lake_DSL_expandFacets(
    mut v_tgt_656_: *mut crate::leanh::LeanObject,
    mut v_facets_657_: *mut crate::leanh::LeanObject,
    mut v_a_658_: *mut crate::leanh::LeanObject,
    mut v_a_659_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_660_: usize = 0;
    let mut v___x_661_: usize = 0;
    let mut v_facetLits_662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_665_: u8 = 0;
    v_sz_660_ = lean_array_size(v_facets_657_);
    v___x_661_ = 0usize;
    v_facetLits_662_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__0(v_sz_660_, v___x_661_, v_facets_657_);
    v___x_663_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_664_ = lean_array_get_size(v_facetLits_662_);
    v___x_665_ = lean_nat_dec_lt(v___x_663_, v___x_664_);
    if v___x_665_ == 0 {
        let mut v___x_666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_facetLits_662_);
        v___x_666_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_666_, 0, v_tgt_656_);
        crate::leanh::lean_ctor_set(v___x_666_, 1, v_a_659_);
        return v___x_666_;
    } else {
        let mut v___x_667_: u8 = 0;
        v___x_667_ = lean_nat_dec_le(v___x_664_, v___x_664_);
        if v___x_667_ == 0 {
            if v___x_665_ == 0 {
                let mut v___x_668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v_facetLits_662_);
                v___x_668_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_668_, 0, v_tgt_656_);
                crate::leanh::lean_ctor_set(v___x_668_, 1, v_a_659_);
                return v___x_668_;
            } else {
                let mut v___x_669_: usize = 0;
                let mut v___x_670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_669_ = lean_usize_of_nat(v___x_664_);
                v___x_670_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1(v_facetLits_662_, v___x_661_, v___x_669_, v_tgt_656_, v_a_658_, v_a_659_);
                crate::leanh::lean_dec_ref(v_facetLits_662_);
                return v___x_670_;
            }
        } else {
            let mut v___x_671_: usize = 0;
            let mut v___x_672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_671_ = lean_usize_of_nat(v___x_664_);
            v___x_672_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1(v_facetLits_662_, v___x_661_, v___x_671_, v_tgt_656_, v_a_658_, v_a_659_);
            crate::leanh::lean_dec_ref(v_facetLits_662_);
            return v___x_672_;
        }
    }
}
pub unsafe fn l___private_Lake_DSL_Key_0__Lake_DSL_expandFacets___boxed(
    mut v_tgt_673_: *mut crate::leanh::LeanObject,
    mut v_facets_674_: *mut crate::leanh::LeanObject,
    mut v_a_675_: *mut crate::leanh::LeanObject,
    mut v_a_676_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_677_ = l___private_Lake_DSL_Key_0__Lake_DSL_expandFacets(
        v_tgt_673_,
        v_facets_674_,
        v_a_675_,
        v_a_676_,
    );
    crate::leanh::lean_dec_ref(v_a_675_);
    return v_res_677_;
}
pub unsafe fn _init_l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_679_ = l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__0;
    v___x_680_ = l_String_toRawSubstring_x27(v___x_679_);
    return v___x_680_;
}
pub unsafe fn _init_l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_701_ = l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__9;
    v___x_702_ = l_String_toRawSubstring_x27(v___x_701_);
    return v___x_702_;
}
pub unsafe fn l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit(
    mut v_pkg_729_: *mut crate::leanh::LeanObject,
    mut v_stx_730_: *mut crate::leanh::LeanObject,
    mut v_a_731_: *mut crate::leanh::LeanObject,
    mut v_a_732_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_methods_733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_x3f_740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tgt_744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_746_: u8 = 0;
    let mut v_tgtLit_747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_777_: u8 = 0;
    let mut v_ref_778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_784_: u8 = 0;
    let mut v___x_785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_786_: u8 = 0;
    let mut v___x_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_x3f_789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_methods_733_ = crate::leanh::lean_ctor_get(v_a_731_, 0);
                v_quotContext_734_ = crate::leanh::lean_ctor_get(v_a_731_, 1);
                v_currMacroScope_735_ = crate::leanh::lean_ctor_get(v_a_731_, 2);
                v_currRecDepth_736_ = crate::leanh::lean_ctor_get(v_a_731_, 3);
                v_maxRecDepth_737_ = crate::leanh::lean_ctor_get(v_a_731_, 4);
                v_ref_738_ = crate::leanh::lean_ctor_get(v_a_731_, 5);
                v___x_776_ =
                    l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__20;
                crate::leanh::lean_inc(v_stx_730_);
                v___x_777_ = l_Lean_Syntax_isOfKind(v_stx_730_, v___x_776_);
                v_ref_778_ = l_Lean_replaceRef(v_stx_730_, v_ref_738_);
                crate::leanh::lean_inc(v_maxRecDepth_737_);
                crate::leanh::lean_inc(v_currRecDepth_736_);
                crate::leanh::lean_inc(v_currMacroScope_735_);
                crate::leanh::lean_inc(v_quotContext_734_);
                crate::leanh::lean_inc(v_methods_733_);
                v___x_779_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_779_, 0, v_methods_733_);
                crate::leanh::lean_ctor_set(v___x_779_, 1, v_quotContext_734_);
                crate::leanh::lean_ctor_set(v___x_779_, 2, v_currMacroScope_735_);
                crate::leanh::lean_ctor_set(v___x_779_, 3, v_currRecDepth_736_);
                crate::leanh::lean_ctor_set(v___x_779_, 4, v_maxRecDepth_737_);
                crate::leanh::lean_ctor_set(v___x_779_, 5, v_ref_778_);
                if v___x_777_ == 0 {
                    crate::leanh::lean_dec(v_stx_730_);
                    crate::leanh::lean_dec(v_pkg_729_);
                    v___x_780_ =
                        l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__21;
                    v___x_781_ = l_Lean_Macro_throwError___redArg(v___x_780_, v___x_779_, v_a_732_);
                    crate::leanh::lean_dec_ref_known(v___x_779_, 6);
                    return v___x_781_;
                } else {
                    v___x_782_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_783_ = l_Lean_Syntax_getArg(v_stx_730_, v___x_782_);
                    v___x_784_ = l_Lean_Syntax_isNone(v___x_783_);
                    if v___x_784_ == 0 {
                        v___x_785_ = crate::leanh::lean_unsigned_to_nat(1);
                        crate::leanh::lean_inc(v___x_783_);
                        v___x_786_ = l_Lean_Syntax_matchesNull(v___x_783_, v___x_785_);
                        if v___x_786_ == 0 {
                            crate::leanh::lean_dec(v___x_783_);
                            crate::leanh::lean_dec(v_stx_730_);
                            crate::leanh::lean_dec(v_pkg_729_);
                            v___x_787_ = l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__21;
                            v___x_788_ =
                                l_Lean_Macro_throwError___redArg(v___x_787_, v___x_779_, v_a_732_);
                            crate::leanh::lean_dec_ref_known(v___x_779_, 6);
                            return v___x_788_;
                        } else {
                            v_mod_x3f_789_ = l_Lean_Syntax_getArg(v___x_783_, v___x_782_);
                            crate::leanh::lean_dec(v___x_783_);
                            v___x_790_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_790_, 0, v_mod_x3f_789_);
                            v_mod_x3f_740_ = v___x_790_;
                            v___y_741_ = v___x_779_;
                            v___y_742_ = v_a_732_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_783_);
                        v___x_791_ = crate::leanh::lean_box(0);
                        v_mod_x3f_740_ = v___x_791_;
                        v___y_741_ = v___x_779_;
                        v___y_742_ = v_a_732_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_743_ = crate::leanh::lean_unsigned_to_nat(1);
                v_tgt_744_ = l_Lean_Syntax_getArg(v_stx_730_, v___x_743_);
                crate::leanh::lean_dec(v_stx_730_);
                v___x_745_ = l_Lean_TSyntax_getId(v_tgt_744_);
                v___x_746_ = 0;
                v_tgtLit_747_ = l_Lake_Name_quoteFrom(v_tgt_744_, v___x_745_, v___x_746_);
                if crate::leanh::lean_obj_tag(v_mod_x3f_740_) == 0 {
                    v_quotContext_748_ = crate::leanh::lean_ctor_get(v___y_741_, 1);
                    crate::leanh::lean_inc(v_quotContext_748_);
                    v_currMacroScope_749_ = crate::leanh::lean_ctor_get(v___y_741_, 2);
                    crate::leanh::lean_inc(v_currMacroScope_749_);
                    v_ref_750_ = crate::leanh::lean_ctor_get(v___y_741_, 5);
                    crate::leanh::lean_inc(v_ref_750_);
                    crate::leanh::lean_dec_ref(v___y_741_);
                    v___x_751_ = l_Lean_SourceInfo_fromRef(v_ref_750_, v___x_746_);
                    crate::leanh::lean_dec(v_ref_750_);
                    v___x_752_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__4;
                    v___x_753_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__1), core::ptr::addr_of_mut!(l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__1_once), _init_l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__1);
                    v___x_754_ =
                        l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__3;
                    v___x_755_ =
                        l_Lean_addMacroScope(v_quotContext_748_, v___x_754_, v_currMacroScope_749_);
                    v___x_756_ =
                        l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__8;
                    crate::leanh::lean_inc_n(v___x_751_, 2);
                    v___x_757_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_757_, 0, v___x_751_);
                    crate::leanh::lean_ctor_set(v___x_757_, 1, v___x_753_);
                    crate::leanh::lean_ctor_set(v___x_757_, 2, v___x_755_);
                    crate::leanh::lean_ctor_set(v___x_757_, 3, v___x_756_);
                    v___x_758_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__17;
                    v___x_759_ =
                        l_Lean_Syntax_node2(v___x_751_, v___x_758_, v_pkg_729_, v_tgtLit_747_);
                    v___x_760_ =
                        l_Lean_Syntax_node2(v___x_751_, v___x_752_, v___x_757_, v___x_759_);
                    v___x_761_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_761_, 0, v___x_760_);
                    crate::leanh::lean_ctor_set(v___x_761_, 1, v___y_742_);
                    return v___x_761_;
                } else {
                    crate::leanh::lean_dec_ref_known(v_mod_x3f_740_, 1);
                    v_quotContext_762_ = crate::leanh::lean_ctor_get(v___y_741_, 1);
                    crate::leanh::lean_inc(v_quotContext_762_);
                    v_currMacroScope_763_ = crate::leanh::lean_ctor_get(v___y_741_, 2);
                    crate::leanh::lean_inc(v_currMacroScope_763_);
                    v_ref_764_ = crate::leanh::lean_ctor_get(v___y_741_, 5);
                    crate::leanh::lean_inc(v_ref_764_);
                    crate::leanh::lean_dec_ref(v___y_741_);
                    v___x_765_ = l_Lean_SourceInfo_fromRef(v_ref_764_, v___x_746_);
                    crate::leanh::lean_dec(v_ref_764_);
                    v___x_766_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__4;
                    v___x_767_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__10), core::ptr::addr_of_mut!(l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__10_once), _init_l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__10);
                    v___x_768_ =
                        l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__12;
                    v___x_769_ =
                        l_Lean_addMacroScope(v_quotContext_762_, v___x_768_, v_currMacroScope_763_);
                    v___x_770_ =
                        l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__17;
                    crate::leanh::lean_inc_n(v___x_765_, 2);
                    v___x_771_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_771_, 0, v___x_765_);
                    crate::leanh::lean_ctor_set(v___x_771_, 1, v___x_767_);
                    crate::leanh::lean_ctor_set(v___x_771_, 2, v___x_769_);
                    crate::leanh::lean_ctor_set(v___x_771_, 3, v___x_770_);
                    v___x_772_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__17;
                    v___x_773_ =
                        l_Lean_Syntax_node2(v___x_765_, v___x_772_, v_pkg_729_, v_tgtLit_747_);
                    v___x_774_ =
                        l_Lean_Syntax_node2(v___x_765_, v___x_766_, v___x_771_, v___x_773_);
                    v___x_775_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_775_, 0, v___x_774_);
                    crate::leanh::lean_ctor_set(v___x_775_, 1, v___y_742_);
                    return v___x_775_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___boxed(
    mut v_pkg_792_: *mut crate::leanh::LeanObject,
    mut v_stx_793_: *mut crate::leanh::LeanObject,
    mut v_a_794_: *mut crate::leanh::LeanObject,
    mut v_a_795_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_796_ = l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit(
        v_pkg_792_, v_stx_793_, v_a_794_, v_a_795_,
    );
    crate::leanh::lean_dec_ref(v_a_794_);
    return v_res_796_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit_spec__0(
    mut v_sz_802_: usize,
    mut v_i_803_: usize,
    mut v_bs_804_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_805_: u8 = 0;
    let mut v___x_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_809_: u8 = 0;
    let mut v___x_810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_facets_814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_815_: usize = 0;
    let mut v___x_816_: usize = 0;
    let mut v___x_817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_805_ = lean_usize_dec_lt(v_i_803_, v_sz_802_);
                if v___x_805_ == 0 {
                    v___x_806_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_806_, 0, v_bs_804_);
                    return v___x_806_;
                } else {
                    v_v_807_ = lean_array_uget(v_bs_804_, v_i_803_);
                    v___x_808_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit_spec__0___closed__1;
                    crate::leanh::lean_inc(v_v_807_);
                    v___x_809_ = l_Lean_Syntax_isOfKind(v_v_807_, v___x_808_);
                    if v___x_809_ == 0 {
                        crate::leanh::lean_dec(v_v_807_);
                        crate::leanh::lean_dec_ref(v_bs_804_);
                        v___x_810_ = crate::leanh::lean_box(0);
                        return v___x_810_;
                    } else {
                        v___x_811_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_812_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_813_ = lean_array_uset(v_bs_804_, v_i_803_, v___x_812_);
                        v_facets_814_ = l_Lean_Syntax_getArg(v_v_807_, v___x_811_);
                        crate::leanh::lean_dec(v_v_807_);
                        v___x_815_ = 1usize;
                        v___x_816_ = lean_usize_add(v_i_803_, v___x_815_);
                        v___x_817_ = lean_array_uset(v_bs_x27_813_, v_i_803_, v_facets_814_);
                        v_i_803_ = v___x_816_;
                        v_bs_804_ = v___x_817_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit_spec__0___boxed(
    mut v_sz_819_: *mut crate::leanh::LeanObject,
    mut v_i_820_: *mut crate::leanh::LeanObject,
    mut v_bs_821_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_822_: usize = 0;
    let mut v_i_boxed_823_: usize = 0;
    let mut v_res_824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_822_ = crate::leanh::lean_unbox_usize(v_sz_819_);
    crate::leanh::lean_dec(v_sz_819_);
    v_i_boxed_823_ = crate::leanh::lean_unbox_usize(v_i_820_);
    crate::leanh::lean_dec(v_i_820_);
    v_res_824_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit_spec__0(v_sz_boxed_822_, v_i_boxed_823_, v_bs_821_);
    return v_res_824_;
}
pub unsafe fn _init_l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_831_ = l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__2;
    v___x_832_ = l_String_toRawSubstring_x27(v___x_831_);
    return v___x_832_;
}
pub unsafe fn _init_l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_853_ = l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__11;
    v___x_854_ = l_String_toRawSubstring_x27(v___x_853_);
    return v___x_854_;
}
pub unsafe fn l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit(
    mut v_stx_870_: *mut crate::leanh::LeanObject,
    mut v_a_871_: *mut crate::leanh::LeanObject,
    mut v_a_872_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_874_: u8 = 0;
    let mut v___x_875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_879_: usize = 0;
    let mut v___x_880_: usize = 0;
    let mut v___x_881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_methods_884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_895_: u8 = 0;
    let mut v_modLit_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v_a_910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_914_: u8 = 0;
    let mut v___x_915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_925_: u8 = 0;
    let mut v_a_926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_930_: u8 = 0;
    let mut v___x_932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_934_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_873_ =
                    l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__1;
                crate::leanh::lean_inc(v_stx_870_);
                v___x_874_ = l_Lean_Syntax_isOfKind(v_stx_870_, v___x_873_);
                if v___x_874_ == 0 {
                    crate::leanh::lean_dec(v_stx_870_);
                    v___x_875_ = l_Lean_Macro_throwUnsupported___redArg(v_a_872_);
                    return v___x_875_;
                } else {
                    v___x_876_ = crate::leanh::lean_unsigned_to_nat(2);
                    v___x_877_ = l_Lean_Syntax_getArg(v_stx_870_, v___x_876_);
                    v___x_878_ = l_Lean_Syntax_getArgs(v___x_877_);
                    crate::leanh::lean_dec(v___x_877_);
                    v_sz_879_ = lean_array_size(v___x_878_);
                    v___x_880_ = 0usize;
                    v___x_881_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit_spec__0(v_sz_879_, v___x_880_, v___x_878_);
                    if crate::leanh::lean_obj_tag(v___x_881_) == 0 {
                        crate::leanh::lean_dec(v_stx_870_);
                        v___x_882_ = l_Lean_Macro_throwUnsupported___redArg(v_a_872_);
                        return v___x_882_;
                    } else {
                        v_val_883_ = crate::leanh::lean_ctor_get(v___x_881_, 0);
                        crate::leanh::lean_inc(v_val_883_);
                        crate::leanh::lean_dec_ref_known(v___x_881_, 1);
                        v_methods_884_ = crate::leanh::lean_ctor_get(v_a_871_, 0);
                        v_quotContext_885_ = crate::leanh::lean_ctor_get(v_a_871_, 1);
                        v_currMacroScope_886_ = crate::leanh::lean_ctor_get(v_a_871_, 2);
                        v_currRecDepth_887_ = crate::leanh::lean_ctor_get(v_a_871_, 3);
                        v_maxRecDepth_888_ = crate::leanh::lean_ctor_get(v_a_871_, 4);
                        v_ref_889_ = crate::leanh::lean_ctor_get(v_a_871_, 5);
                        v___x_890_ = crate::leanh::lean_unsigned_to_nat(1);
                        v_mod_891_ = l_Lean_Syntax_getArg(v_stx_870_, v___x_890_);
                        v___x_892_ = l_Lean_TSyntax_getId(v_mod_891_);
                        v___x_893_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_tk_894_ = l_Lean_Syntax_getArg(v_stx_870_, v___x_893_);
                        crate::leanh::lean_dec(v_stx_870_);
                        v___x_895_ = 0;
                        v_modLit_896_ = l_Lake_Name_quoteFrom(v_mod_891_, v___x_892_, v___x_895_);
                        v_ref_897_ = l_Lean_replaceRef(v_tk_894_, v_ref_889_);
                        crate::leanh::lean_dec(v_tk_894_);
                        crate::leanh::lean_inc(v_ref_897_);
                        crate::leanh::lean_inc(v_maxRecDepth_888_);
                        crate::leanh::lean_inc(v_currRecDepth_887_);
                        crate::leanh::lean_inc_n(v_currMacroScope_886_, 2);
                        crate::leanh::lean_inc_n(v_quotContext_885_, 2);
                        crate::leanh::lean_inc(v_methods_884_);
                        v___x_898_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_898_, 0, v_methods_884_);
                        crate::leanh::lean_ctor_set(v___x_898_, 1, v_quotContext_885_);
                        crate::leanh::lean_ctor_set(v___x_898_, 2, v_currMacroScope_886_);
                        crate::leanh::lean_ctor_set(v___x_898_, 3, v_currRecDepth_887_);
                        crate::leanh::lean_ctor_set(v___x_898_, 4, v_maxRecDepth_888_);
                        crate::leanh::lean_ctor_set(v___x_898_, 5, v_ref_897_);
                        v___x_899_ = l_Lean_SourceInfo_fromRef(v_ref_897_, v___x_895_);
                        crate::leanh::lean_dec(v_ref_897_);
                        v___x_900_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__4;
                        v___x_901_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__3), core::ptr::addr_of_mut!(l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__3_once), _init_l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__3);
                        v___x_902_ = l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__5;
                        v___x_903_ = l_Lean_addMacroScope(
                            v_quotContext_885_,
                            v___x_902_,
                            v_currMacroScope_886_,
                        );
                        v___x_904_ = l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__10;
                        crate::leanh::lean_inc_n(v___x_899_, 3);
                        v___x_905_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_905_, 0, v___x_899_);
                        crate::leanh::lean_ctor_set(v___x_905_, 1, v___x_901_);
                        crate::leanh::lean_ctor_set(v___x_905_, 2, v___x_903_);
                        crate::leanh::lean_ctor_set(v___x_905_, 3, v___x_904_);
                        v___x_906_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__17;
                        v___x_907_ = l_Lean_Syntax_node1(v___x_899_, v___x_906_, v_modLit_896_);
                        v___x_908_ =
                            l_Lean_Syntax_node2(v___x_899_, v___x_900_, v___x_905_, v___x_907_);
                        v___x_909_ = l___private_Lake_DSL_Key_0__Lake_DSL_expandFacets(
                            v___x_908_, v_val_883_, v___x_898_, v_a_872_,
                        );
                        crate::leanh::lean_dec_ref_known(v___x_898_, 6);
                        if crate::leanh::lean_obj_tag(v___x_909_) == 0 {
                            v_a_910_ = crate::leanh::lean_ctor_get(v___x_909_, 0);
                            v_a_911_ = crate::leanh::lean_ctor_get(v___x_909_, 1);
                            v_isSharedCheck_925_ =
                                (!crate::leanh::lean_is_exclusive(v___x_909_)) as u8;
                            if v_isSharedCheck_925_ == 0 {
                                v___x_913_ = v___x_909_;
                                v_isShared_914_ = v_isSharedCheck_925_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_911_);
                                crate::leanh::lean_inc(v_a_910_);
                                crate::leanh::lean_dec(v___x_909_);
                                v___x_913_ = crate::leanh::lean_box(0);
                                v_isShared_914_ = v_isSharedCheck_925_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_899_);
                            v_a_926_ = crate::leanh::lean_ctor_get(v___x_909_, 0);
                            v_a_927_ = crate::leanh::lean_ctor_get(v___x_909_, 1);
                            v_isSharedCheck_934_ =
                                (!crate::leanh::lean_is_exclusive(v___x_909_)) as u8;
                            if v_isSharedCheck_934_ == 0 {
                                v___x_929_ = v___x_909_;
                                v_isShared_930_ = v_isSharedCheck_934_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_927_);
                                crate::leanh::lean_inc(v_a_926_);
                                crate::leanh::lean_dec(v___x_909_);
                                v___x_929_ = crate::leanh::lean_box(0);
                                v_isShared_930_ = v_isSharedCheck_934_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_915_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__12), core::ptr::addr_of_mut!(l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__12_once), _init_l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__12);
                v___x_916_ =
                    l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__15;
                crate::leanh::lean_inc(v_currMacroScope_886_);
                crate::leanh::lean_inc(v_quotContext_885_);
                v___x_917_ =
                    l_Lean_addMacroScope(v_quotContext_885_, v___x_916_, v_currMacroScope_886_);
                v___x_918_ =
                    l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__18;
                crate::leanh::lean_inc_n(v___x_899_, 2);
                v___x_919_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_919_, 0, v___x_899_);
                crate::leanh::lean_ctor_set(v___x_919_, 1, v___x_915_);
                crate::leanh::lean_ctor_set(v___x_919_, 2, v___x_917_);
                crate::leanh::lean_ctor_set(v___x_919_, 3, v___x_918_);
                v___x_920_ = l_Lean_Syntax_node1(v___x_899_, v___x_906_, v_a_910_);
                v___x_921_ = l_Lean_Syntax_node2(v___x_899_, v___x_900_, v___x_919_, v___x_920_);
                if v_isShared_914_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_913_, 0, v___x_921_);
                    v___x_923_ = v___x_913_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_924_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_924_, 0, v___x_921_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_924_, 1, v_a_911_);
                    v___x_923_ = v_reuseFailAlloc_924_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_923_;
            }
            3 => {
                if v_isShared_930_ == 0 {
                    v___x_932_ = v___x_929_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_933_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_933_, 0, v_a_926_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_933_, 1, v_a_927_);
                    v___x_932_ = v_reuseFailAlloc_933_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_932_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___boxed(
    mut v_stx_935_: *mut crate::leanh::LeanObject,
    mut v_a_936_: *mut crate::leanh::LeanObject,
    mut v_a_937_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_938_ = l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit(
        v_stx_935_, v_a_936_, v_a_937_,
    );
    crate::leanh::lean_dec_ref(v_a_936_);
    return v_res_938_;
}
pub unsafe fn l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_967_ = l_Lean_Elab_macroAttribute;
    v___x_968_ = l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__1;
    v___x_969_ = l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__10;
    v___x_970_ = crate::leanh::lean_alloc_closure(
        l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___boxed
            as *mut core::ffi::c_void,
        3,
        0,
    );
    v___x_971_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_967_, v___x_968_, v___x_969_, v___x_970_,
    );
    return v___x_971_;
}
pub unsafe fn l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___boxed(
    mut v_a_972_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_973_ = l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1();
    return v_res_973_;
}
pub unsafe fn _init_l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_980_ = l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__2;
    v___x_981_ = l_String_toRawSubstring_x27(v___x_980_);
    return v___x_981_;
}
pub unsafe fn l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit(
    mut v_stx_1001_: *mut crate::leanh::LeanObject,
    mut v_a_1002_: *mut crate::leanh::LeanObject,
    mut v_a_1003_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tgt_1006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1014_: u8 = 0;
    let mut v_quotContext_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: u8 = 0;
    let mut v___x_1019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1032_: u8 = 0;
    let mut v_a_1033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1037_: u8 = 0;
    let mut v___x_1039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1041_: u8 = 0;
    let mut v___x_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: u8 = 0;
    let mut v___x_1044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk_1046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_methods_1053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1069_: u8 = 0;
    let mut v___x_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1073_: u8 = 0;
    let mut v___x_1074_: u8 = 0;
    let mut v___x_1075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tgt_x3f_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1094_: usize = 0;
    let mut v___x_1095_: usize = 0;
    let mut v___x_1096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: u8 = 0;
    let mut v___x_1102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: u8 = 0;
    let mut v___x_1106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: u8 = 0;
    let mut v___x_1110_: u8 = 0;
    let mut v___x_1111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tgt_x3f_1112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1042_ =
                    l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__1;
                crate::leanh::lean_inc(v_stx_1001_);
                v___x_1043_ = l_Lean_Syntax_isOfKind(v_stx_1001_, v___x_1042_);
                if v___x_1043_ == 0 {
                    crate::leanh::lean_dec(v_stx_1001_);
                    v___x_1044_ = l_Lean_Macro_throwUnsupported___redArg(v_a_1003_);
                    return v___x_1044_;
                } else {
                    v___x_1045_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_tk_1046_ = l_Lean_Syntax_getArg(v_stx_1001_, v___x_1045_);
                    v___x_1085_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1086_ = l_Lean_Syntax_getArg(v_stx_1001_, v___x_1085_);
                    v___x_1107_ = crate::leanh::lean_unsigned_to_nat(2);
                    v___x_1108_ = l_Lean_Syntax_getArg(v_stx_1001_, v___x_1107_);
                    v___x_1109_ = l_Lean_Syntax_isNone(v___x_1108_);
                    if v___x_1109_ == 0 {
                        crate::leanh::lean_inc(v___x_1108_);
                        v___x_1110_ = l_Lean_Syntax_matchesNull(v___x_1108_, v___x_1107_);
                        if v___x_1110_ == 0 {
                            crate::leanh::lean_dec(v___x_1108_);
                            crate::leanh::lean_dec(v___x_1086_);
                            crate::leanh::lean_dec(v_tk_1046_);
                            crate::leanh::lean_dec(v_stx_1001_);
                            v___x_1111_ = l_Lean_Macro_throwUnsupported___redArg(v_a_1003_);
                            return v___x_1111_;
                        } else {
                            v_tgt_x3f_1112_ = l_Lean_Syntax_getArg(v___x_1108_, v___x_1085_);
                            crate::leanh::lean_dec(v___x_1108_);
                            v___x_1113_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1113_, 0, v_tgt_x3f_1112_);
                            v_tgt_x3f_1088_ = v___x_1113_;
                            v___y_1089_ = v_a_1002_;
                            v___y_1090_ = v_a_1003_;
                            state = 9;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_1108_);
                        v___x_1114_ = crate::leanh::lean_box(0);
                        v_tgt_x3f_1088_ = v___x_1114_;
                        v___y_1089_ = v_a_1002_;
                        v___y_1090_ = v_a_1003_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1009_ = l___private_Lake_DSL_Key_0__Lake_DSL_expandFacets(
                    v_tgt_1006_,
                    v___y_1005_,
                    v___y_1007_,
                    v___y_1008_,
                );
                if crate::leanh::lean_obj_tag(v___x_1009_) == 0 {
                    v_a_1010_ = crate::leanh::lean_ctor_get(v___x_1009_, 0);
                    v_a_1011_ = crate::leanh::lean_ctor_get(v___x_1009_, 1);
                    v_isSharedCheck_1032_ = (!crate::leanh::lean_is_exclusive(v___x_1009_)) as u8;
                    if v_isSharedCheck_1032_ == 0 {
                        v___x_1013_ = v___x_1009_;
                        v_isShared_1014_ = v_isSharedCheck_1032_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1011_);
                        crate::leanh::lean_inc(v_a_1010_);
                        crate::leanh::lean_dec(v___x_1009_);
                        v___x_1013_ = crate::leanh::lean_box(0);
                        v_isShared_1014_ = v_isSharedCheck_1032_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_1007_);
                    v_a_1033_ = crate::leanh::lean_ctor_get(v___x_1009_, 0);
                    v_a_1034_ = crate::leanh::lean_ctor_get(v___x_1009_, 1);
                    v_isSharedCheck_1041_ = (!crate::leanh::lean_is_exclusive(v___x_1009_)) as u8;
                    if v_isSharedCheck_1041_ == 0 {
                        v___x_1036_ = v___x_1009_;
                        v_isShared_1037_ = v_isSharedCheck_1041_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1034_);
                        crate::leanh::lean_inc(v_a_1033_);
                        crate::leanh::lean_dec(v___x_1009_);
                        v___x_1036_ = crate::leanh::lean_box(0);
                        v_isShared_1037_ = v_isSharedCheck_1041_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v_quotContext_1015_ = crate::leanh::lean_ctor_get(v___y_1007_, 1);
                crate::leanh::lean_inc(v_quotContext_1015_);
                v_currMacroScope_1016_ = crate::leanh::lean_ctor_get(v___y_1007_, 2);
                crate::leanh::lean_inc(v_currMacroScope_1016_);
                v_ref_1017_ = crate::leanh::lean_ctor_get(v___y_1007_, 5);
                crate::leanh::lean_inc(v_ref_1017_);
                crate::leanh::lean_dec_ref(v___y_1007_);
                v___x_1018_ = 0;
                v___x_1019_ = l_Lean_SourceInfo_fromRef(v_ref_1017_, v___x_1018_);
                crate::leanh::lean_dec(v_ref_1017_);
                v___x_1020_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__4;
                v___x_1021_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__12), core::ptr::addr_of_mut!(l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__12_once), _init_l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__12);
                v___x_1022_ =
                    l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__15;
                v___x_1023_ =
                    l_Lean_addMacroScope(v_quotContext_1015_, v___x_1022_, v_currMacroScope_1016_);
                v___x_1024_ =
                    l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__18;
                crate::leanh::lean_inc_n(v___x_1019_, 2);
                v___x_1025_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1025_, 0, v___x_1019_);
                crate::leanh::lean_ctor_set(v___x_1025_, 1, v___x_1021_);
                crate::leanh::lean_ctor_set(v___x_1025_, 2, v___x_1023_);
                crate::leanh::lean_ctor_set(v___x_1025_, 3, v___x_1024_);
                v___x_1026_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__17;
                v___x_1027_ = l_Lean_Syntax_node1(v___x_1019_, v___x_1026_, v_a_1010_);
                v___x_1028_ =
                    l_Lean_Syntax_node2(v___x_1019_, v___x_1020_, v___x_1025_, v___x_1027_);
                if v_isShared_1014_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1013_, 0, v___x_1028_);
                    v___x_1030_ = v___x_1013_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1031_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1031_, 0, v___x_1028_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1031_, 1, v_a_1011_);
                    v___x_1030_ = v_reuseFailAlloc_1031_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1030_;
            }
            4 => {
                if v_isShared_1037_ == 0 {
                    v___x_1039_ = v___x_1036_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1040_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1040_, 0, v_a_1033_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1040_, 1, v_a_1034_);
                    v___x_1039_ = v_reuseFailAlloc_1040_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1039_;
            }
            6 => {
                v_methods_1053_ = crate::leanh::lean_ctor_get(v___y_1050_, 0);
                v_quotContext_1054_ = crate::leanh::lean_ctor_get(v___y_1050_, 1);
                v_currMacroScope_1055_ = crate::leanh::lean_ctor_get(v___y_1050_, 2);
                v_currRecDepth_1056_ = crate::leanh::lean_ctor_get(v___y_1050_, 3);
                v_maxRecDepth_1057_ = crate::leanh::lean_ctor_get(v___y_1050_, 4);
                v_ref_1058_ = crate::leanh::lean_ctor_get(v___y_1050_, 5);
                v_ref_1059_ = l_Lean_replaceRef(v_tk_1046_, v_ref_1058_);
                crate::leanh::lean_dec(v_tk_1046_);
                crate::leanh::lean_inc(v_ref_1059_);
                crate::leanh::lean_inc(v_maxRecDepth_1057_);
                crate::leanh::lean_inc(v_currRecDepth_1056_);
                crate::leanh::lean_inc(v_currMacroScope_1055_);
                crate::leanh::lean_inc(v_quotContext_1054_);
                crate::leanh::lean_inc(v_methods_1053_);
                v___x_1060_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1060_, 0, v_methods_1053_);
                crate::leanh::lean_ctor_set(v___x_1060_, 1, v_quotContext_1054_);
                crate::leanh::lean_ctor_set(v___x_1060_, 2, v_currMacroScope_1055_);
                crate::leanh::lean_ctor_set(v___x_1060_, 3, v_currRecDepth_1056_);
                crate::leanh::lean_ctor_set(v___x_1060_, 4, v_maxRecDepth_1057_);
                crate::leanh::lean_ctor_set(v___x_1060_, 5, v_ref_1059_);
                if crate::leanh::lean_obj_tag(v___y_1049_) == 1 {
                    crate::leanh::lean_dec(v_ref_1059_);
                    v_val_1061_ = crate::leanh::lean_ctor_get(v___y_1049_, 0);
                    crate::leanh::lean_inc(v_val_1061_);
                    crate::leanh::lean_dec_ref_known(v___y_1049_, 1);
                    v___x_1062_ = l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit(
                        v___y_1052_,
                        v_val_1061_,
                        v___x_1060_,
                        v___y_1048_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1062_) == 0 {
                        v_a_1063_ = crate::leanh::lean_ctor_get(v___x_1062_, 0);
                        crate::leanh::lean_inc(v_a_1063_);
                        v_a_1064_ = crate::leanh::lean_ctor_get(v___x_1062_, 1);
                        crate::leanh::lean_inc(v_a_1064_);
                        crate::leanh::lean_dec_ref_known(v___x_1062_, 2);
                        v___y_1005_ = v___y_1051_;
                        v_tgt_1006_ = v_a_1063_;
                        v___y_1007_ = v___x_1060_;
                        v___y_1008_ = v_a_1064_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref_known(v___x_1060_, 6);
                        crate::leanh::lean_dec_ref(v___y_1051_);
                        v_a_1065_ = crate::leanh::lean_ctor_get(v___x_1062_, 0);
                        v_a_1066_ = crate::leanh::lean_ctor_get(v___x_1062_, 1);
                        v_isSharedCheck_1073_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1062_)) as u8;
                        if v_isSharedCheck_1073_ == 0 {
                            v___x_1068_ = v___x_1062_;
                            v_isShared_1069_ = v_isSharedCheck_1073_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1066_);
                            crate::leanh::lean_inc(v_a_1065_);
                            crate::leanh::lean_dec(v___x_1062_);
                            v___x_1068_ = crate::leanh::lean_box(0);
                            v_isShared_1069_ = v_isSharedCheck_1073_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___y_1049_);
                    v___x_1074_ = 0;
                    v___x_1075_ = l_Lean_SourceInfo_fromRef(v_ref_1059_, v___x_1074_);
                    crate::leanh::lean_dec(v_ref_1059_);
                    v___x_1076_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__4;
                    v___x_1077_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__3), core::ptr::addr_of_mut!(l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__3_once), _init_l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__3);
                    v___x_1078_ =
                        l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__5;
                    crate::leanh::lean_inc(v_currMacroScope_1055_);
                    crate::leanh::lean_inc(v_quotContext_1054_);
                    v___x_1079_ = l_Lean_addMacroScope(
                        v_quotContext_1054_,
                        v___x_1078_,
                        v_currMacroScope_1055_,
                    );
                    v___x_1080_ =
                        l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__10;
                    crate::leanh::lean_inc_n(v___x_1075_, 2);
                    v___x_1081_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1081_, 0, v___x_1075_);
                    crate::leanh::lean_ctor_set(v___x_1081_, 1, v___x_1077_);
                    crate::leanh::lean_ctor_set(v___x_1081_, 2, v___x_1079_);
                    crate::leanh::lean_ctor_set(v___x_1081_, 3, v___x_1080_);
                    v___x_1082_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__17;
                    v___x_1083_ = l_Lean_Syntax_node1(v___x_1075_, v___x_1082_, v___y_1052_);
                    v___x_1084_ =
                        l_Lean_Syntax_node2(v___x_1075_, v___x_1076_, v___x_1081_, v___x_1083_);
                    v___y_1005_ = v___y_1051_;
                    v_tgt_1006_ = v___x_1084_;
                    v___y_1007_ = v___x_1060_;
                    v___y_1008_ = v___y_1048_;
                    state = 1;
                    continue;
                }
            }
            7 => {
                if v_isShared_1069_ == 0 {
                    v___x_1071_ = v___x_1068_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1072_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1072_, 0, v_a_1065_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1072_, 1, v_a_1066_);
                    v___x_1071_ = v_reuseFailAlloc_1072_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1071_;
            }
            9 => {
                v___x_1091_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_1092_ = l_Lean_Syntax_getArg(v_stx_1001_, v___x_1091_);
                crate::leanh::lean_dec(v_stx_1001_);
                v___x_1093_ = l_Lean_Syntax_getArgs(v___x_1092_);
                crate::leanh::lean_dec(v___x_1092_);
                v_sz_1094_ = lean_array_size(v___x_1093_);
                v___x_1095_ = 0usize;
                v___x_1096_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit_spec__0(v_sz_1094_, v___x_1095_, v___x_1093_);
                if crate::leanh::lean_obj_tag(v___x_1096_) == 0 {
                    crate::leanh::lean_dec(v_tgt_x3f_1088_);
                    crate::leanh::lean_dec(v___x_1086_);
                    crate::leanh::lean_dec(v_tk_1046_);
                    v___x_1097_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1090_);
                    return v___x_1097_;
                } else {
                    v_val_1098_ = crate::leanh::lean_ctor_get(v___x_1096_, 0);
                    crate::leanh::lean_inc(v_val_1098_);
                    crate::leanh::lean_dec_ref_known(v___x_1096_, 1);
                    v___x_1099_ = l_Lean_Syntax_getOptional_x3f(v___x_1086_);
                    crate::leanh::lean_dec(v___x_1086_);
                    if crate::leanh::lean_obj_tag(v___x_1099_) == 0 {
                        v___x_1100_ = crate::leanh::lean_box(0);
                        v___x_1101_ = 0;
                        crate::leanh::lean_inc(v_tk_1046_);
                        v___x_1102_ = l_Lake_Name_quoteFrom(v_tk_1046_, v___x_1100_, v___x_1101_);
                        v___y_1048_ = v___y_1090_;
                        v___y_1049_ = v_tgt_x3f_1088_;
                        v___y_1050_ = v___y_1089_;
                        v___y_1051_ = v_val_1098_;
                        v___y_1052_ = v___x_1102_;
                        state = 6;
                        continue;
                    } else {
                        v_val_1103_ = crate::leanh::lean_ctor_get(v___x_1099_, 0);
                        crate::leanh::lean_inc(v_val_1103_);
                        crate::leanh::lean_dec_ref_known(v___x_1099_, 1);
                        v___x_1104_ = l_Lean_TSyntax_getId(v_val_1103_);
                        v___x_1105_ = 0;
                        v___x_1106_ = l_Lake_Name_quoteFrom(v_val_1103_, v___x_1104_, v___x_1105_);
                        v___y_1048_ = v___y_1090_;
                        v___y_1049_ = v_tgt_x3f_1088_;
                        v___y_1050_ = v___y_1089_;
                        v___y_1051_ = v_val_1098_;
                        v___y_1052_ = v___x_1106_;
                        state = 6;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___boxed(
    mut v_stx_1115_: *mut crate::leanh::LeanObject,
    mut v_a_1116_: *mut crate::leanh::LeanObject,
    mut v_a_1117_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1118_ = l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit(
        v_stx_1115_,
        v_a_1116_,
        v_a_1117_,
    );
    crate::leanh::lean_dec_ref(v_a_1116_);
    return v_res_1118_;
}
pub unsafe fn l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1124_ = l_Lean_Elab_macroAttribute;
    v___x_1125_ = l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__1;
    v___x_1126_ = l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit__1___closed__1;
    v___x_1127_ = crate::leanh::lean_alloc_closure(
        l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___boxed
            as *mut core::ffi::c_void,
        3,
        0,
    );
    v___x_1128_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1124_,
        v___x_1125_,
        v___x_1126_,
        v___x_1127_,
    );
    return v___x_1128_;
}
pub unsafe fn l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit__1___boxed(
    mut v_a_1129_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1130_ = l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit__1();
    return v_res_1130_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_DSL_Key(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Build_Key(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_DSL_Syntax(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Name(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_DSL_Key(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_DSL_Key(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Build_Key(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_DSL_Syntax(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Util_Name(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_DSL_Key(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_DSL_Key(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_DSL_Key(builtin);
}
