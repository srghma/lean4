// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.CollectParams
// Imports: Lean.Meta.Tactic.Grind.Types
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Meta::Defs::{
    l_Lean_Syntax_SepArray_ofElems, l_Lean_Syntax_TSepArray_getElems___redArg,
    l_Lean_Syntax_isNone, l_Lean_Syntax_structEq,
};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs,
    l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesNull, l_Lean_Syntax_node1, l_Lean_Syntax_node3,
    l_Lean_Syntax_node4, l_Lean_Syntax_node5,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::{
    initialize_Lean_Meta_Tactic_Grind_Types, runtime_initialize_Lean_Meta_Tactic_Grind_Types,
};
use crate::ffi::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::ffi::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::ffi::{
    lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_dec_eq,
    lean_nat_dec_lt, lean_usize_dec_eq,
};
use crate::ffi::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__2_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__3_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [71, 114, 105, 110, 100, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__4_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [116, 104, 109, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__5_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__5_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__5_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__5_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__2_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__5_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__5_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__3_value) as *mut crate::leanh::LeanObject,3168557723425139092 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__5_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__4_value) as *mut crate::leanh::LeanObject,4493657671338864619 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__6_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [103, 114, 105, 110, 100, 76, 101, 109, 109, 97, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__7_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__7_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__7_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__7_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__7_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__2_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__7_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__7_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__6_value) as *mut crate::leanh::LeanObject,9605956393242244281 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__8_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [103, 114, 105, 110, 100, 76, 101, 109, 109, 97, 77, 105, 110, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__8_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__9_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__9_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__9_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__9_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__9_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__2_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__9_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__9_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__8_value) as *mut crate::leanh::LeanObject,15805583526285245505 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__10_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [97, 110, 99, 104, 111, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__10_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__11_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__11_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__11_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__11_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__11_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__2_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__11_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__11_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__10_value) as *mut crate::leanh::LeanObject,12570470872972041128 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__12_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [103, 114, 105, 110, 100, 80, 97, 114, 97, 109, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__12_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__13_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__13_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__13_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__13_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__13_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__2_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__13_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__13_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__12_value) as *mut crate::leanh::LeanObject,6042821575048204304 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__0_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [103, 114, 105, 110, 100, 83, 116, 101, 112, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__2_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__3_value) as *mut crate::leanh::LeanObject,3168557723425139092 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__1_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,6321866296242073541 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__2_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__2_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [115, 111, 114, 114, 121, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__2_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__3_value) as *mut crate::leanh::LeanObject,3168557723425139092 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__1_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__0_value) as *mut crate::leanh::LeanObject,12610174047474239361 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__2_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 101, 120, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__2_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__2_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__3_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__3_value) as *mut crate::leanh::LeanObject,3168557723425139092 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__3_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__2_value) as *mut crate::leanh::LeanObject,7819112639170036602 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__4_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 7, m_data: [103, 114, 105, 110, 100, 194, 183, 95, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__4_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__5_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__5_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__5_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__5_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__2_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__5_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__5_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__3_value) as *mut crate::leanh::LeanObject,3168557723425139092 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__5_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__4_value) as *mut crate::leanh::LeanObject,12389819025714499611 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__6_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [103, 114, 105, 110, 100, 95, 60, 59, 62, 95, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__6_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__7_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__7_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__7_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__7_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__7_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__2_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__7_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__7_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__3_value) as *mut crate::leanh::LeanObject,3168557723425139092 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__7_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__7_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__6_value) as *mut crate::leanh::LeanObject,17356226235442988904 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__8_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [99, 97, 115, 101, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__8_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__9_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__9_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__9_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__9_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__9_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__2_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__9_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__9_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__3_value) as *mut crate::leanh::LeanObject,3168557723425139092 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__9_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__9_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__8_value) as *mut crate::leanh::LeanObject,9932274655851112959 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__10_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [117, 115, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__10_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__11_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__11_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__11_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__11_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__11_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__2_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__11_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__11_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__3_value) as *mut crate::leanh::LeanObject,3168557723425139092 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__11_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__11_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__10_value) as *mut crate::leanh::LeanObject,4803991667162169508 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__12_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [105, 110, 115, 116, 97, 110, 116, 105, 97, 116, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__12_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__13_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__13_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__13_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__13_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__13_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__2_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__13_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__13_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__3_value) as *mut crate::leanh::LeanObject,3168557723425139092 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__13_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__13_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__12_value) as *mut crate::leanh::LeanObject,12928201877799427862 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__14_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [103, 114, 105, 110, 100, 95, 114, 101, 102, 95, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__14_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__15_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__15_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__15_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__15_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__15_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__2_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__15_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__15_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__3_value) as *mut crate::leanh::LeanObject,3168557723425139092 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__15_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__15_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__14_value) as *mut crate::leanh::LeanObject,11143388761733130988 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__16_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [103, 114, 105, 110, 100, 83, 101, 113, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__16_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__17_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__17_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__17_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__17_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__17_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__2_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__17_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__17_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__3_value) as *mut crate::leanh::LeanObject,3168557723425139092 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__17_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__17_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__16_value) as *mut crate::leanh::LeanObject,12547805878916670878 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__17_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__18_value: crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [103, 114, 105, 110, 100, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__18_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__19_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__19_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__19_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__19_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__19_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__2_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__19_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__19_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__3_value) as *mut crate::leanh::LeanObject,3168557723425139092 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__19_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__19_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__18_value) as *mut crate::leanh::LeanObject,13326625262248817187 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__19: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__19_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_collectParamsCore___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_collectParamsCore___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_collectParamsCore___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_collectParamsCore___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_collectParamsCore___closed__0_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_collectParamsCore___closed__0_value) as *mut crate::leanh::LeanObject,0 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_collectParamsCore___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_collectParamsCore___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_mkFinishTactic___closed__0_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [102, 105, 110, 105, 115, 104, 0],
    };
static mut l_Lean_Meta_Grind_mkFinishTactic___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkFinishTactic___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_mkFinishTactic___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Grind_mkFinishTactic___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_mkFinishTactic___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Grind_mkFinishTactic___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_mkFinishTactic___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__2_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Grind_mkFinishTactic___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_mkFinishTactic___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__3_value) as *mut crate::leanh::LeanObject,3168557723425139092 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Grind_mkFinishTactic___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_mkFinishTactic___closed__1_value_aux_3)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_mkFinishTactic___closed__0_value)
                as *mut crate::leanh::LeanObject,
            15503256039972703489 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_mkFinishTactic___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkFinishTactic___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_mkFinishTactic___closed__2_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [110, 117, 108, 108, 0],
    };
static mut l_Lean_Meta_Grind_mkFinishTactic___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkFinishTactic___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_mkFinishTactic___closed__3_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_mkFinishTactic___closed__2_value)
                as *mut crate::leanh::LeanObject,
            9855511589286918680 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_mkFinishTactic___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkFinishTactic___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_mkFinishTactic___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_mkFinishTactic___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_mkFinishTactic___closed__5_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [111, 110, 108, 121, 0],
    };
static mut l_Lean_Meta_Grind_mkFinishTactic___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkFinishTactic___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_mkFinishTactic___closed__6_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_mkFinishTactic___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkFinishTactic___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_mkFinishTactic___closed__7_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [44, 0],
    };
static mut l_Lean_Meta_Grind_mkFinishTactic___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkFinishTactic___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_mkFinishTactic___closed__8_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_mkFinishTactic___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkFinishTactic___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_mkGrindOnlyTactics_mkTac___redArg___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [103, 114, 105, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_mkGrindOnlyTactics_mkTac___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_mkGrindOnlyTactics_mkTac___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_mkGrindOnlyTactics_mkTac___redArg___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_mkGrindOnlyTactics_mkTac___redArg___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_mkGrindOnlyTactics_mkTac___redArg___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_mkGrindOnlyTactics_mkTac___redArg___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_mkGrindOnlyTactics_mkTac___redArg___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__2_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_mkGrindOnlyTactics_mkTac___redArg___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_mkGrindOnlyTactics_mkTac___redArg___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_mkGrindOnlyTactics_mkTac___redArg___closed__0_value) as *mut crate::leanh::LeanObject,7213727686127018646 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_mkGrindOnlyTactics_mkTac___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_mkGrindOnlyTactics_mkTac___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushParam_spec__0_spec__0(
    mut v_a_976_: *mut crate::leanh::LeanObject,
    mut v_as_977_: *mut crate::leanh::LeanObject,
    mut v_i_978_: usize,
    mut v_stop_979_: usize,
) -> u8 {
    let mut v___x_980_: u8 = 0;
    let mut v___x_981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_982_: u8 = 0;
    let mut v___x_983_: usize = 0;
    let mut v___x_984_: usize = 0;
    let mut v___x_986_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_980_ = lean_usize_dec_eq(v_i_978_, v_stop_979_);
                if v___x_980_ == 0 {
                    v___x_981_ = lean_array_uget_borrowed(v_as_977_, v_i_978_);
                    crate::leanh::lean_inc(v___x_981_);
                    crate::leanh::lean_inc(v_a_976_);
                    v___x_982_ = l_Lean_Syntax_structEq(v_a_976_, v___x_981_);
                    if v___x_982_ == 0 {
                        v___x_983_ = 1usize;
                        v___x_984_ = lean_usize_add(v_i_978_, v___x_983_);
                        v_i_978_ = v___x_984_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_a_976_);
                        return v___x_982_;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_976_);
                    v___x_986_ = 0;
                    return v___x_986_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushParam_spec__0_spec__0___boxed(
    mut v_a_987_: *mut crate::leanh::LeanObject,
    mut v_as_988_: *mut crate::leanh::LeanObject,
    mut v_i_989_: *mut crate::leanh::LeanObject,
    mut v_stop_990_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_991_: usize = 0;
    let mut v_stop_boxed_992_: usize = 0;
    let mut v_res_993_: u8 = 0;
    let mut v_r_994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_991_ = crate::leanh::lean_unbox_usize(v_i_989_);
    crate::leanh::lean_dec(v_i_989_);
    v_stop_boxed_992_ = crate::leanh::lean_unbox_usize(v_stop_990_);
    crate::leanh::lean_dec(v_stop_990_);
    v_res_993_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushParam_spec__0_spec__0(v_a_987_, v_as_988_, v_i_boxed_991_, v_stop_boxed_992_);
    crate::leanh::lean_dec_ref(v_as_988_);
    v_r_994_ = crate::leanh::lean_box((v_res_993_) as usize);
    return v_r_994_;
}
pub unsafe fn l_Array_contains___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushParam_spec__0(
    mut v_as_995_: *mut crate::leanh::LeanObject,
    mut v_a_996_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_999_: u8 = 0;
    v___x_997_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_998_ = lean_array_get_size(v_as_995_);
    v___x_999_ = lean_nat_dec_lt(v___x_997_, v___x_998_);
    if v___x_999_ == 0 {
        crate::leanh::lean_dec(v_a_996_);
        return v___x_999_;
    } else {
        if v___x_999_ == 0 {
            crate::leanh::lean_dec(v_a_996_);
            return v___x_999_;
        } else {
            let mut v___x_1000_: usize = 0;
            let mut v___x_1001_: usize = 0;
            let mut v___x_1002_: u8 = 0;
            v___x_1000_ = 0usize;
            v___x_1001_ = lean_usize_of_nat(v___x_998_);
            v___x_1002_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushParam_spec__0_spec__0(v_a_996_, v_as_995_, v___x_1000_, v___x_1001_);
            return v___x_1002_;
        }
    }
}
pub unsafe fn l_Array_contains___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushParam_spec__0___boxed(
    mut v_as_1003_: *mut crate::leanh::LeanObject,
    mut v_a_1004_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1005_: u8 = 0;
    let mut v_r_1006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1005_ = l_Array_contains___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushParam_spec__0(v_as_1003_, v_a_1004_);
    crate::leanh::lean_dec_ref(v_as_1003_);
    v_r_1006_ = crate::leanh::lean_box((v_res_1005_) as usize);
    return v_r_1006_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushParam___redArg(
    mut v_p_1007_: *mut crate::leanh::LeanObject,
    mut v_a_1008_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_1011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1012_: u8 = 0;
    let mut v___x_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_anchors_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasSorry_1016_: u8 = 0;
    let mut v___x_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1019_: u8 = 0;
    let mut v___x_1020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1027_: u8 = 0;
    let mut v___x_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1010_ = lean_st_ref_get(v_a_1008_);
                v_params_1011_ = crate::leanh::lean_ctor_get(v___x_1010_, 0);
                crate::leanh::lean_inc_ref(v_params_1011_);
                crate::leanh::lean_dec(v___x_1010_);
                crate::leanh::lean_inc(v_p_1007_);
                v___x_1012_ = l_Array_contains___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushParam_spec__0(v_params_1011_, v_p_1007_);
                crate::leanh::lean_dec_ref(v_params_1011_);
                if v___x_1012_ == 0 {
                    v___x_1013_ = lean_st_ref_take(v_a_1008_);
                    v_params_1014_ = crate::leanh::lean_ctor_get(v___x_1013_, 0);
                    v_anchors_1015_ = crate::leanh::lean_ctor_get(v___x_1013_, 1);
                    v_hasSorry_1016_ = crate::leanh::lean_ctor_get_uint8(
                        v___x_1013_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v_isSharedCheck_1027_ = (!crate::leanh::lean_is_exclusive(v___x_1013_)) as u8;
                    if v_isSharedCheck_1027_ == 0 {
                        v___x_1018_ = v___x_1013_;
                        v_isShared_1019_ = v_isSharedCheck_1027_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_anchors_1015_);
                        crate::leanh::lean_inc(v_params_1014_);
                        crate::leanh::lean_dec(v___x_1013_);
                        v___x_1018_ = crate::leanh::lean_box(0);
                        v_isShared_1019_ = v_isSharedCheck_1027_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_p_1007_);
                    v___x_1028_ = crate::leanh::lean_box(0);
                    v___x_1029_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1029_, 0, v___x_1028_);
                    return v___x_1029_;
                }
            }
            1 => {
                v___x_1020_ = lean_array_push(v_params_1014_, v_p_1007_);
                if v_isShared_1019_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1018_, 0, v___x_1020_);
                    v___x_1022_ = v___x_1018_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1026_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1026_, 0, v___x_1020_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1026_, 1, v_anchors_1015_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1026_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        v_hasSorry_1016_,
                    );
                    v___x_1022_ = v_reuseFailAlloc_1026_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1023_ = lean_st_ref_set(v_a_1008_, v___x_1022_);
                v___x_1024_ = crate::leanh::lean_box(0);
                v___x_1025_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1025_, 0, v___x_1024_);
                return v___x_1025_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushParam___redArg___boxed(
    mut v_p_1030_: *mut crate::leanh::LeanObject,
    mut v_a_1031_: *mut crate::leanh::LeanObject,
    mut v_a_1032_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1033_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushParam___redArg(v_p_1030_, v_a_1031_);
    crate::leanh::lean_dec(v_a_1031_);
    return v_res_1033_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushParam(
    mut v_p_1034_: *mut crate::leanh::LeanObject,
    mut v_a_1035_: *mut crate::leanh::LeanObject,
    mut v_a_1036_: *mut crate::leanh::LeanObject,
    mut v_a_1037_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1039_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushParam___redArg(v_p_1034_, v_a_1035_);
    return v___x_1039_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushParam___boxed(
    mut v_p_1040_: *mut crate::leanh::LeanObject,
    mut v_a_1041_: *mut crate::leanh::LeanObject,
    mut v_a_1042_: *mut crate::leanh::LeanObject,
    mut v_a_1043_: *mut crate::leanh::LeanObject,
    mut v_a_1044_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1045_ =
        l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushParam(
            v_p_1040_, v_a_1041_, v_a_1042_, v_a_1043_,
        );
    crate::leanh::lean_dec(v_a_1043_);
    crate::leanh::lean_dec_ref(v_a_1042_);
    crate::leanh::lean_dec(v_a_1041_);
    return v_res_1045_;
}
pub unsafe fn l_Array_contains___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushAnchor_spec__0(
    mut v_as_1046_: *mut crate::leanh::LeanObject,
    mut v_a_1047_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1050_: u8 = 0;
    v___x_1048_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1049_ = lean_array_get_size(v_as_1046_);
    v___x_1050_ = lean_nat_dec_lt(v___x_1048_, v___x_1049_);
    if v___x_1050_ == 0 {
        crate::leanh::lean_dec(v_a_1047_);
        return v___x_1050_;
    } else {
        if v___x_1050_ == 0 {
            crate::leanh::lean_dec(v_a_1047_);
            return v___x_1050_;
        } else {
            let mut v___x_1051_: usize = 0;
            let mut v___x_1052_: usize = 0;
            let mut v___x_1053_: u8 = 0;
            v___x_1051_ = 0usize;
            v___x_1052_ = lean_usize_of_nat(v___x_1049_);
            v___x_1053_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushParam_spec__0_spec__0(v_a_1047_, v_as_1046_, v___x_1051_, v___x_1052_);
            return v___x_1053_;
        }
    }
}
pub unsafe fn l_Array_contains___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushAnchor_spec__0___boxed(
    mut v_as_1054_: *mut crate::leanh::LeanObject,
    mut v_a_1055_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1056_: u8 = 0;
    let mut v_r_1057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1056_ = l_Array_contains___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushAnchor_spec__0(v_as_1054_, v_a_1055_);
    crate::leanh::lean_dec_ref(v_as_1054_);
    v_r_1057_ = crate::leanh::lean_box((v_res_1056_) as usize);
    return v_r_1057_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushAnchor___redArg(
    mut v_a_1058_: *mut crate::leanh::LeanObject,
    mut v_a_1059_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_anchors_1062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: u8 = 0;
    let mut v___x_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_anchors_1066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasSorry_1067_: u8 = 0;
    let mut v___x_1069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1070_: u8 = 0;
    let mut v___x_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1078_: u8 = 0;
    let mut v___x_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1061_ = lean_st_ref_get(v_a_1059_);
                v_anchors_1062_ = crate::leanh::lean_ctor_get(v___x_1061_, 1);
                crate::leanh::lean_inc_ref(v_anchors_1062_);
                crate::leanh::lean_dec(v___x_1061_);
                crate::leanh::lean_inc(v_a_1058_);
                v___x_1063_ = l_Array_contains___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushAnchor_spec__0(v_anchors_1062_, v_a_1058_);
                crate::leanh::lean_dec_ref(v_anchors_1062_);
                if v___x_1063_ == 0 {
                    v___x_1064_ = lean_st_ref_take(v_a_1059_);
                    v_params_1065_ = crate::leanh::lean_ctor_get(v___x_1064_, 0);
                    v_anchors_1066_ = crate::leanh::lean_ctor_get(v___x_1064_, 1);
                    v_hasSorry_1067_ = crate::leanh::lean_ctor_get_uint8(
                        v___x_1064_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v_isSharedCheck_1078_ = (!crate::leanh::lean_is_exclusive(v___x_1064_)) as u8;
                    if v_isSharedCheck_1078_ == 0 {
                        v___x_1069_ = v___x_1064_;
                        v_isShared_1070_ = v_isSharedCheck_1078_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_anchors_1066_);
                        crate::leanh::lean_inc(v_params_1065_);
                        crate::leanh::lean_dec(v___x_1064_);
                        v___x_1069_ = crate::leanh::lean_box(0);
                        v_isShared_1070_ = v_isSharedCheck_1078_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1058_);
                    v___x_1079_ = crate::leanh::lean_box(0);
                    v___x_1080_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1080_, 0, v___x_1079_);
                    return v___x_1080_;
                }
            }
            1 => {
                v___x_1071_ = lean_array_push(v_anchors_1066_, v_a_1058_);
                if v_isShared_1070_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1069_, 1, v___x_1071_);
                    v___x_1073_ = v___x_1069_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1077_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1077_, 0, v_params_1065_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1077_, 1, v___x_1071_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1077_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        v_hasSorry_1067_,
                    );
                    v___x_1073_ = v_reuseFailAlloc_1077_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1074_ = lean_st_ref_set(v_a_1059_, v___x_1073_);
                v___x_1075_ = crate::leanh::lean_box(0);
                v___x_1076_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1076_, 0, v___x_1075_);
                return v___x_1076_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushAnchor___redArg___boxed(
    mut v_a_1081_: *mut crate::leanh::LeanObject,
    mut v_a_1082_: *mut crate::leanh::LeanObject,
    mut v_a_1083_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1084_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushAnchor___redArg(v_a_1081_, v_a_1082_);
    crate::leanh::lean_dec(v_a_1082_);
    return v_res_1084_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushAnchor(
    mut v_a_1085_: *mut crate::leanh::LeanObject,
    mut v_a_1086_: *mut crate::leanh::LeanObject,
    mut v_a_1087_: *mut crate::leanh::LeanObject,
    mut v_a_1088_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1090_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushAnchor___redArg(v_a_1085_, v_a_1086_);
    return v___x_1090_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushAnchor___boxed(
    mut v_a_1091_: *mut crate::leanh::LeanObject,
    mut v_a_1092_: *mut crate::leanh::LeanObject,
    mut v_a_1093_: *mut crate::leanh::LeanObject,
    mut v_a_1094_: *mut crate::leanh::LeanObject,
    mut v_a_1095_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1096_ =
        l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushAnchor(
            v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_,
        );
    crate::leanh::lean_dec(v_a_1094_);
    crate::leanh::lean_dec_ref(v_a_1093_);
    crate::leanh::lean_dec(v_a_1092_);
    return v_res_1096_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg(
    mut v_as_1132_: *mut crate::leanh::LeanObject,
    mut v_sz_1133_: usize,
    mut v_i_1134_: usize,
    mut v_b_1135_: *mut crate::leanh::LeanObject,
    mut v___y_1136_: *mut crate::leanh::LeanObject,
    mut v___y_1137_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1141_: usize = 0;
    let mut v___x_1142_: usize = 0;
    let mut v___x_1144_: u8 = 0;
    let mut v___x_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: u8 = 0;
    let mut v___x_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1153_: u8 = 0;
    let mut v___x_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: u8 = 0;
    let mut v___x_1156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1157_: u8 = 0;
    let mut v___x_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: u8 = 0;
    let mut v___x_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1144_ = lean_usize_dec_lt(v_i_1134_, v_sz_1133_);
                if v___x_1144_ == 0 {
                    v___x_1145_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1145_, 0, v_b_1135_);
                    return v___x_1145_;
                } else {
                    v___x_1146_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__5;
                    v___x_1147_ = crate::leanh::lean_box(0);
                    v_a_1148_ = lean_array_uget_borrowed(v_as_1132_, v_i_1134_);
                    crate::leanh::lean_inc(v_a_1148_);
                    v___x_1149_ = l_Lean_Syntax_isOfKind(v_a_1148_, v___x_1146_);
                    if v___x_1149_ == 0 {
                        v_a_1140_ = v___x_1147_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1150_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_1151_ = l_Lean_Syntax_getArg(v_a_1148_, v___x_1150_);
                        v___x_1152_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__7;
                        crate::leanh::lean_inc(v___x_1151_);
                        v___x_1153_ = l_Lean_Syntax_isOfKind(v___x_1151_, v___x_1152_);
                        if v___x_1153_ == 0 {
                            v___x_1154_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__9;
                            crate::leanh::lean_inc(v___x_1151_);
                            v___x_1155_ = l_Lean_Syntax_isOfKind(v___x_1151_, v___x_1154_);
                            if v___x_1155_ == 0 {
                                v___x_1156_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__11;
                                crate::leanh::lean_inc(v___x_1151_);
                                v___x_1157_ = l_Lean_Syntax_isOfKind(v___x_1151_, v___x_1156_);
                                if v___x_1157_ == 0 {
                                    crate::leanh::lean_dec(v___x_1151_);
                                    v_a_1140_ = v___x_1147_;
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_1158_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushAnchor___redArg(v___x_1151_, v___y_1136_);
                                    if crate::leanh::lean_obj_tag(v___x_1158_) == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_1158_, 1);
                                        v_a_1140_ = v___x_1147_;
                                        state = 1;
                                        continue;
                                    } else {
                                        return v___x_1158_;
                                    }
                                }
                            } else {
                                v_ref_1159_ = crate::leanh::lean_ctor_get(v___y_1137_, 5);
                                v___x_1160_ = l_Lean_SourceInfo_fromRef(v_ref_1159_, v___x_1153_);
                                v___x_1161_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__13;
                                v___x_1162_ =
                                    l_Lean_Syntax_node1(v___x_1160_, v___x_1161_, v___x_1151_);
                                v___x_1163_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushParam___redArg(v___x_1162_, v___y_1136_);
                                if crate::leanh::lean_obj_tag(v___x_1163_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_1163_, 1);
                                    v_a_1140_ = v___x_1147_;
                                    state = 1;
                                    continue;
                                } else {
                                    return v___x_1163_;
                                }
                            }
                        } else {
                            v_ref_1164_ = crate::leanh::lean_ctor_get(v___y_1137_, 5);
                            v___x_1165_ = 0;
                            v___x_1166_ = l_Lean_SourceInfo_fromRef(v_ref_1164_, v___x_1165_);
                            v___x_1167_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__13;
                            v___x_1168_ =
                                l_Lean_Syntax_node1(v___x_1166_, v___x_1167_, v___x_1151_);
                            v___x_1169_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushParam___redArg(v___x_1168_, v___y_1136_);
                            if crate::leanh::lean_obj_tag(v___x_1169_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_1169_, 1);
                                v_a_1140_ = v___x_1147_;
                                state = 1;
                                continue;
                            } else {
                                return v___x_1169_;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_1141_ = 1usize;
                v___x_1142_ = lean_usize_add(v_i_1134_, v___x_1141_);
                v_i_1134_ = v___x_1142_;
                v_b_1135_ = v_a_1140_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___boxed(
    mut v_as_1170_: *mut crate::leanh::LeanObject,
    mut v_sz_1171_: *mut crate::leanh::LeanObject,
    mut v_i_1172_: *mut crate::leanh::LeanObject,
    mut v_b_1173_: *mut crate::leanh::LeanObject,
    mut v___y_1174_: *mut crate::leanh::LeanObject,
    mut v___y_1175_: *mut crate::leanh::LeanObject,
    mut v___y_1176_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1177_: usize = 0;
    let mut v_i_boxed_1178_: usize = 0;
    let mut v_res_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1177_ = crate::leanh::lean_unbox_usize(v_sz_1171_);
    crate::leanh::lean_dec(v_sz_1171_);
    v_i_boxed_1178_ = crate::leanh::lean_unbox_usize(v_i_1172_);
    crate::leanh::lean_dec(v_i_1172_);
    v_res_1179_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg(v_as_1170_, v_sz_boxed_1177_, v_i_boxed_1178_, v_b_1173_, v___y_1174_, v___y_1175_);
    crate::leanh::lean_dec_ref(v___y_1175_);
    crate::leanh::lean_dec(v___y_1174_);
    crate::leanh::lean_dec_ref(v_as_1170_);
    return v_res_1179_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams(
    mut v_params_1180_: *mut crate::leanh::LeanObject,
    mut v_a_1181_: *mut crate::leanh::LeanObject,
    mut v_a_1182_: *mut crate::leanh::LeanObject,
    mut v_a_1183_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1187_: usize = 0;
    let mut v___x_1188_: usize = 0;
    let mut v___x_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1192_: u8 = 0;
    let mut v___x_1194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1196_: u8 = 0;
    let mut v_unused_1197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1185_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_params_1180_);
                v___x_1186_ = crate::leanh::lean_box(0);
                v_sz_1187_ = lean_array_size(v___x_1185_);
                v___x_1188_ = 0usize;
                v___x_1189_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg(v___x_1185_, v_sz_1187_, v___x_1188_, v___x_1186_, v_a_1181_, v_a_1182_);
                crate::leanh::lean_dec_ref(v___x_1185_);
                if crate::leanh::lean_obj_tag(v___x_1189_) == 0 {
                    v_isSharedCheck_1196_ = (!crate::leanh::lean_is_exclusive(v___x_1189_)) as u8;
                    if v_isSharedCheck_1196_ == 0 {
                        v_unused_1197_ = crate::leanh::lean_ctor_get(v___x_1189_, 0);
                        crate::leanh::lean_dec(v_unused_1197_);
                        v___x_1191_ = v___x_1189_;
                        v_isShared_1192_ = v_isSharedCheck_1196_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_1189_);
                        v___x_1191_ = crate::leanh::lean_box(0);
                        v_isShared_1192_ = v_isSharedCheck_1196_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_1189_;
                }
            }
            1 => {
                if v_isShared_1192_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1191_, 0, v___x_1186_);
                    v___x_1194_ = v___x_1191_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1195_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1195_, 0, v___x_1186_);
                    v___x_1194_ = v_reuseFailAlloc_1195_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1194_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams___boxed(
    mut v_params_1198_: *mut crate::leanh::LeanObject,
    mut v_a_1199_: *mut crate::leanh::LeanObject,
    mut v_a_1200_: *mut crate::leanh::LeanObject,
    mut v_a_1201_: *mut crate::leanh::LeanObject,
    mut v_a_1202_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1203_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams(v_params_1198_, v_a_1199_, v_a_1200_, v_a_1201_);
    crate::leanh::lean_dec(v_a_1201_);
    crate::leanh::lean_dec_ref(v_a_1200_);
    crate::leanh::lean_dec(v_a_1199_);
    crate::leanh::lean_dec_ref(v_params_1198_);
    return v_res_1203_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0(
    mut v_as_1204_: *mut crate::leanh::LeanObject,
    mut v_sz_1205_: usize,
    mut v_i_1206_: usize,
    mut v_b_1207_: *mut crate::leanh::LeanObject,
    mut v___y_1208_: *mut crate::leanh::LeanObject,
    mut v___y_1209_: *mut crate::leanh::LeanObject,
    mut v___y_1210_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1212_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg(v_as_1204_, v_sz_1205_, v_i_1206_, v_b_1207_, v___y_1208_, v___y_1209_);
    return v___x_1212_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___boxed(
    mut v_as_1213_: *mut crate::leanh::LeanObject,
    mut v_sz_1214_: *mut crate::leanh::LeanObject,
    mut v_i_1215_: *mut crate::leanh::LeanObject,
    mut v_b_1216_: *mut crate::leanh::LeanObject,
    mut v___y_1217_: *mut crate::leanh::LeanObject,
    mut v___y_1218_: *mut crate::leanh::LeanObject,
    mut v___y_1219_: *mut crate::leanh::LeanObject,
    mut v___y_1220_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1221_: usize = 0;
    let mut v_i_boxed_1222_: usize = 0;
    let mut v_res_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1221_ = crate::leanh::lean_unbox_usize(v_sz_1214_);
    crate::leanh::lean_dec(v_sz_1214_);
    v_i_boxed_1222_ = crate::leanh::lean_unbox_usize(v_i_1215_);
    crate::leanh::lean_dec(v_i_1215_);
    v_res_1223_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0(v_as_1213_, v_sz_boxed_1221_, v_i_boxed_1222_, v_b_1216_, v___y_1217_, v___y_1218_, v___y_1219_);
    crate::leanh::lean_dec(v___y_1219_);
    crate::leanh::lean_dec_ref(v___y_1218_);
    crate::leanh::lean_dec(v___y_1217_);
    crate::leanh::lean_dec_ref(v_as_1213_);
    return v_res_1223_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__1(
    mut v_as_1309_: *mut crate::leanh::LeanObject,
    mut v_sz_1310_: usize,
    mut v_i_1311_: usize,
    mut v_b_1312_: *mut crate::leanh::LeanObject,
    mut v___y_1313_: *mut crate::leanh::LeanObject,
    mut v___y_1314_: *mut crate::leanh::LeanObject,
    mut v___y_1315_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1317_: u8 = 0;
    let mut v___x_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: u8 = 0;
    let mut v___x_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: usize = 0;
    let mut v___x_1334_: usize = 0;
    let mut v_a_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1339_: u8 = 0;
    let mut v___x_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1343_: u8 = 0;
    let mut v___x_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: u8 = 0;
    let mut v___x_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: u8 = 0;
    let mut v___x_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: u8 = 0;
    let mut v___x_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1317_ = lean_usize_dec_lt(v_i_1311_, v_sz_1310_);
                if v___x_1317_ == 0 {
                    v___x_1318_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1318_, 0, v_b_1312_);
                    return v___x_1318_;
                } else {
                    crate::leanh::lean_dec_ref(v_b_1312_);
                    v___x_1319_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__1;
                    v_a_1320_ = lean_array_uget_borrowed(v_as_1309_, v_i_1311_);
                    crate::leanh::lean_inc(v_a_1320_);
                    v___x_1321_ = l_Lean_Syntax_isOfKind(v_a_1320_, v___x_1319_);
                    if v___x_1321_ == 0 {
                        v___x_1322_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__3;
                        v___x_1323_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1323_, 0, v___x_1322_);
                        return v___x_1323_;
                    } else {
                        v___x_1324_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_1325_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__4;
                        v___x_1326_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1327_ = l_Lean_Syntax_getArg(v_a_1320_, v___x_1324_);
                        v___x_1344_ = l_Lean_Syntax_getArg(v_a_1320_, v___x_1326_);
                        v___x_1345_ = l_Lean_Syntax_isNone(v___x_1344_);
                        if v___x_1345_ == 0 {
                            v___x_1346_ = crate::leanh::lean_unsigned_to_nat(2);
                            crate::leanh::lean_inc(v___x_1344_);
                            v___x_1347_ = l_Lean_Syntax_matchesNull(v___x_1344_, v___x_1346_);
                            if v___x_1347_ == 0 {
                                crate::leanh::lean_dec(v___x_1344_);
                                crate::leanh::lean_dec(v___x_1327_);
                                v___x_1348_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__3;
                                v___x_1349_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1349_, 0, v___x_1348_);
                                return v___x_1349_;
                            } else {
                                v___x_1350_ = l_Lean_Syntax_getArg(v___x_1344_, v___x_1326_);
                                crate::leanh::lean_dec(v___x_1344_);
                                v___x_1351_ = l_Lean_Syntax_matchesNull(v___x_1350_, v___x_1326_);
                                if v___x_1351_ == 0 {
                                    crate::leanh::lean_dec(v___x_1327_);
                                    v___x_1352_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__3;
                                    v___x_1353_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_1353_, 0, v___x_1352_);
                                    return v___x_1353_;
                                } else {
                                    v___y_1329_ = v___y_1313_;
                                    v___y_1330_ = v___y_1314_;
                                    v___y_1331_ = v___y_1315_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_1344_);
                            v___y_1329_ = v___y_1313_;
                            v___y_1330_ = v___y_1314_;
                            v___y_1331_ = v___y_1315_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1332_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect(v___x_1327_, v___y_1329_, v___y_1330_, v___y_1331_);
                if crate::leanh::lean_obj_tag(v___x_1332_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_1332_, 1);
                    v___x_1333_ = 1usize;
                    v___x_1334_ = lean_usize_add(v_i_1311_, v___x_1333_);
                    v_i_1311_ = v___x_1334_;
                    v_b_1312_ = v___x_1325_;
                    state = 0;
                    continue;
                } else {
                    v_a_1336_ = crate::leanh::lean_ctor_get(v___x_1332_, 0);
                    v_isSharedCheck_1343_ = (!crate::leanh::lean_is_exclusive(v___x_1332_)) as u8;
                    if v_isSharedCheck_1343_ == 0 {
                        v___x_1338_ = v___x_1332_;
                        v_isShared_1339_ = v_isSharedCheck_1343_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1336_);
                        crate::leanh::lean_dec(v___x_1332_);
                        v___x_1338_ = crate::leanh::lean_box(0);
                        v_isShared_1339_ = v_isSharedCheck_1343_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1339_ == 0 {
                    v___x_1341_ = v___x_1338_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1342_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1342_, 0, v_a_1336_);
                    v___x_1341_ = v_reuseFailAlloc_1342_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1341_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect(
    mut v_tac_1354_: *mut crate::leanh::LeanObject,
    mut v_a_1355_: *mut crate::leanh::LeanObject,
    mut v_a_1356_: *mut crate::leanh::LeanObject,
    mut v_a_1357_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: u8 = 0;
    let mut v___x_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: u8 = 0;
    let mut v___x_1363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: u8 = 0;
    let mut v___x_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: u8 = 0;
    let mut v___x_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: u8 = 0;
    let mut v___x_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: u8 = 0;
    let mut v___x_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: u8 = 0;
    let mut v___x_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: u8 = 0;
    let mut v___x_1383_: u8 = 0;
    let mut v___x_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_x3f_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: u8 = 0;
    let mut v___x_1398_: u8 = 0;
    let mut v___x_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: u8 = 0;
    let mut v___x_1403_: u8 = 0;
    let mut v___x_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: u8 = 0;
    let mut v___x_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: u8 = 0;
    let mut v___x_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tac_u2081_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tac_u2082_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: u8 = 0;
    let mut v___x_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: u8 = 0;
    let mut v___x_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_seq_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1446_: usize = 0;
    let mut v___x_1447_: usize = 0;
    let mut v___x_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1452_: u8 = 0;
    let mut v_fst_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1461_: u8 = 0;
    let mut v_a_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1465_: u8 = 0;
    let mut v___x_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1469_: u8 = 0;
    let mut v___x_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: u8 = 0;
    let mut v___x_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: u8 = 0;
    let mut v___x_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: u8 = 0;
    let mut v___x_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_seq_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1492_: usize = 0;
    let mut v___x_1493_: usize = 0;
    let mut v___x_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1498_: u8 = 0;
    let mut v_fst_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1507_: u8 = 0;
    let mut v_a_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1511_: u8 = 0;
    let mut v___x_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1515_: u8 = 0;
    let mut v___x_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_anchors_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1521_: u8 = 0;
    let mut v___x_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1528_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1359_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__1;
                crate::leanh::lean_inc(v_tac_1354_);
                v___x_1360_ = l_Lean_Syntax_isOfKind(v_tac_1354_, v___x_1359_);
                if v___x_1360_ == 0 {
                    v___x_1361_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__3;
                    crate::leanh::lean_inc(v_tac_1354_);
                    v___x_1362_ = l_Lean_Syntax_isOfKind(v_tac_1354_, v___x_1361_);
                    if v___x_1362_ == 0 {
                        v___x_1363_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__5;
                        crate::leanh::lean_inc(v_tac_1354_);
                        v___x_1364_ = l_Lean_Syntax_isOfKind(v_tac_1354_, v___x_1363_);
                        if v___x_1364_ == 0 {
                            v___x_1365_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__7;
                            crate::leanh::lean_inc(v_tac_1354_);
                            v___x_1366_ = l_Lean_Syntax_isOfKind(v_tac_1354_, v___x_1365_);
                            if v___x_1366_ == 0 {
                                v___x_1367_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__9;
                                crate::leanh::lean_inc(v_tac_1354_);
                                v___x_1368_ = l_Lean_Syntax_isOfKind(v_tac_1354_, v___x_1367_);
                                if v___x_1368_ == 0 {
                                    v___x_1369_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__11;
                                    crate::leanh::lean_inc(v_tac_1354_);
                                    v___x_1370_ = l_Lean_Syntax_isOfKind(v_tac_1354_, v___x_1369_);
                                    if v___x_1370_ == 0 {
                                        v___x_1371_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__13;
                                        crate::leanh::lean_inc(v_tac_1354_);
                                        v___x_1372_ =
                                            l_Lean_Syntax_isOfKind(v_tac_1354_, v___x_1371_);
                                        if v___x_1372_ == 0 {
                                            crate::leanh::lean_dec(v_tac_1354_);
                                            v___x_1373_ = crate::leanh::lean_box(0);
                                            v___x_1374_ =
                                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v___x_1374_,
                                                0,
                                                v___x_1373_,
                                            );
                                            return v___x_1374_;
                                        } else {
                                            v___x_1375_ = crate::leanh::lean_unsigned_to_nat(1);
                                            v___x_1401_ =
                                                l_Lean_Syntax_getArg(v_tac_1354_, v___x_1375_);
                                            v___x_1402_ = l_Lean_Syntax_isNone(v___x_1401_);
                                            if v___x_1402_ == 0 {
                                                v___x_1403_ = l_Lean_Syntax_matchesNull(
                                                    v___x_1401_,
                                                    v___x_1375_,
                                                );
                                                if v___x_1403_ == 0 {
                                                    crate::leanh::lean_dec(v_tac_1354_);
                                                    v___x_1404_ = crate::leanh::lean_box(0);
                                                    v___x_1405_ = crate::leanh::lean_alloc_ctor(
                                                        0,
                                                        1,
                                                        (0) as u32,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_1405_,
                                                        0,
                                                        v___x_1404_,
                                                    );
                                                    return v___x_1405_;
                                                } else {
                                                    v___y_1392_ = v_a_1355_;
                                                    v___y_1393_ = v_a_1356_;
                                                    v___y_1394_ = v_a_1357_;
                                                    state = 2;
                                                    continue;
                                                }
                                            } else {
                                                crate::leanh::lean_dec(v___x_1401_);
                                                v___y_1392_ = v_a_1355_;
                                                v___y_1393_ = v_a_1356_;
                                                v___y_1394_ = v_a_1357_;
                                                state = 2;
                                                continue;
                                            }
                                        }
                                    } else {
                                        v___x_1406_ = crate::leanh::lean_unsigned_to_nat(2);
                                        v___x_1407_ =
                                            l_Lean_Syntax_getArg(v_tac_1354_, v___x_1406_);
                                        crate::leanh::lean_dec(v_tac_1354_);
                                        v_params_1408_ = l_Lean_Syntax_getArgs(v___x_1407_);
                                        crate::leanh::lean_dec(v___x_1407_);
                                        v___x_1409_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams(v_params_1408_, v_a_1355_, v_a_1356_, v_a_1357_);
                                        crate::leanh::lean_dec_ref(v_params_1408_);
                                        return v___x_1409_;
                                    }
                                } else {
                                    v___x_1410_ = crate::leanh::lean_unsigned_to_nat(1);
                                    v___x_1411_ = l_Lean_Syntax_getArg(v_tac_1354_, v___x_1410_);
                                    crate::leanh::lean_dec(v_tac_1354_);
                                    v___x_1412_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__15;
                                    crate::leanh::lean_inc(v___x_1411_);
                                    v___x_1413_ = l_Lean_Syntax_isOfKind(v___x_1411_, v___x_1412_);
                                    if v___x_1413_ == 0 {
                                        crate::leanh::lean_dec(v___x_1411_);
                                        v___x_1414_ = crate::leanh::lean_box(0);
                                        v___x_1415_ =
                                            crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_1415_, 0, v___x_1414_);
                                        return v___x_1415_;
                                    } else {
                                        v___x_1416_ = crate::leanh::lean_unsigned_to_nat(0);
                                        v_a_1417_ = l_Lean_Syntax_getArg(v___x_1411_, v___x_1416_);
                                        crate::leanh::lean_dec(v___x_1411_);
                                        v___x_1418_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__11;
                                        crate::leanh::lean_inc(v_a_1417_);
                                        v___x_1419_ =
                                            l_Lean_Syntax_isOfKind(v_a_1417_, v___x_1418_);
                                        if v___x_1419_ == 0 {
                                            crate::leanh::lean_dec(v_a_1417_);
                                            v___x_1420_ = crate::leanh::lean_box(0);
                                            v___x_1421_ =
                                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v___x_1421_,
                                                0,
                                                v___x_1420_,
                                            );
                                            return v___x_1421_;
                                        } else {
                                            v___x_1422_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushAnchor___redArg(v_a_1417_, v_a_1355_);
                                            return v___x_1422_;
                                        }
                                    }
                                }
                            } else {
                                v___x_1423_ = crate::leanh::lean_unsigned_to_nat(0);
                                v_tac_u2081_1424_ = l_Lean_Syntax_getArg(v_tac_1354_, v___x_1423_);
                                v___x_1425_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect(v_tac_u2081_1424_, v_a_1355_, v_a_1356_, v_a_1357_);
                                if crate::leanh::lean_obj_tag(v___x_1425_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_1425_, 1);
                                    v___x_1426_ = crate::leanh::lean_unsigned_to_nat(2);
                                    v_tac_u2082_1427_ =
                                        l_Lean_Syntax_getArg(v_tac_1354_, v___x_1426_);
                                    crate::leanh::lean_dec(v_tac_1354_);
                                    v_tac_1354_ = v_tac_u2082_1427_;
                                    state = 0;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_tac_1354_);
                                    return v___x_1425_;
                                }
                            }
                        } else {
                            v___x_1429_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_1430_ = l_Lean_Syntax_getArg(v_tac_1354_, v___x_1429_);
                            crate::leanh::lean_dec(v_tac_1354_);
                            v___x_1431_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__17;
                            crate::leanh::lean_inc(v___x_1430_);
                            v___x_1432_ = l_Lean_Syntax_isOfKind(v___x_1430_, v___x_1431_);
                            if v___x_1432_ == 0 {
                                crate::leanh::lean_dec(v___x_1430_);
                                v___x_1433_ = crate::leanh::lean_box(0);
                                v___x_1434_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1434_, 0, v___x_1433_);
                                return v___x_1434_;
                            } else {
                                v___x_1435_ = crate::leanh::lean_unsigned_to_nat(0);
                                v___x_1436_ = l_Lean_Syntax_getArg(v___x_1430_, v___x_1435_);
                                crate::leanh::lean_dec(v___x_1430_);
                                v___x_1437_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__19;
                                crate::leanh::lean_inc(v___x_1436_);
                                v___x_1438_ = l_Lean_Syntax_isOfKind(v___x_1436_, v___x_1437_);
                                if v___x_1438_ == 0 {
                                    crate::leanh::lean_dec(v___x_1436_);
                                    v___x_1439_ = crate::leanh::lean_box(0);
                                    v___x_1440_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_1440_, 0, v___x_1439_);
                                    return v___x_1440_;
                                } else {
                                    v___x_1441_ = l_Lean_Syntax_getArg(v___x_1436_, v___x_1435_);
                                    crate::leanh::lean_dec(v___x_1436_);
                                    v_seq_1442_ = l_Lean_Syntax_getArgs(v___x_1441_);
                                    crate::leanh::lean_dec(v___x_1441_);
                                    v___x_1443_ =
                                        l_Lean_Syntax_TSepArray_getElems___redArg(v_seq_1442_);
                                    crate::leanh::lean_dec_ref(v_seq_1442_);
                                    v___x_1444_ = crate::leanh::lean_box(0);
                                    v___x_1445_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__4;
                                    v_sz_1446_ = lean_array_size(v___x_1443_);
                                    v___x_1447_ = 0usize;
                                    v___x_1448_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0(v___x_1443_, v_sz_1446_, v___x_1447_, v___x_1445_, v_a_1355_, v_a_1356_, v_a_1357_);
                                    crate::leanh::lean_dec_ref(v___x_1443_);
                                    if crate::leanh::lean_obj_tag(v___x_1448_) == 0 {
                                        v_a_1449_ = crate::leanh::lean_ctor_get(v___x_1448_, 0);
                                        v_isSharedCheck_1461_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_1448_)) as u8;
                                        if v_isSharedCheck_1461_ == 0 {
                                            v___x_1451_ = v___x_1448_;
                                            v_isShared_1452_ = v_isSharedCheck_1461_;
                                            state = 3;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_1449_);
                                            crate::leanh::lean_dec(v___x_1448_);
                                            v___x_1451_ = crate::leanh::lean_box(0);
                                            v_isShared_1452_ = v_isSharedCheck_1461_;
                                            state = 3;
                                            continue;
                                        }
                                    } else {
                                        v_a_1462_ = crate::leanh::lean_ctor_get(v___x_1448_, 0);
                                        v_isSharedCheck_1469_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_1448_)) as u8;
                                        if v_isSharedCheck_1469_ == 0 {
                                            v___x_1464_ = v___x_1448_;
                                            v_isShared_1465_ = v_isSharedCheck_1469_;
                                            state = 6;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_1462_);
                                            crate::leanh::lean_dec(v___x_1448_);
                                            v___x_1464_ = crate::leanh::lean_box(0);
                                            v_isShared_1465_ = v_isSharedCheck_1469_;
                                            state = 6;
                                            continue;
                                        }
                                    }
                                }
                            }
                        }
                    } else {
                        v___x_1470_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_1471_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1472_ = l_Lean_Syntax_getArg(v_tac_1354_, v___x_1471_);
                        v___x_1473_ = l_Lean_Syntax_matchesNull(v___x_1472_, v___x_1470_);
                        if v___x_1473_ == 0 {
                            crate::leanh::lean_dec(v_tac_1354_);
                            v___x_1474_ = crate::leanh::lean_box(0);
                            v___x_1475_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1475_, 0, v___x_1474_);
                            return v___x_1475_;
                        } else {
                            v___x_1476_ = crate::leanh::lean_unsigned_to_nat(3);
                            v___x_1477_ = l_Lean_Syntax_getArg(v_tac_1354_, v___x_1476_);
                            crate::leanh::lean_dec(v_tac_1354_);
                            v___x_1478_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__17;
                            crate::leanh::lean_inc(v___x_1477_);
                            v___x_1479_ = l_Lean_Syntax_isOfKind(v___x_1477_, v___x_1478_);
                            if v___x_1479_ == 0 {
                                crate::leanh::lean_dec(v___x_1477_);
                                v___x_1480_ = crate::leanh::lean_box(0);
                                v___x_1481_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1481_, 0, v___x_1480_);
                                return v___x_1481_;
                            } else {
                                v___x_1482_ = l_Lean_Syntax_getArg(v___x_1477_, v___x_1470_);
                                crate::leanh::lean_dec(v___x_1477_);
                                v___x_1483_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__19;
                                crate::leanh::lean_inc(v___x_1482_);
                                v___x_1484_ = l_Lean_Syntax_isOfKind(v___x_1482_, v___x_1483_);
                                if v___x_1484_ == 0 {
                                    crate::leanh::lean_dec(v___x_1482_);
                                    v___x_1485_ = crate::leanh::lean_box(0);
                                    v___x_1486_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_1486_, 0, v___x_1485_);
                                    return v___x_1486_;
                                } else {
                                    v___x_1487_ = l_Lean_Syntax_getArg(v___x_1482_, v___x_1470_);
                                    crate::leanh::lean_dec(v___x_1482_);
                                    v_seq_1488_ = l_Lean_Syntax_getArgs(v___x_1487_);
                                    crate::leanh::lean_dec(v___x_1487_);
                                    v___x_1489_ =
                                        l_Lean_Syntax_TSepArray_getElems___redArg(v_seq_1488_);
                                    crate::leanh::lean_dec_ref(v_seq_1488_);
                                    v___x_1490_ = crate::leanh::lean_box(0);
                                    v___x_1491_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__4;
                                    v_sz_1492_ = lean_array_size(v___x_1489_);
                                    v___x_1493_ = 0usize;
                                    v___x_1494_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__1(v___x_1489_, v_sz_1492_, v___x_1493_, v___x_1491_, v_a_1355_, v_a_1356_, v_a_1357_);
                                    crate::leanh::lean_dec_ref(v___x_1489_);
                                    if crate::leanh::lean_obj_tag(v___x_1494_) == 0 {
                                        v_a_1495_ = crate::leanh::lean_ctor_get(v___x_1494_, 0);
                                        v_isSharedCheck_1507_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_1494_)) as u8;
                                        if v_isSharedCheck_1507_ == 0 {
                                            v___x_1497_ = v___x_1494_;
                                            v_isShared_1498_ = v_isSharedCheck_1507_;
                                            state = 8;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_1495_);
                                            crate::leanh::lean_dec(v___x_1494_);
                                            v___x_1497_ = crate::leanh::lean_box(0);
                                            v_isShared_1498_ = v_isSharedCheck_1507_;
                                            state = 8;
                                            continue;
                                        }
                                    } else {
                                        v_a_1508_ = crate::leanh::lean_ctor_get(v___x_1494_, 0);
                                        v_isSharedCheck_1515_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_1494_)) as u8;
                                        if v_isSharedCheck_1515_ == 0 {
                                            v___x_1510_ = v___x_1494_;
                                            v_isShared_1511_ = v_isSharedCheck_1515_;
                                            state = 11;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_1508_);
                                            crate::leanh::lean_dec(v___x_1494_);
                                            v___x_1510_ = crate::leanh::lean_box(0);
                                            v_isShared_1511_ = v_isSharedCheck_1515_;
                                            state = 11;
                                            continue;
                                        }
                                    }
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_tac_1354_);
                    v___x_1516_ = lean_st_ref_take(v_a_1355_);
                    v_params_1517_ = crate::leanh::lean_ctor_get(v___x_1516_, 0);
                    v_anchors_1518_ = crate::leanh::lean_ctor_get(v___x_1516_, 1);
                    v_isSharedCheck_1528_ = (!crate::leanh::lean_is_exclusive(v___x_1516_)) as u8;
                    if v_isSharedCheck_1528_ == 0 {
                        v___x_1520_ = v___x_1516_;
                        v_isShared_1521_ = v_isSharedCheck_1528_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_anchors_1518_);
                        crate::leanh::lean_inc(v_params_1517_);
                        crate::leanh::lean_dec(v___x_1516_);
                        v___x_1520_ = crate::leanh::lean_box(0);
                        v_isShared_1521_ = v_isSharedCheck_1528_;
                        state = 13;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1380_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_1381_ = l_Lean_Syntax_getArg(v_tac_1354_, v___x_1380_);
                crate::leanh::lean_dec(v_tac_1354_);
                v___x_1382_ = l_Lean_Syntax_isNone(v___x_1381_);
                if v___x_1382_ == 0 {
                    crate::leanh::lean_inc(v___x_1381_);
                    v___x_1383_ = l_Lean_Syntax_matchesNull(v___x_1381_, v___x_1380_);
                    if v___x_1383_ == 0 {
                        crate::leanh::lean_dec(v___x_1381_);
                        v___x_1384_ = crate::leanh::lean_box(0);
                        v___x_1385_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1385_, 0, v___x_1384_);
                        return v___x_1385_;
                    } else {
                        v___x_1386_ = l_Lean_Syntax_getArg(v___x_1381_, v___x_1375_);
                        crate::leanh::lean_dec(v___x_1381_);
                        v_params_x3f_1387_ = l_Lean_Syntax_getArgs(v___x_1386_);
                        crate::leanh::lean_dec(v___x_1386_);
                        v___x_1388_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams(v_params_x3f_1387_, v___y_1377_, v___y_1378_, v___y_1379_);
                        crate::leanh::lean_dec_ref(v_params_x3f_1387_);
                        return v___x_1388_;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1381_);
                    v___x_1389_ = crate::leanh::lean_box(0);
                    v___x_1390_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1390_, 0, v___x_1389_);
                    return v___x_1390_;
                }
            }
            2 => {
                v___x_1395_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_1396_ = l_Lean_Syntax_getArg(v_tac_1354_, v___x_1395_);
                v___x_1397_ = l_Lean_Syntax_isNone(v___x_1396_);
                if v___x_1397_ == 0 {
                    v___x_1398_ = l_Lean_Syntax_matchesNull(v___x_1396_, v___x_1375_);
                    if v___x_1398_ == 0 {
                        crate::leanh::lean_dec(v_tac_1354_);
                        v___x_1399_ = crate::leanh::lean_box(0);
                        v___x_1400_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1400_, 0, v___x_1399_);
                        return v___x_1400_;
                    } else {
                        v___y_1377_ = v___y_1392_;
                        v___y_1378_ = v___y_1393_;
                        v___y_1379_ = v___y_1394_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1396_);
                    v___y_1377_ = v___y_1392_;
                    v___y_1378_ = v___y_1393_;
                    v___y_1379_ = v___y_1394_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v_fst_1453_ = crate::leanh::lean_ctor_get(v_a_1449_, 0);
                crate::leanh::lean_inc(v_fst_1453_);
                crate::leanh::lean_dec(v_a_1449_);
                if crate::leanh::lean_obj_tag(v_fst_1453_) == 0 {
                    if v_isShared_1452_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1451_, 0, v___x_1444_);
                        v___x_1455_ = v___x_1451_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1456_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1456_, 0, v___x_1444_);
                        v___x_1455_ = v_reuseFailAlloc_1456_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_val_1457_ = crate::leanh::lean_ctor_get(v_fst_1453_, 0);
                    crate::leanh::lean_inc(v_val_1457_);
                    crate::leanh::lean_dec_ref_known(v_fst_1453_, 1);
                    if v_isShared_1452_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1451_, 0, v_val_1457_);
                        v___x_1459_ = v___x_1451_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1460_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1460_, 0, v_val_1457_);
                        v___x_1459_ = v_reuseFailAlloc_1460_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_1455_;
            }
            5 => {
                return v___x_1459_;
            }
            6 => {
                if v_isShared_1465_ == 0 {
                    v___x_1467_ = v___x_1464_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1468_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1468_, 0, v_a_1462_);
                    v___x_1467_ = v_reuseFailAlloc_1468_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1467_;
            }
            8 => {
                v_fst_1499_ = crate::leanh::lean_ctor_get(v_a_1495_, 0);
                crate::leanh::lean_inc(v_fst_1499_);
                crate::leanh::lean_dec(v_a_1495_);
                if crate::leanh::lean_obj_tag(v_fst_1499_) == 0 {
                    if v_isShared_1498_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1497_, 0, v___x_1490_);
                        v___x_1501_ = v___x_1497_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_1502_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1502_, 0, v___x_1490_);
                        v___x_1501_ = v_reuseFailAlloc_1502_;
                        state = 9;
                        continue;
                    }
                } else {
                    v_val_1503_ = crate::leanh::lean_ctor_get(v_fst_1499_, 0);
                    crate::leanh::lean_inc(v_val_1503_);
                    crate::leanh::lean_dec_ref_known(v_fst_1499_, 1);
                    if v_isShared_1498_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1497_, 0, v_val_1503_);
                        v___x_1505_ = v___x_1497_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_1506_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_val_1503_);
                        v___x_1505_ = v_reuseFailAlloc_1506_;
                        state = 10;
                        continue;
                    }
                }
            }
            9 => {
                return v___x_1501_;
            }
            10 => {
                return v___x_1505_;
            }
            11 => {
                if v_isShared_1511_ == 0 {
                    v___x_1513_ = v___x_1510_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1514_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1514_, 0, v_a_1508_);
                    v___x_1513_ = v_reuseFailAlloc_1514_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1513_;
            }
            13 => {
                if v_isShared_1521_ == 0 {
                    v___x_1523_ = v___x_1520_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1527_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_params_1517_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1527_, 1, v_anchors_1518_);
                    v___x_1523_ = v_reuseFailAlloc_1527_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1523_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_1360_,
                );
                v___x_1524_ = lean_st_ref_set(v_a_1355_, v___x_1523_);
                v___x_1525_ = crate::leanh::lean_box(0);
                v___x_1526_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1526_, 0, v___x_1525_);
                return v___x_1526_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0(
    mut v_as_1529_: *mut crate::leanh::LeanObject,
    mut v_sz_1530_: usize,
    mut v_i_1531_: usize,
    mut v_b_1532_: *mut crate::leanh::LeanObject,
    mut v___y_1533_: *mut crate::leanh::LeanObject,
    mut v___y_1534_: *mut crate::leanh::LeanObject,
    mut v___y_1535_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1537_: u8 = 0;
    let mut v___x_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: u8 = 0;
    let mut v___x_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: usize = 0;
    let mut v___x_1554_: usize = 0;
    let mut v_a_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1559_: u8 = 0;
    let mut v___x_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1563_: u8 = 0;
    let mut v___x_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: u8 = 0;
    let mut v___x_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: u8 = 0;
    let mut v___x_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: u8 = 0;
    let mut v___x_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1537_ = lean_usize_dec_lt(v_i_1531_, v_sz_1530_);
                if v___x_1537_ == 0 {
                    v___x_1538_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1538_, 0, v_b_1532_);
                    return v___x_1538_;
                } else {
                    crate::leanh::lean_dec_ref(v_b_1532_);
                    v___x_1539_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__1;
                    v_a_1540_ = lean_array_uget_borrowed(v_as_1529_, v_i_1531_);
                    crate::leanh::lean_inc(v_a_1540_);
                    v___x_1541_ = l_Lean_Syntax_isOfKind(v_a_1540_, v___x_1539_);
                    if v___x_1541_ == 0 {
                        v___x_1542_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__3;
                        v___x_1543_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1543_, 0, v___x_1542_);
                        return v___x_1543_;
                    } else {
                        v___x_1544_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_1545_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__4;
                        v___x_1546_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1547_ = l_Lean_Syntax_getArg(v_a_1540_, v___x_1544_);
                        v___x_1564_ = l_Lean_Syntax_getArg(v_a_1540_, v___x_1546_);
                        v___x_1565_ = l_Lean_Syntax_isNone(v___x_1564_);
                        if v___x_1565_ == 0 {
                            v___x_1566_ = crate::leanh::lean_unsigned_to_nat(2);
                            crate::leanh::lean_inc(v___x_1564_);
                            v___x_1567_ = l_Lean_Syntax_matchesNull(v___x_1564_, v___x_1566_);
                            if v___x_1567_ == 0 {
                                crate::leanh::lean_dec(v___x_1564_);
                                crate::leanh::lean_dec(v___x_1547_);
                                v___x_1568_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__3;
                                v___x_1569_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1569_, 0, v___x_1568_);
                                return v___x_1569_;
                            } else {
                                v___x_1570_ = l_Lean_Syntax_getArg(v___x_1564_, v___x_1546_);
                                crate::leanh::lean_dec(v___x_1564_);
                                v___x_1571_ = l_Lean_Syntax_matchesNull(v___x_1570_, v___x_1546_);
                                if v___x_1571_ == 0 {
                                    crate::leanh::lean_dec(v___x_1547_);
                                    v___x_1572_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__3;
                                    v___x_1573_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_1573_, 0, v___x_1572_);
                                    return v___x_1573_;
                                } else {
                                    v___y_1549_ = v___y_1533_;
                                    v___y_1550_ = v___y_1534_;
                                    v___y_1551_ = v___y_1535_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_1564_);
                            v___y_1549_ = v___y_1533_;
                            v___y_1550_ = v___y_1534_;
                            v___y_1551_ = v___y_1535_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1552_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect(v___x_1547_, v___y_1549_, v___y_1550_, v___y_1551_);
                if crate::leanh::lean_obj_tag(v___x_1552_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_1552_, 1);
                    v___x_1553_ = 1usize;
                    v___x_1554_ = lean_usize_add(v_i_1531_, v___x_1553_);
                    v_i_1531_ = v___x_1554_;
                    v_b_1532_ = v___x_1545_;
                    state = 0;
                    continue;
                } else {
                    v_a_1556_ = crate::leanh::lean_ctor_get(v___x_1552_, 0);
                    v_isSharedCheck_1563_ = (!crate::leanh::lean_is_exclusive(v___x_1552_)) as u8;
                    if v_isSharedCheck_1563_ == 0 {
                        v___x_1558_ = v___x_1552_;
                        v_isShared_1559_ = v_isSharedCheck_1563_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1556_);
                        crate::leanh::lean_dec(v___x_1552_);
                        v___x_1558_ = crate::leanh::lean_box(0);
                        v_isShared_1559_ = v_isSharedCheck_1563_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1559_ == 0 {
                    v___x_1561_ = v___x_1558_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1562_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1562_, 0, v_a_1556_);
                    v___x_1561_ = v_reuseFailAlloc_1562_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1561_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___boxed(
    mut v_as_1574_: *mut crate::leanh::LeanObject,
    mut v_sz_1575_: *mut crate::leanh::LeanObject,
    mut v_i_1576_: *mut crate::leanh::LeanObject,
    mut v_b_1577_: *mut crate::leanh::LeanObject,
    mut v___y_1578_: *mut crate::leanh::LeanObject,
    mut v___y_1579_: *mut crate::leanh::LeanObject,
    mut v___y_1580_: *mut crate::leanh::LeanObject,
    mut v___y_1581_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1582_: usize = 0;
    let mut v_i_boxed_1583_: usize = 0;
    let mut v_res_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1582_ = crate::leanh::lean_unbox_usize(v_sz_1575_);
    crate::leanh::lean_dec(v_sz_1575_);
    v_i_boxed_1583_ = crate::leanh::lean_unbox_usize(v_i_1576_);
    crate::leanh::lean_dec(v_i_1576_);
    v_res_1584_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0(v_as_1574_, v_sz_boxed_1582_, v_i_boxed_1583_, v_b_1577_, v___y_1578_, v___y_1579_, v___y_1580_);
    crate::leanh::lean_dec(v___y_1580_);
    crate::leanh::lean_dec_ref(v___y_1579_);
    crate::leanh::lean_dec(v___y_1578_);
    crate::leanh::lean_dec_ref(v_as_1574_);
    return v_res_1584_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__1___boxed(
    mut v_as_1585_: *mut crate::leanh::LeanObject,
    mut v_sz_1586_: *mut crate::leanh::LeanObject,
    mut v_i_1587_: *mut crate::leanh::LeanObject,
    mut v_b_1588_: *mut crate::leanh::LeanObject,
    mut v___y_1589_: *mut crate::leanh::LeanObject,
    mut v___y_1590_: *mut crate::leanh::LeanObject,
    mut v___y_1591_: *mut crate::leanh::LeanObject,
    mut v___y_1592_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1593_: usize = 0;
    let mut v_i_boxed_1594_: usize = 0;
    let mut v_res_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1593_ = crate::leanh::lean_unbox_usize(v_sz_1586_);
    crate::leanh::lean_dec(v_sz_1586_);
    v_i_boxed_1594_ = crate::leanh::lean_unbox_usize(v_i_1587_);
    crate::leanh::lean_dec(v_i_1587_);
    v_res_1595_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__1(v_as_1585_, v_sz_boxed_1593_, v_i_boxed_1594_, v_b_1588_, v___y_1589_, v___y_1590_, v___y_1591_);
    crate::leanh::lean_dec(v___y_1591_);
    crate::leanh::lean_dec_ref(v___y_1590_);
    crate::leanh::lean_dec(v___y_1589_);
    crate::leanh::lean_dec_ref(v_as_1585_);
    return v_res_1595_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___boxed(
    mut v_tac_1596_: *mut crate::leanh::LeanObject,
    mut v_a_1597_: *mut crate::leanh::LeanObject,
    mut v_a_1598_: *mut crate::leanh::LeanObject,
    mut v_a_1599_: *mut crate::leanh::LeanObject,
    mut v_a_1600_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1601_ =
        l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect(
            v_tac_1596_,
            v_a_1597_,
            v_a_1598_,
            v_a_1599_,
        );
    crate::leanh::lean_dec(v_a_1599_);
    crate::leanh::lean_dec_ref(v_a_1598_);
    crate::leanh::lean_dec(v_a_1597_);
    return v_res_1601_;
}
pub unsafe fn l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_main_spec__0(
    mut v_as_1602_: *mut crate::leanh::LeanObject,
    mut v___y_1603_: *mut crate::leanh::LeanObject,
    mut v___y_1604_: *mut crate::leanh::LeanObject,
    mut v___y_1605_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_1602_) == 0 {
                    v___x_1607_ = crate::leanh::lean_box(0);
                    v___x_1608_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1608_, 0, v___x_1607_);
                    return v___x_1608_;
                } else {
                    v_head_1609_ = crate::leanh::lean_ctor_get(v_as_1602_, 0);
                    crate::leanh::lean_inc(v_head_1609_);
                    v_tail_1610_ = crate::leanh::lean_ctor_get(v_as_1602_, 1);
                    crate::leanh::lean_inc(v_tail_1610_);
                    crate::leanh::lean_dec_ref_known(v_as_1602_, 2);
                    v___x_1611_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect(v_head_1609_, v___y_1603_, v___y_1604_, v___y_1605_);
                    if crate::leanh::lean_obj_tag(v___x_1611_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_1611_, 1);
                        v_as_1602_ = v_tail_1610_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_tail_1610_);
                        return v___x_1611_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_main_spec__0___boxed(
    mut v_as_1613_: *mut crate::leanh::LeanObject,
    mut v___y_1614_: *mut crate::leanh::LeanObject,
    mut v___y_1615_: *mut crate::leanh::LeanObject,
    mut v___y_1616_: *mut crate::leanh::LeanObject,
    mut v___y_1617_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1618_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_main_spec__0(v_as_1613_, v___y_1614_, v___y_1615_, v___y_1616_);
    crate::leanh::lean_dec(v___y_1616_);
    crate::leanh::lean_dec_ref(v___y_1615_);
    crate::leanh::lean_dec(v___y_1614_);
    return v_res_1618_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_main(
    mut v_seq_1619_: *mut crate::leanh::LeanObject,
    mut v_a_1620_: *mut crate::leanh::LeanObject,
    mut v_a_1621_: *mut crate::leanh::LeanObject,
    mut v_a_1622_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1624_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_main_spec__0(v_seq_1619_, v_a_1620_, v_a_1621_, v_a_1622_);
    return v___x_1624_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_main___boxed(
    mut v_seq_1625_: *mut crate::leanh::LeanObject,
    mut v_a_1626_: *mut crate::leanh::LeanObject,
    mut v_a_1627_: *mut crate::leanh::LeanObject,
    mut v_a_1628_: *mut crate::leanh::LeanObject,
    mut v_a_1629_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1630_ =
        l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_main(
            v_seq_1625_,
            v_a_1626_,
            v_a_1627_,
            v_a_1628_,
        );
    crate::leanh::lean_dec(v_a_1628_);
    crate::leanh::lean_dec_ref(v_a_1627_);
    crate::leanh::lean_dec(v_a_1626_);
    return v_res_1630_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_collectParamsCore_spec__0___redArg(
    mut v_sz_1631_: usize,
    mut v_i_1632_: usize,
    mut v_bs_1633_: *mut crate::leanh::LeanObject,
    mut v___y_1634_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1636_: u8 = 0;
    let mut v___x_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: u8 = 0;
    let mut v___x_1643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: usize = 0;
    let mut v___x_1647_: usize = 0;
    let mut v___x_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1636_ = lean_usize_dec_lt(v_i_1632_, v_sz_1631_);
                if v___x_1636_ == 0 {
                    v___x_1637_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1637_, 0, v_bs_1633_);
                    return v___x_1637_;
                } else {
                    v_ref_1638_ = crate::leanh::lean_ctor_get(v___y_1634_, 5);
                    v_v_1639_ = lean_array_uget(v_bs_1633_, v_i_1632_);
                    v___x_1640_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1641_ = lean_array_uset(v_bs_1633_, v_i_1632_, v___x_1640_);
                    v___x_1642_ = 0;
                    v___x_1643_ = l_Lean_SourceInfo_fromRef(v_ref_1638_, v___x_1642_);
                    v___x_1644_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__13;
                    v___x_1645_ = l_Lean_Syntax_node1(v___x_1643_, v___x_1644_, v_v_1639_);
                    v___x_1646_ = 1usize;
                    v___x_1647_ = lean_usize_add(v_i_1632_, v___x_1646_);
                    v___x_1648_ = lean_array_uset(v_bs_x27_1641_, v_i_1632_, v___x_1645_);
                    v_i_1632_ = v___x_1647_;
                    v_bs_1633_ = v___x_1648_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_collectParamsCore_spec__0___redArg___boxed(
    mut v_sz_1650_: *mut crate::leanh::LeanObject,
    mut v_i_1651_: *mut crate::leanh::LeanObject,
    mut v_bs_1652_: *mut crate::leanh::LeanObject,
    mut v___y_1653_: *mut crate::leanh::LeanObject,
    mut v___y_1654_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1655_: usize = 0;
    let mut v_i_boxed_1656_: usize = 0;
    let mut v_res_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1655_ = crate::leanh::lean_unbox_usize(v_sz_1650_);
    crate::leanh::lean_dec(v_sz_1650_);
    v_i_boxed_1656_ = crate::leanh::lean_unbox_usize(v_i_1651_);
    crate::leanh::lean_dec(v_i_1651_);
    v_res_1657_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_collectParamsCore_spec__0___redArg(v_sz_boxed_1655_, v_i_boxed_1656_, v_bs_1652_, v___y_1653_);
    crate::leanh::lean_dec_ref(v___y_1653_);
    return v_res_1657_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_collectParamsCore(
    mut v_seq_1663_: *mut crate::leanh::LeanObject,
    mut v_a_1664_: *mut crate::leanh::LeanObject,
    mut v_a_1665_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_anchors_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasSorry_1673_: u8 = 0;
    let mut v_sz_1674_: usize = 0;
    let mut v___x_1675_: usize = 0;
    let mut v___x_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1680_: u8 = 0;
    let mut v___x_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1687_: u8 = 0;
    let mut v_a_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1691_: u8 = 0;
    let mut v___x_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1695_: u8 = 0;
    let mut v_a_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1699_: u8 = 0;
    let mut v___x_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1703_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1667_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_collectParamsCore___closed__1;
                v___x_1668_ = lean_st_mk_ref(v___x_1667_);
                v___x_1669_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_main_spec__0(v_seq_1663_, v___x_1668_, v_a_1664_, v_a_1665_);
                if crate::leanh::lean_obj_tag(v___x_1669_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_1669_, 1);
                    v___x_1670_ = lean_st_ref_get(v___x_1668_);
                    crate::leanh::lean_dec(v___x_1668_);
                    v_params_1671_ = crate::leanh::lean_ctor_get(v___x_1670_, 0);
                    crate::leanh::lean_inc_ref(v_params_1671_);
                    v_anchors_1672_ = crate::leanh::lean_ctor_get(v___x_1670_, 1);
                    crate::leanh::lean_inc_ref(v_anchors_1672_);
                    v_hasSorry_1673_ = crate::leanh::lean_ctor_get_uint8(
                        v___x_1670_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    crate::leanh::lean_dec(v___x_1670_);
                    v_sz_1674_ = lean_array_size(v_anchors_1672_);
                    v___x_1675_ = 0usize;
                    v___x_1676_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_collectParamsCore_spec__0___redArg(v_sz_1674_, v___x_1675_, v_anchors_1672_, v_a_1664_);
                    if crate::leanh::lean_obj_tag(v___x_1676_) == 0 {
                        v_a_1677_ = crate::leanh::lean_ctor_get(v___x_1676_, 0);
                        v_isSharedCheck_1687_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1676_)) as u8;
                        if v_isSharedCheck_1687_ == 0 {
                            v___x_1679_ = v___x_1676_;
                            v_isShared_1680_ = v_isSharedCheck_1687_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1677_);
                            crate::leanh::lean_dec(v___x_1676_);
                            v___x_1679_ = crate::leanh::lean_box(0);
                            v_isShared_1680_ = v_isSharedCheck_1687_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_params_1671_);
                        v_a_1688_ = crate::leanh::lean_ctor_get(v___x_1676_, 0);
                        v_isSharedCheck_1695_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1676_)) as u8;
                        if v_isSharedCheck_1695_ == 0 {
                            v___x_1690_ = v___x_1676_;
                            v_isShared_1691_ = v_isSharedCheck_1695_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1688_);
                            crate::leanh::lean_dec(v___x_1676_);
                            v___x_1690_ = crate::leanh::lean_box(0);
                            v_isShared_1691_ = v_isSharedCheck_1695_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1668_);
                    v_a_1696_ = crate::leanh::lean_ctor_get(v___x_1669_, 0);
                    v_isSharedCheck_1703_ = (!crate::leanh::lean_is_exclusive(v___x_1669_)) as u8;
                    if v_isSharedCheck_1703_ == 0 {
                        v___x_1698_ = v___x_1669_;
                        v_isShared_1699_ = v_isSharedCheck_1703_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1696_);
                        crate::leanh::lean_dec(v___x_1669_);
                        v___x_1698_ = crate::leanh::lean_box(0);
                        v_isShared_1699_ = v_isSharedCheck_1703_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1681_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1681_, 0, v_params_1671_);
                crate::leanh::lean_ctor_set(v___x_1681_, 1, v_a_1677_);
                v___x_1682_ = crate::leanh::lean_box((v_hasSorry_1673_) as usize);
                v___x_1683_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1683_, 0, v___x_1682_);
                crate::leanh::lean_ctor_set(v___x_1683_, 1, v___x_1681_);
                if v_isShared_1680_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1679_, 0, v___x_1683_);
                    v___x_1685_ = v___x_1679_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1686_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1686_, 0, v___x_1683_);
                    v___x_1685_ = v_reuseFailAlloc_1686_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1685_;
            }
            3 => {
                if v_isShared_1691_ == 0 {
                    v___x_1693_ = v___x_1690_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1694_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1694_, 0, v_a_1688_);
                    v___x_1693_ = v_reuseFailAlloc_1694_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1693_;
            }
            5 => {
                if v_isShared_1699_ == 0 {
                    v___x_1701_ = v___x_1698_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1702_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1702_, 0, v_a_1696_);
                    v___x_1701_ = v_reuseFailAlloc_1702_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1701_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_collectParamsCore___boxed(
    mut v_seq_1704_: *mut crate::leanh::LeanObject,
    mut v_a_1705_: *mut crate::leanh::LeanObject,
    mut v_a_1706_: *mut crate::leanh::LeanObject,
    mut v_a_1707_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1708_ =
        l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_collectParamsCore(
            v_seq_1704_,
            v_a_1705_,
            v_a_1706_,
        );
    crate::leanh::lean_dec(v_a_1706_);
    crate::leanh::lean_dec_ref(v_a_1705_);
    return v_res_1708_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_collectParamsCore_spec__0(
    mut v_sz_1709_: usize,
    mut v_i_1710_: usize,
    mut v_bs_1711_: *mut crate::leanh::LeanObject,
    mut v___y_1712_: *mut crate::leanh::LeanObject,
    mut v___y_1713_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1715_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_collectParamsCore_spec__0___redArg(v_sz_1709_, v_i_1710_, v_bs_1711_, v___y_1712_);
    return v___x_1715_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_collectParamsCore_spec__0___boxed(
    mut v_sz_1716_: *mut crate::leanh::LeanObject,
    mut v_i_1717_: *mut crate::leanh::LeanObject,
    mut v_bs_1718_: *mut crate::leanh::LeanObject,
    mut v___y_1719_: *mut crate::leanh::LeanObject,
    mut v___y_1720_: *mut crate::leanh::LeanObject,
    mut v___y_1721_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1722_: usize = 0;
    let mut v_i_boxed_1723_: usize = 0;
    let mut v_res_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1722_ = crate::leanh::lean_unbox_usize(v_sz_1716_);
    crate::leanh::lean_dec(v_sz_1716_);
    v_i_boxed_1723_ = crate::leanh::lean_unbox_usize(v_i_1717_);
    crate::leanh::lean_dec(v_i_1717_);
    v_res_1724_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_collectParamsCore_spec__0(v_sz_boxed_1722_, v_i_boxed_1723_, v_bs_1718_, v___y_1719_, v___y_1720_);
    crate::leanh::lean_dec(v___y_1720_);
    crate::leanh::lean_dec_ref(v___y_1719_);
    return v_res_1724_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_collectParams(
    mut v_seq_1725_: *mut crate::leanh::LeanObject,
    mut v_a_1726_: *mut crate::leanh::LeanObject,
    mut v_a_1727_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1733_: u8 = 0;
    let mut v_snd_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1741_: u8 = 0;
    let mut v_a_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1745_: u8 = 0;
    let mut v___x_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1749_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1729_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_collectParamsCore(v_seq_1725_, v_a_1726_, v_a_1727_);
                if crate::leanh::lean_obj_tag(v___x_1729_) == 0 {
                    v_a_1730_ = crate::leanh::lean_ctor_get(v___x_1729_, 0);
                    v_isSharedCheck_1741_ = (!crate::leanh::lean_is_exclusive(v___x_1729_)) as u8;
                    if v_isSharedCheck_1741_ == 0 {
                        v___x_1732_ = v___x_1729_;
                        v_isShared_1733_ = v_isSharedCheck_1741_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1730_);
                        crate::leanh::lean_dec(v___x_1729_);
                        v___x_1732_ = crate::leanh::lean_box(0);
                        v_isShared_1733_ = v_isSharedCheck_1741_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1742_ = crate::leanh::lean_ctor_get(v___x_1729_, 0);
                    v_isSharedCheck_1749_ = (!crate::leanh::lean_is_exclusive(v___x_1729_)) as u8;
                    if v_isSharedCheck_1749_ == 0 {
                        v___x_1744_ = v___x_1729_;
                        v_isShared_1745_ = v_isSharedCheck_1749_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1742_);
                        crate::leanh::lean_dec(v___x_1729_);
                        v___x_1744_ = crate::leanh::lean_box(0);
                        v_isShared_1745_ = v_isSharedCheck_1749_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_1734_ = crate::leanh::lean_ctor_get(v_a_1730_, 1);
                crate::leanh::lean_inc(v_snd_1734_);
                crate::leanh::lean_dec(v_a_1730_);
                v_fst_1735_ = crate::leanh::lean_ctor_get(v_snd_1734_, 0);
                crate::leanh::lean_inc(v_fst_1735_);
                v_snd_1736_ = crate::leanh::lean_ctor_get(v_snd_1734_, 1);
                crate::leanh::lean_inc(v_snd_1736_);
                crate::leanh::lean_dec(v_snd_1734_);
                v___x_1737_ = l_Array_append___redArg(v_fst_1735_, v_snd_1736_);
                crate::leanh::lean_dec(v_snd_1736_);
                if v_isShared_1733_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1732_, 0, v___x_1737_);
                    v___x_1739_ = v___x_1732_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1740_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1740_, 0, v___x_1737_);
                    v___x_1739_ = v_reuseFailAlloc_1740_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1739_;
            }
            3 => {
                if v_isShared_1745_ == 0 {
                    v___x_1747_ = v___x_1744_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1748_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1748_, 0, v_a_1742_);
                    v___x_1747_ = v_reuseFailAlloc_1748_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1747_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_collectParams___boxed(
    mut v_seq_1750_: *mut crate::leanh::LeanObject,
    mut v_a_1751_: *mut crate::leanh::LeanObject,
    mut v_a_1752_: *mut crate::leanh::LeanObject,
    mut v_a_1753_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1754_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_collectParams(
        v_seq_1750_,
        v_a_1751_,
        v_a_1752_,
    );
    crate::leanh::lean_dec(v_a_1752_);
    crate::leanh::lean_dec_ref(v_a_1751_);
    return v_res_1754_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_mkFinishTactic___closed__4() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1765_ = l_Array_mkArray0(crate::leanh::lean_box(0));
    return v___x_1765_;
}
pub unsafe fn l_Lean_Meta_Grind_mkFinishTactic(
    mut v_seq_1770_: *mut crate::leanh::LeanObject,
    mut v_a_1771_: *mut crate::leanh::LeanObject,
    mut v_a_1772_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1778_: u8 = 0;
    let mut v_ref_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: u8 = 0;
    let mut v___x_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1804_: u8 = 0;
    let mut v_a_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1808_: u8 = 0;
    let mut v___x_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1812_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1774_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_collectParams(v_seq_1770_, v_a_1771_, v_a_1772_);
                if crate::leanh::lean_obj_tag(v___x_1774_) == 0 {
                    v_a_1775_ = crate::leanh::lean_ctor_get(v___x_1774_, 0);
                    v_isSharedCheck_1804_ = (!crate::leanh::lean_is_exclusive(v___x_1774_)) as u8;
                    if v_isSharedCheck_1804_ == 0 {
                        v___x_1777_ = v___x_1774_;
                        v_isShared_1778_ = v_isSharedCheck_1804_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1775_);
                        crate::leanh::lean_dec(v___x_1774_);
                        v___x_1777_ = crate::leanh::lean_box(0);
                        v_isShared_1778_ = v_isSharedCheck_1804_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1805_ = crate::leanh::lean_ctor_get(v___x_1774_, 0);
                    v_isSharedCheck_1812_ = (!crate::leanh::lean_is_exclusive(v___x_1774_)) as u8;
                    if v_isSharedCheck_1812_ == 0 {
                        v___x_1807_ = v___x_1774_;
                        v_isShared_1808_ = v_isSharedCheck_1812_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1805_);
                        crate::leanh::lean_dec(v___x_1774_);
                        v___x_1807_ = crate::leanh::lean_box(0);
                        v_isShared_1808_ = v_isSharedCheck_1812_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_ref_1779_ = crate::leanh::lean_ctor_get(v_a_1771_, 5);
                v___x_1780_ = 0;
                v___x_1781_ = l_Lean_SourceInfo_fromRef(v_ref_1779_, v___x_1780_);
                v___x_1782_ = l_Lean_Meta_Grind_mkFinishTactic___closed__0;
                v___x_1783_ = l_Lean_Meta_Grind_mkFinishTactic___closed__1;
                crate::leanh::lean_inc_n(v___x_1781_, 8);
                v___x_1784_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1784_, 0, v___x_1781_);
                crate::leanh::lean_ctor_set(v___x_1784_, 1, v___x_1782_);
                v___x_1785_ = l_Lean_Meta_Grind_mkFinishTactic___closed__3;
                v___x_1786_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkFinishTactic___closed__4),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkFinishTactic___closed__4_once),
                    _init_l_Lean_Meta_Grind_mkFinishTactic___closed__4,
                );
                v___x_1787_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1787_, 0, v___x_1781_);
                crate::leanh::lean_ctor_set(v___x_1787_, 1, v___x_1785_);
                crate::leanh::lean_ctor_set(v___x_1787_, 2, v___x_1786_);
                v___x_1788_ = l_Lean_Meta_Grind_mkFinishTactic___closed__5;
                v___x_1789_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1789_, 0, v___x_1781_);
                crate::leanh::lean_ctor_set(v___x_1789_, 1, v___x_1788_);
                v___x_1790_ = l_Lean_Syntax_node1(v___x_1781_, v___x_1785_, v___x_1789_);
                v___x_1791_ = l_Lean_Meta_Grind_mkFinishTactic___closed__6;
                v___x_1792_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1792_, 0, v___x_1781_);
                crate::leanh::lean_ctor_set(v___x_1792_, 1, v___x_1791_);
                v___x_1793_ = l_Lean_Meta_Grind_mkFinishTactic___closed__7;
                v___x_1794_ = l_Lean_Syntax_SepArray_ofElems(v___x_1793_, v_a_1775_);
                crate::leanh::lean_dec(v_a_1775_);
                v___x_1795_ = l_Array_append___redArg(v___x_1786_, v___x_1794_);
                crate::leanh::lean_dec_ref(v___x_1794_);
                v___x_1796_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1796_, 0, v___x_1781_);
                crate::leanh::lean_ctor_set(v___x_1796_, 1, v___x_1785_);
                crate::leanh::lean_ctor_set(v___x_1796_, 2, v___x_1795_);
                v___x_1797_ = l_Lean_Meta_Grind_mkFinishTactic___closed__8;
                v___x_1798_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1798_, 0, v___x_1781_);
                crate::leanh::lean_ctor_set(v___x_1798_, 1, v___x_1797_);
                v___x_1799_ = l_Lean_Syntax_node3(
                    v___x_1781_,
                    v___x_1785_,
                    v___x_1792_,
                    v___x_1796_,
                    v___x_1798_,
                );
                v___x_1800_ = l_Lean_Syntax_node4(
                    v___x_1781_,
                    v___x_1783_,
                    v___x_1784_,
                    v___x_1787_,
                    v___x_1790_,
                    v___x_1799_,
                );
                if v_isShared_1778_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1777_, 0, v___x_1800_);
                    v___x_1802_ = v___x_1777_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1803_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1803_, 0, v___x_1800_);
                    v___x_1802_ = v_reuseFailAlloc_1803_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1802_;
            }
            3 => {
                if v_isShared_1808_ == 0 {
                    v___x_1810_ = v___x_1807_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1811_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1811_, 0, v_a_1805_);
                    v___x_1810_ = v_reuseFailAlloc_1811_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1810_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_mkFinishTactic___boxed(
    mut v_seq_1813_: *mut crate::leanh::LeanObject,
    mut v_a_1814_: *mut crate::leanh::LeanObject,
    mut v_a_1815_: *mut crate::leanh::LeanObject,
    mut v_a_1816_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1817_ = l_Lean_Meta_Grind_mkFinishTactic(v_seq_1813_, v_a_1814_, v_a_1815_);
    crate::leanh::lean_dec(v_a_1815_);
    crate::leanh::lean_dec_ref(v_a_1814_);
    return v_res_1817_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_mkGrindOnlyTactics_mkTac___redArg(
    mut v_cfg_1824_: *mut crate::leanh::LeanObject,
    mut v_params_1825_: *mut crate::leanh::LeanObject,
    mut v_a_1826_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: u8 = 0;
    v___x_1828_ = lean_array_get_size(v_params_1825_);
    v___x_1829_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1830_ = lean_nat_dec_eq(v___x_1828_, v___x_1829_);
    if v___x_1830_ == 0 {
        let mut v_ref_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
        let mut v___x_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_ref_1831_ = crate::leanh::lean_ctor_get(v_a_1826_, 5);
        v___x_1832_ = l_Lean_SourceInfo_fromRef(v_ref_1831_, v___x_1830_);
        v___x_1833_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_mkGrindOnlyTactics_mkTac___redArg___closed__0;
        v___x_1834_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_mkGrindOnlyTactics_mkTac___redArg___closed__1;
        crate::leanh::lean_inc_n(v___x_1832_, 8);
        v___x_1835_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1835_, 0, v___x_1832_);
        crate::leanh::lean_ctor_set(v___x_1835_, 1, v___x_1833_);
        v___x_1836_ = l_Lean_Meta_Grind_mkFinishTactic___closed__3;
        v___x_1837_ = l_Lean_Meta_Grind_mkFinishTactic___closed__5;
        v___x_1838_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1838_, 0, v___x_1832_);
        crate::leanh::lean_ctor_set(v___x_1838_, 1, v___x_1837_);
        v___x_1839_ = l_Lean_Syntax_node1(v___x_1832_, v___x_1836_, v___x_1838_);
        v___x_1840_ = l_Lean_Meta_Grind_mkFinishTactic___closed__6;
        v___x_1841_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1841_, 0, v___x_1832_);
        crate::leanh::lean_ctor_set(v___x_1841_, 1, v___x_1840_);
        v___x_1842_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkFinishTactic___closed__4),
            core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkFinishTactic___closed__4_once),
            _init_l_Lean_Meta_Grind_mkFinishTactic___closed__4,
        );
        v___x_1843_ = l_Lean_Meta_Grind_mkFinishTactic___closed__7;
        v___x_1844_ = l_Lean_Syntax_SepArray_ofElems(v___x_1843_, v_params_1825_);
        v___x_1845_ = l_Array_append___redArg(v___x_1842_, v___x_1844_);
        crate::leanh::lean_dec_ref(v___x_1844_);
        v___x_1846_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1846_, 0, v___x_1832_);
        crate::leanh::lean_ctor_set(v___x_1846_, 1, v___x_1836_);
        crate::leanh::lean_ctor_set(v___x_1846_, 2, v___x_1845_);
        v___x_1847_ = l_Lean_Meta_Grind_mkFinishTactic___closed__8;
        v___x_1848_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1848_, 0, v___x_1832_);
        crate::leanh::lean_ctor_set(v___x_1848_, 1, v___x_1847_);
        v___x_1849_ = l_Lean_Syntax_node3(
            v___x_1832_,
            v___x_1836_,
            v___x_1841_,
            v___x_1846_,
            v___x_1848_,
        );
        v___x_1850_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1850_, 0, v___x_1832_);
        crate::leanh::lean_ctor_set(v___x_1850_, 1, v___x_1836_);
        crate::leanh::lean_ctor_set(v___x_1850_, 2, v___x_1842_);
        v___x_1851_ = l_Lean_Syntax_node5(
            v___x_1832_,
            v___x_1834_,
            v___x_1835_,
            v_cfg_1824_,
            v___x_1839_,
            v___x_1849_,
            v___x_1850_,
        );
        v___x_1852_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1852_, 0, v___x_1851_);
        return v___x_1852_;
    } else {
        let mut v_ref_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1854_: u8 = 0;
        let mut v___x_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_ref_1853_ = crate::leanh::lean_ctor_get(v_a_1826_, 5);
        v___x_1854_ = 0;
        v___x_1855_ = l_Lean_SourceInfo_fromRef(v_ref_1853_, v___x_1854_);
        v___x_1856_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_mkGrindOnlyTactics_mkTac___redArg___closed__0;
        v___x_1857_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_mkGrindOnlyTactics_mkTac___redArg___closed__1;
        crate::leanh::lean_inc_n(v___x_1855_, 4);
        v___x_1858_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1858_, 0, v___x_1855_);
        crate::leanh::lean_ctor_set(v___x_1858_, 1, v___x_1856_);
        v___x_1859_ = l_Lean_Meta_Grind_mkFinishTactic___closed__3;
        v___x_1860_ = l_Lean_Meta_Grind_mkFinishTactic___closed__5;
        v___x_1861_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1861_, 0, v___x_1855_);
        crate::leanh::lean_ctor_set(v___x_1861_, 1, v___x_1860_);
        v___x_1862_ = l_Lean_Syntax_node1(v___x_1855_, v___x_1859_, v___x_1861_);
        v___x_1863_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkFinishTactic___closed__4),
            core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkFinishTactic___closed__4_once),
            _init_l_Lean_Meta_Grind_mkFinishTactic___closed__4,
        );
        v___x_1864_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1864_, 0, v___x_1855_);
        crate::leanh::lean_ctor_set(v___x_1864_, 1, v___x_1859_);
        crate::leanh::lean_ctor_set(v___x_1864_, 2, v___x_1863_);
        crate::leanh::lean_inc_ref(v___x_1864_);
        v___x_1865_ = l_Lean_Syntax_node5(
            v___x_1855_,
            v___x_1857_,
            v___x_1858_,
            v_cfg_1824_,
            v___x_1862_,
            v___x_1864_,
            v___x_1864_,
        );
        v___x_1866_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1866_, 0, v___x_1865_);
        return v___x_1866_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_mkGrindOnlyTactics_mkTac___redArg___boxed(
    mut v_cfg_1867_: *mut crate::leanh::LeanObject,
    mut v_params_1868_: *mut crate::leanh::LeanObject,
    mut v_a_1869_: *mut crate::leanh::LeanObject,
    mut v_a_1870_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1871_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_mkGrindOnlyTactics_mkTac___redArg(v_cfg_1867_, v_params_1868_, v_a_1869_);
    crate::leanh::lean_dec_ref(v_a_1869_);
    crate::leanh::lean_dec_ref(v_params_1868_);
    return v_res_1871_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_mkGrindOnlyTactics_mkTac(
    mut v_cfg_1872_: *mut crate::leanh::LeanObject,
    mut v_params_1873_: *mut crate::leanh::LeanObject,
    mut v_a_1874_: *mut crate::leanh::LeanObject,
    mut v_a_1875_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1877_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_mkGrindOnlyTactics_mkTac___redArg(v_cfg_1872_, v_params_1873_, v_a_1874_);
    return v___x_1877_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_mkGrindOnlyTactics_mkTac___boxed(
    mut v_cfg_1878_: *mut crate::leanh::LeanObject,
    mut v_params_1879_: *mut crate::leanh::LeanObject,
    mut v_a_1880_: *mut crate::leanh::LeanObject,
    mut v_a_1881_: *mut crate::leanh::LeanObject,
    mut v_a_1882_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1883_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_mkGrindOnlyTactics_mkTac(v_cfg_1878_, v_params_1879_, v_a_1880_, v_a_1881_);
    crate::leanh::lean_dec(v_a_1881_);
    crate::leanh::lean_dec_ref(v_a_1880_);
    crate::leanh::lean_dec_ref(v_params_1879_);
    return v_res_1883_;
}
pub unsafe fn l_Lean_Meta_Grind_mkGrindOnlyTactics(
    mut v_cfg_1884_: *mut crate::leanh::LeanObject,
    mut v_seq_1885_: *mut crate::leanh::LeanObject,
    mut v_extraParams_1886_: *mut crate::leanh::LeanObject,
    mut v_a_1887_: *mut crate::leanh::LeanObject,
    mut v_a_1888_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1894_: u8 = 0;
    let mut v_snd_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: u8 = 0;
    let mut v_fst_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1906_: u8 = 0;
    let mut v___x_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: u8 = 0;
    let mut v___x_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1915_: u8 = 0;
    let mut v___x_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1923_: u8 = 0;
    let mut v___x_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1930_: u8 = 0;
    let mut v___x_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1935_: u8 = 0;
    let mut v_a_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1939_: u8 = 0;
    let mut v___x_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1943_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1890_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_collectParamsCore(v_seq_1885_, v_a_1887_, v_a_1888_);
                if crate::leanh::lean_obj_tag(v___x_1890_) == 0 {
                    v_a_1891_ = crate::leanh::lean_ctor_get(v___x_1890_, 0);
                    v_isSharedCheck_1935_ = (!crate::leanh::lean_is_exclusive(v___x_1890_)) as u8;
                    if v_isSharedCheck_1935_ == 0 {
                        v___x_1893_ = v___x_1890_;
                        v_isShared_1894_ = v_isSharedCheck_1935_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1891_);
                        crate::leanh::lean_dec(v___x_1890_);
                        v___x_1893_ = crate::leanh::lean_box(0);
                        v_isShared_1894_ = v_isSharedCheck_1935_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_cfg_1884_);
                    v_a_1936_ = crate::leanh::lean_ctor_get(v___x_1890_, 0);
                    v_isSharedCheck_1943_ = (!crate::leanh::lean_is_exclusive(v___x_1890_)) as u8;
                    if v_isSharedCheck_1943_ == 0 {
                        v___x_1938_ = v___x_1890_;
                        v_isShared_1939_ = v_isSharedCheck_1943_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1936_);
                        crate::leanh::lean_dec(v___x_1890_);
                        v___x_1938_ = crate::leanh::lean_box(0);
                        v_isShared_1939_ = v_isSharedCheck_1943_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_1895_ = crate::leanh::lean_ctor_get(v_a_1891_, 1);
                crate::leanh::lean_inc(v_snd_1895_);
                v_fst_1896_ = crate::leanh::lean_ctor_get(v_a_1891_, 0);
                crate::leanh::lean_inc(v_fst_1896_);
                crate::leanh::lean_dec(v_a_1891_);
                v___x_1897_ = (crate::leanh::lean_unbox(v_fst_1896_) as u8);
                crate::leanh::lean_dec(v_fst_1896_);
                if v___x_1897_ == 0 {
                    crate::leanh::lean_del_object(v___x_1893_);
                    v_fst_1898_ = crate::leanh::lean_ctor_get(v_snd_1895_, 0);
                    crate::leanh::lean_inc_n(v_fst_1898_, 2);
                    v_snd_1899_ = crate::leanh::lean_ctor_get(v_snd_1895_, 1);
                    crate::leanh::lean_inc(v_snd_1899_);
                    crate::leanh::lean_dec(v_snd_1895_);
                    v___x_1900_ = l_Array_append___redArg(v_fst_1898_, v_snd_1899_);
                    v___x_1901_ = l_Array_append___redArg(v___x_1900_, v_extraParams_1886_);
                    crate::leanh::lean_inc(v_cfg_1884_);
                    v___x_1902_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_mkGrindOnlyTactics_mkTac___redArg(v_cfg_1884_, v___x_1901_, v_a_1887_);
                    crate::leanh::lean_dec_ref(v___x_1901_);
                    v_a_1903_ = crate::leanh::lean_ctor_get(v___x_1902_, 0);
                    v_isSharedCheck_1930_ = (!crate::leanh::lean_is_exclusive(v___x_1902_)) as u8;
                    if v_isSharedCheck_1930_ == 0 {
                        v___x_1905_ = v___x_1902_;
                        v_isShared_1906_ = v_isSharedCheck_1930_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1903_);
                        crate::leanh::lean_dec(v___x_1902_);
                        v___x_1905_ = crate::leanh::lean_box(0);
                        v_isShared_1906_ = v_isSharedCheck_1930_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_snd_1895_);
                    crate::leanh::lean_dec(v_cfg_1884_);
                    v___x_1931_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_collectParamsCore___closed__0;
                    if v_isShared_1894_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1893_, 0, v___x_1931_);
                        v___x_1933_ = v___x_1893_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1934_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1934_, 0, v___x_1931_);
                        v___x_1933_ = v_reuseFailAlloc_1934_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1907_ = lean_array_get_size(v_snd_1899_);
                crate::leanh::lean_dec(v_snd_1899_);
                v___x_1908_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1909_ = lean_nat_dec_eq(v___x_1907_, v___x_1908_);
                if v___x_1909_ == 0 {
                    crate::leanh::lean_del_object(v___x_1905_);
                    v___x_1910_ = l_Array_append___redArg(v_fst_1898_, v_extraParams_1886_);
                    v___x_1911_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_mkGrindOnlyTactics_mkTac___redArg(v_cfg_1884_, v___x_1910_, v_a_1887_);
                    crate::leanh::lean_dec_ref(v___x_1910_);
                    v_a_1912_ = crate::leanh::lean_ctor_get(v___x_1911_, 0);
                    v_isSharedCheck_1923_ = (!crate::leanh::lean_is_exclusive(v___x_1911_)) as u8;
                    if v_isSharedCheck_1923_ == 0 {
                        v___x_1914_ = v___x_1911_;
                        v_isShared_1915_ = v_isSharedCheck_1923_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1912_);
                        crate::leanh::lean_dec(v___x_1911_);
                        v___x_1914_ = crate::leanh::lean_box(0);
                        v_isShared_1915_ = v_isSharedCheck_1923_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_fst_1898_);
                    crate::leanh::lean_dec(v_cfg_1884_);
                    v___x_1924_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1925_ = lean_mk_empty_array_with_capacity(v___x_1924_);
                    v___x_1926_ = lean_array_push(v___x_1925_, v_a_1903_);
                    if v_isShared_1906_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1905_, 0, v___x_1926_);
                        v___x_1928_ = v___x_1905_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1929_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1929_, 0, v___x_1926_);
                        v___x_1928_ = v_reuseFailAlloc_1929_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1916_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_1917_ = lean_mk_empty_array_with_capacity(v___x_1916_);
                v___x_1918_ = lean_array_push(v___x_1917_, v_a_1903_);
                v___x_1919_ = lean_array_push(v___x_1918_, v_a_1912_);
                if v_isShared_1915_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1914_, 0, v___x_1919_);
                    v___x_1921_ = v___x_1914_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1922_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1922_, 0, v___x_1919_);
                    v___x_1921_ = v_reuseFailAlloc_1922_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1921_;
            }
            5 => {
                return v___x_1928_;
            }
            6 => {
                return v___x_1933_;
            }
            7 => {
                if v_isShared_1939_ == 0 {
                    v___x_1941_ = v___x_1938_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1942_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1942_, 0, v_a_1936_);
                    v___x_1941_ = v_reuseFailAlloc_1942_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1941_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_mkGrindOnlyTactics___boxed(
    mut v_cfg_1944_: *mut crate::leanh::LeanObject,
    mut v_seq_1945_: *mut crate::leanh::LeanObject,
    mut v_extraParams_1946_: *mut crate::leanh::LeanObject,
    mut v_a_1947_: *mut crate::leanh::LeanObject,
    mut v_a_1948_: *mut crate::leanh::LeanObject,
    mut v_a_1949_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1950_ = l_Lean_Meta_Grind_mkGrindOnlyTactics(
        v_cfg_1944_,
        v_seq_1945_,
        v_extraParams_1946_,
        v_a_1947_,
        v_a_1948_,
    );
    crate::leanh::lean_dec(v_a_1948_);
    crate::leanh::lean_dec_ref(v_a_1947_);
    crate::leanh::lean_dec_ref(v_extraParams_1946_);
    return v_res_1950_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_CollectParams(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_CollectParams(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_CollectParams(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_CollectParams(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_CollectParams(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_CollectParams(builtin);
}
