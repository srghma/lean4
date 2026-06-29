// Lean compiler output
// Module: Lean.Parser.Term.Doc
// Imports: Lean.Parser.Extension
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fswap, lean_array_get_size,
    lean_array_push, lean_array_size, lean_array_to_list, lean_array_uget_borrowed, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_shiftr, lean_nat_sub,
    lean_string_append, lean_string_utf8_byte_size, lean_string_utf8_extract,
    lean_string_utf8_get_fast, lean_string_utf8_next_fast, lean_uint32_dec_eq, lean_usize_add,
    lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::String::FindPos::l_String_Slice_posLE;
use crate::r#gen::Init::Data::String::Slice::l_String_Slice_toString;
use crate::r#gen::Init::Data::String::Subslice::l_String_Slice_subslice_x21;
use crate::r#gen::Init::Prelude::l_Array_push___boxed;
use crate::r#gen::Lean::Data::Name::{
    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl, l_Lean_Name_quickLt,
};
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg,
};
use crate::r#gen::Lean::Environment::{
    l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg,
    l_Lean_PersistentEnvExtension_addEntry___redArg,
    l_Lean_PersistentEnvExtension_getState___redArg,
    l_Lean_instInhabitedPersistentEnvExtensionState___redArg,
    l_Lean_registerPersistentEnvExtensionUnsafe___redArg,
};
use crate::r#gen::Lean::Parser::Extension::{
    initialize_Lean_Parser_Extension, runtime_initialize_Lean_Parser_Extension,
};
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__3___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__0_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__0_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__0_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__0_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__1_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__1_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__1_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__1_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__2_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__2_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__2_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__2_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__3_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__3_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__3_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__3_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__4_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__4_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__4_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__5_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__5_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__5_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__6_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__6_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__6_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__7_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [68, 111, 99, 0]};
static mut l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__7_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__7_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__8_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 29, m_capacity: 29, m_length: 28, m_data: [114, 101, 99, 111, 109, 109, 101, 110, 100, 101, 100, 83, 112, 101, 108, 108, 105, 110, 103, 66, 121, 78, 97, 109, 101, 69, 120, 116, 0]};
static mut l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__8_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__8_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__9_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__4_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__9_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__9_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__5_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__9_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__9_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__6_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__9_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__9_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__7_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,9734693949192152375 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__9_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__9_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__8_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8358569760598905025 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__9_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__9_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__10_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__4_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 1, m_objs: [((( 1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__10_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__10_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__11_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__5_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 1, m_objs: [((( 1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__11_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__11_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__12_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<8> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*8 + 0) as u16, other: 8, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__9_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__10_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__11_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__0_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__1_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__2_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__12_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__12_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__13_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__12_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__3_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__13_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__13_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Term_Doc_recommendedSpellingByNameExt: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__0_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__0_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__0_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__0_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__1_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__1_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__1_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__1_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__2_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__2_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__2_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__2_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__3_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [114, 101, 99, 111, 109, 109, 101, 110, 100, 101, 100, 83, 112, 101, 108, 108, 105, 110, 103, 69, 120, 116, 0]};
static mut l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__3_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__3_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__4_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__4_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__4_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__4_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__5_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__4_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__4_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__6_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__4_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__4_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__7_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,9734693949192152375 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__4_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__4_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__3_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,12885371681865753169 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__4_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__4_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__5_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__5_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__5_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__6_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__3_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__5_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__6_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__6_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__7_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__4_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__5_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__7_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__7_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__8_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l_Array_push___boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__8_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__8_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__9_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<8> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*8 + 0) as u16, other: 8, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__4_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__6_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__7_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__8_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__1_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__2_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__9_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__9_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__10_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__9_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__0_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__10_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__10_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Term_Doc_recommendedSpellingExt: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Term_Doc_getRecommendedSpellingsForName___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Term_Doc_getRecommendedSpellingsForName___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_indentLine___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [10, 0]};
static mut l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_indentLine___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_indentLine___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_indentLine___closed__1_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [32, 32, 32, 0]};
static mut l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_indentLine___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_indentLine___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__0___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__0_value: crate::leanh::LeanStringObject<33> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [32, 42, 32, 84, 104, 101, 32, 114, 101, 99, 111, 109, 109, 101, 110, 100, 101, 100, 32, 115, 112, 101, 108, 108, 105, 110, 103, 32, 111, 102, 32, 96, 0]};
static mut l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__1_value: crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [96, 32, 105, 110, 32, 105, 100, 101, 110, 116, 105, 102, 105, 101, 114, 115, 32, 105, 115, 32, 96, 0]};
static mut l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__2_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__3_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [46, 10, 10, 0]};
static mut l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__4_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__5_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [32, 40, 0]};
static mut l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__6_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [41, 46, 10, 10, 0]};
static mut l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__7_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__8_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [10, 10, 0]};
static mut l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Term_Doc_getRecommendedSpellingString___closed__0_value:
    crate::leanh::LeanStringObject<46> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 46,
    m_capacity: 46,
    m_length: 45,
    m_data: [
        10, 10, 67, 111, 110, 118, 101, 110, 116, 105, 111, 110, 115, 32, 102, 111, 114, 32, 110,
        111, 116, 97, 116, 105, 111, 110, 115, 32, 105, 110, 32, 105, 100, 101, 110, 116, 105, 102,
        105, 101, 114, 115, 58, 10, 10, 0,
    ],
};
static mut l_Lean_Parser_Term_Doc_getRecommendedSpellingString___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Term_Doc_getRecommendedSpellingString___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__2___redArg(
    mut v_t_721_: *mut crate::leanh::LeanObject,
    mut v_k_722_: *mut crate::leanh::LeanObject,
    mut v_fallback_723_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_728_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_721_) == 0 {
                    v_k_724_ = crate::leanh::lean_ctor_get(v_t_721_, 1);
                    v_v_725_ = crate::leanh::lean_ctor_get(v_t_721_, 2);
                    v_l_726_ = crate::leanh::lean_ctor_get(v_t_721_, 3);
                    v_r_727_ = crate::leanh::lean_ctor_get(v_t_721_, 4);
                    v___x_728_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_722_, v_k_724_);
                    match v___x_728_ {
                        0 => {
                            v_t_721_ = v_l_726_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            crate::leanh::lean_inc(v_v_725_);
                            return v_v_725_;
                        }
                        _ => {
                            v_t_721_ = v_r_727_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_fallback_723_);
                    return v_fallback_723_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__2___redArg___boxed(
    mut v_t_731_: *mut crate::leanh::LeanObject,
    mut v_k_732_: *mut crate::leanh::LeanObject,
    mut v_fallback_733_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_734_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__2___redArg(v_t_731_, v_k_732_, v_fallback_733_);
    crate::leanh::lean_dec(v_fallback_733_);
    crate::leanh::lean_dec(v_k_732_);
    crate::leanh::lean_dec(v_t_731_);
    return v_res_734_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__3(
    mut v_fst_737_: *mut crate::leanh::LeanObject,
    mut v_as_738_: *mut crate::leanh::LeanObject,
    mut v_i_739_: usize,
    mut v_stop_740_: usize,
    mut v_b_741_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_742_: u8 = 0;
    let mut v___x_743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_748_: usize = 0;
    let mut v___x_749_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_742_ = lean_usize_dec_eq(v_i_739_, v_stop_740_);
                if v___x_742_ == 0 {
                    v___x_743_ = lean_array_uget_borrowed(v_as_738_, v_i_739_);
                    v___x_744_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__3___closed__0;
                    v___x_745_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__2___redArg(v_b_741_, v___x_743_, v___x_744_);
                    crate::leanh::lean_inc_ref(v_fst_737_);
                    v___x_746_ = lean_array_push(v___x_745_, v_fst_737_);
                    crate::leanh::lean_inc(v___x_743_);
                    v___x_747_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_743_, v___x_746_, v_b_741_);
                    v___x_748_ = 1usize;
                    v___x_749_ = lean_usize_add(v_i_739_, v___x_748_);
                    v_i_739_ = v___x_749_;
                    v_b_741_ = v___x_747_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_fst_737_);
                    return v_b_741_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__3___boxed(
    mut v_fst_751_: *mut crate::leanh::LeanObject,
    mut v_as_752_: *mut crate::leanh::LeanObject,
    mut v_i_753_: *mut crate::leanh::LeanObject,
    mut v_stop_754_: *mut crate::leanh::LeanObject,
    mut v_b_755_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_756_: usize = 0;
    let mut v_stop_boxed_757_: usize = 0;
    let mut v_res_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_756_ = crate::leanh::lean_unbox_usize(v_i_753_);
    crate::leanh::lean_dec(v_i_753_);
    v_stop_boxed_757_ = crate::leanh::lean_unbox_usize(v_stop_754_);
    crate::leanh::lean_dec(v_stop_754_);
    v_res_758_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__3(v_fst_751_, v_as_752_, v_i_boxed_756_, v_stop_boxed_757_, v_b_755_);
    crate::leanh::lean_dec_ref(v_as_752_);
    return v_res_758_;
}
pub unsafe fn l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__0_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_(
    mut v_es_759_: *mut crate::leanh::LeanObject,
    mut v_x_760_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_765_: u8 = 0;
    v_fst_761_ = crate::leanh::lean_ctor_get(v_x_760_, 0);
    crate::leanh::lean_inc(v_fst_761_);
    v_snd_762_ = crate::leanh::lean_ctor_get(v_x_760_, 1);
    crate::leanh::lean_inc(v_snd_762_);
    crate::leanh::lean_dec_ref(v_x_760_);
    v___x_763_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_764_ = lean_array_get_size(v_snd_762_);
    v___x_765_ = lean_nat_dec_lt(v___x_763_, v___x_764_);
    if v___x_765_ == 0 {
        crate::leanh::lean_dec(v_snd_762_);
        crate::leanh::lean_dec(v_fst_761_);
        return v_es_759_;
    } else {
        let mut v___x_766_: u8 = 0;
        v___x_766_ = lean_nat_dec_le(v___x_764_, v___x_764_);
        if v___x_766_ == 0 {
            if v___x_765_ == 0 {
                crate::leanh::lean_dec(v_snd_762_);
                crate::leanh::lean_dec(v_fst_761_);
                return v_es_759_;
            } else {
                let mut v___x_767_: usize = 0;
                let mut v___x_768_: usize = 0;
                let mut v___x_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_767_ = 0usize;
                v___x_768_ = lean_usize_of_nat(v___x_764_);
                v___x_769_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__3(v_fst_761_, v_snd_762_, v___x_767_, v___x_768_, v_es_759_);
                crate::leanh::lean_dec(v_snd_762_);
                return v___x_769_;
            }
        } else {
            let mut v___x_770_: usize = 0;
            let mut v___x_771_: usize = 0;
            let mut v___x_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_770_ = 0usize;
            v___x_771_ = lean_usize_of_nat(v___x_764_);
            v___x_772_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__3(v_fst_761_, v_snd_762_, v___x_770_, v___x_771_, v_es_759_);
            crate::leanh::lean_dec(v_snd_762_);
            return v___x_772_;
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__0_spec__0(
    mut v_init_773_: *mut crate::leanh::LeanObject,
    mut v_x_774_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_774_) == 0 {
                    v_k_775_ = crate::leanh::lean_ctor_get(v_x_774_, 1);
                    v_v_776_ = crate::leanh::lean_ctor_get(v_x_774_, 2);
                    v_l_777_ = crate::leanh::lean_ctor_get(v_x_774_, 3);
                    v_r_778_ = crate::leanh::lean_ctor_get(v_x_774_, 4);
                    v___x_779_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__0_spec__0(v_init_773_, v_l_777_);
                    crate::leanh::lean_inc(v_v_776_);
                    crate::leanh::lean_inc(v_k_775_);
                    v___x_780_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_780_, 0, v_k_775_);
                    crate::leanh::lean_ctor_set(v___x_780_, 1, v_v_776_);
                    v___x_781_ = lean_array_push(v___x_779_, v___x_780_);
                    v_init_773_ = v___x_781_;
                    v_x_774_ = v_r_778_;
                    state = 0;
                    continue;
                } else {
                    return v_init_773_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_init_783_: *mut crate::leanh::LeanObject,
    mut v_x_784_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_785_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__0_spec__0(v_init_783_, v_x_784_);
    crate::leanh::lean_dec(v_x_784_);
    return v_res_785_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1_spec__2___redArg(
    mut v_hi_786_: *mut crate::leanh::LeanObject,
    mut v_pivot_787_: *mut crate::leanh::LeanObject,
    mut v_as_788_: *mut crate::leanh::LeanObject,
    mut v_i_789_: *mut crate::leanh::LeanObject,
    mut v_k_790_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_791_: u8 = 0;
    let mut v___x_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_797_: u8 = 0;
    let mut v___x_798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_791_ = lean_nat_dec_lt(v_k_790_, v_hi_786_);
                if v___x_791_ == 0 {
                    crate::leanh::lean_dec(v_k_790_);
                    v___x_792_ = lean_array_fswap(v_as_788_, v_i_789_, v_hi_786_);
                    v___x_793_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_793_, 0, v_i_789_);
                    crate::leanh::lean_ctor_set(v___x_793_, 1, v___x_792_);
                    return v___x_793_;
                } else {
                    v___x_794_ = lean_array_fget_borrowed(v_as_788_, v_k_790_);
                    v_fst_795_ = crate::leanh::lean_ctor_get(v___x_794_, 0);
                    v_fst_796_ = crate::leanh::lean_ctor_get(v_pivot_787_, 0);
                    v___x_797_ = l_Lean_Name_quickLt(v_fst_795_, v_fst_796_);
                    if v___x_797_ == 0 {
                        v___x_798_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_799_ = lean_nat_add(v_k_790_, v___x_798_);
                        crate::leanh::lean_dec(v_k_790_);
                        v_k_790_ = v___x_799_;
                        state = 0;
                        continue;
                    } else {
                        v___x_801_ = lean_array_fswap(v_as_788_, v_i_789_, v_k_790_);
                        v___x_802_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_803_ = lean_nat_add(v_i_789_, v___x_802_);
                        crate::leanh::lean_dec(v_i_789_);
                        v___x_804_ = lean_nat_add(v_k_790_, v___x_802_);
                        crate::leanh::lean_dec(v_k_790_);
                        v_as_788_ = v___x_801_;
                        v_i_789_ = v___x_803_;
                        v_k_790_ = v___x_804_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(
    mut v_hi_806_: *mut crate::leanh::LeanObject,
    mut v_pivot_807_: *mut crate::leanh::LeanObject,
    mut v_as_808_: *mut crate::leanh::LeanObject,
    mut v_i_809_: *mut crate::leanh::LeanObject,
    mut v_k_810_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_811_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_806_, v_pivot_807_, v_as_808_, v_i_809_, v_k_810_);
    crate::leanh::lean_dec_ref(v_pivot_807_);
    crate::leanh::lean_dec(v_hi_806_);
    return v_res_811_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1___redArg___lam__0(
    mut v_x1_812_: *mut crate::leanh::LeanObject,
    mut v_x2_813_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_fst_814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_816_: u8 = 0;
    v_fst_814_ = crate::leanh::lean_ctor_get(v_x1_812_, 0);
    v_fst_815_ = crate::leanh::lean_ctor_get(v_x2_813_, 0);
    v___x_816_ = l_Lean_Name_quickLt(v_fst_814_, v_fst_815_);
    return v___x_816_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1___redArg___lam__0___boxed(
    mut v_x1_817_: *mut crate::leanh::LeanObject,
    mut v_x2_818_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_819_: u8 = 0;
    let mut v_r_820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_819_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1___redArg___lam__0(v_x1_817_, v_x2_818_);
    crate::leanh::lean_dec_ref(v_x2_818_);
    crate::leanh::lean_dec_ref(v_x1_817_);
    v_r_820_ = crate::leanh::lean_box((v_res_819_) as usize);
    return v_r_820_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1___redArg(
    mut v_n_821_: *mut crate::leanh::LeanObject,
    mut v_as_822_: *mut crate::leanh::LeanObject,
    mut v_lo_823_: *mut crate::leanh::LeanObject,
    mut v_hi_824_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pivot_827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_831_: u8 = 0;
    let mut v___x_832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_836_: u8 = 0;
    let mut v___x_837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_844_: u8 = 0;
    let mut v___x_845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_850_: u8 = 0;
    let mut v___x_851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_854_: u8 = 0;
    let mut v___x_855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_836_ = lean_nat_dec_lt(v_lo_823_, v_hi_824_);
                if v___x_836_ == 0 {
                    crate::leanh::lean_dec(v_lo_823_);
                    return v_as_822_;
                } else {
                    v___x_837_ = lean_nat_add(v_lo_823_, v_hi_824_);
                    v___x_838_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_mid_839_ = lean_nat_shiftr(v___x_837_, v___x_838_);
                    crate::leanh::lean_dec(v___x_837_);
                    v___x_852_ = lean_array_fget_borrowed(v_as_822_, v_mid_839_);
                    v___x_853_ = lean_array_fget_borrowed(v_as_822_, v_lo_823_);
                    v___x_854_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_852_, v___x_853_);
                    if v___x_854_ == 0 {
                        v___y_847_ = v_as_822_;
                        state = 3;
                        continue;
                    } else {
                        v___x_855_ = lean_array_fswap(v_as_822_, v_lo_823_, v_mid_839_);
                        v___y_847_ = v___x_855_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_pivot_827_ = lean_array_fget(v___y_826_, v_hi_824_);
                crate::leanh::lean_inc_n(v_lo_823_, 2);
                v___x_828_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_824_, v_pivot_827_, v___y_826_, v_lo_823_, v_lo_823_);
                crate::leanh::lean_dec(v_pivot_827_);
                v_fst_829_ = crate::leanh::lean_ctor_get(v___x_828_, 0);
                crate::leanh::lean_inc(v_fst_829_);
                v_snd_830_ = crate::leanh::lean_ctor_get(v___x_828_, 1);
                crate::leanh::lean_inc(v_snd_830_);
                crate::leanh::lean_dec_ref(v___x_828_);
                v___x_831_ = lean_nat_dec_le(v_hi_824_, v_fst_829_);
                if v___x_831_ == 0 {
                    v___x_832_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1___redArg(v_n_821_, v_snd_830_, v_lo_823_, v_fst_829_);
                    v___x_833_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_834_ = lean_nat_add(v_fst_829_, v___x_833_);
                    crate::leanh::lean_dec(v_fst_829_);
                    v_as_822_ = v___x_832_;
                    v_lo_823_ = v___x_834_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_fst_829_);
                    crate::leanh::lean_dec(v_lo_823_);
                    return v_snd_830_;
                }
            }
            2 => {
                v___x_842_ = lean_array_fget_borrowed(v___y_841_, v_mid_839_);
                v___x_843_ = lean_array_fget_borrowed(v___y_841_, v_hi_824_);
                v___x_844_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_842_, v___x_843_);
                if v___x_844_ == 0 {
                    crate::leanh::lean_dec(v_mid_839_);
                    v___y_826_ = v___y_841_;
                    state = 1;
                    continue;
                } else {
                    v___x_845_ = lean_array_fswap(v___y_841_, v_mid_839_, v_hi_824_);
                    crate::leanh::lean_dec(v_mid_839_);
                    v___y_826_ = v___x_845_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_848_ = lean_array_fget_borrowed(v___y_847_, v_hi_824_);
                v___x_849_ = lean_array_fget_borrowed(v___y_847_, v_lo_823_);
                v___x_850_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_848_, v___x_849_);
                if v___x_850_ == 0 {
                    v___y_841_ = v___y_847_;
                    state = 2;
                    continue;
                } else {
                    v___x_851_ = lean_array_fswap(v___y_847_, v_lo_823_, v_hi_824_);
                    v___y_841_ = v___x_851_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1___redArg___boxed(
    mut v_n_856_: *mut crate::leanh::LeanObject,
    mut v_as_857_: *mut crate::leanh::LeanObject,
    mut v_lo_858_: *mut crate::leanh::LeanObject,
    mut v_hi_859_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_860_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1___redArg(v_n_856_, v_as_857_, v_lo_858_, v_hi_859_);
    crate::leanh::lean_dec(v_hi_859_);
    crate::leanh::lean_dec(v_n_856_);
    return v_res_860_;
}
pub unsafe fn l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__1_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_(
    mut v_x_863_: *mut crate::leanh::LeanObject,
    mut v_s_864_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_874_: u8 = 0;
    let mut v___x_875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_879_: u8 = 0;
    let mut v___x_880_: u8 = 0;
    let mut v___x_881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_865_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_866_ = l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_;
                v___x_867_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__0_spec__0(v___x_866_, v_s_864_);
                v___x_868_ = lean_array_get_size(v___x_867_);
                v___x_874_ = lean_nat_dec_eq(v___x_868_, v___x_865_);
                if v___x_874_ == 0 {
                    v___x_875_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_876_ = lean_nat_sub(v___x_868_, v___x_875_);
                    v___x_880_ = lean_nat_dec_le(v___x_865_, v___x_876_);
                    if v___x_880_ == 0 {
                        crate::leanh::lean_inc(v___x_876_);
                        v___y_878_ = v___x_876_;
                        state = 2;
                        continue;
                    } else {
                        v___y_878_ = v___x_865_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref_n(v___x_867_, 2);
                    v___x_881_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_881_, 0, v___x_867_);
                    crate::leanh::lean_ctor_set(v___x_881_, 1, v___x_867_);
                    crate::leanh::lean_ctor_set(v___x_881_, 2, v___x_867_);
                    return v___x_881_;
                }
            }
            1 => {
                v___x_872_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1___redArg(v___x_868_, v___x_867_, v___y_870_, v___y_871_);
                crate::leanh::lean_dec(v___y_871_);
                crate::leanh::lean_inc_ref_n(v___x_872_, 2);
                v___x_873_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_873_, 0, v___x_872_);
                crate::leanh::lean_ctor_set(v___x_873_, 1, v___x_872_);
                crate::leanh::lean_ctor_set(v___x_873_, 2, v___x_872_);
                return v___x_873_;
            }
            2 => {
                v___x_879_ = lean_nat_dec_le(v___y_878_, v___x_876_);
                if v___x_879_ == 0 {
                    crate::leanh::lean_dec(v___x_876_);
                    crate::leanh::lean_inc(v___y_878_);
                    v___y_870_ = v___y_878_;
                    v___y_871_ = v___y_878_;
                    state = 1;
                    continue;
                } else {
                    v___y_870_ = v___y_878_;
                    v___y_871_ = v___x_876_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__1_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2____boxed(
    mut v_x_882_: *mut crate::leanh::LeanObject,
    mut v_s_883_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_884_ = l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__1_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_(v_x_882_, v_s_883_);
    crate::leanh::lean_dec(v_s_883_);
    crate::leanh::lean_dec_ref(v_x_882_);
    return v_res_884_;
}
pub unsafe fn l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__2_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_(
    mut v_x_885_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_886_ = crate::leanh::lean_box(0);
    return v___x_886_;
}
pub unsafe fn l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__2_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2____boxed(
    mut v_x_887_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_888_ = l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__2_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_(v_x_887_);
    crate::leanh::lean_dec(v_x_887_);
    return v_res_888_;
}
pub unsafe fn l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__3_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_(
    mut v_es_889_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_894_: u8 = 0;
    let mut v___x_895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_899_: u8 = 0;
    let mut v___x_900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_902_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_890_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_891_ = l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_;
                v___x_892_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__0_spec__0(v___x_891_, v_es_889_);
                v___x_893_ = lean_array_get_size(v___x_892_);
                v___x_894_ = lean_nat_dec_eq(v___x_893_, v___x_890_);
                if v___x_894_ == 0 {
                    v___x_895_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_896_ = lean_nat_sub(v___x_893_, v___x_895_);
                    v___x_902_ = lean_nat_dec_le(v___x_890_, v___x_896_);
                    if v___x_902_ == 0 {
                        crate::leanh::lean_inc(v___x_896_);
                        v___y_898_ = v___x_896_;
                        state = 1;
                        continue;
                    } else {
                        v___y_898_ = v___x_890_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_892_;
                }
            }
            1 => {
                v___x_899_ = lean_nat_dec_le(v___y_898_, v___x_896_);
                if v___x_899_ == 0 {
                    crate::leanh::lean_dec(v___x_896_);
                    crate::leanh::lean_inc(v___y_898_);
                    v___x_900_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1___redArg(v___x_893_, v___x_892_, v___y_898_, v___y_898_);
                    crate::leanh::lean_dec(v___y_898_);
                    return v___x_900_;
                } else {
                    v___x_901_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1___redArg(v___x_893_, v___x_892_, v___y_898_, v___x_896_);
                    crate::leanh::lean_dec(v___x_896_);
                    return v___x_901_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__3_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2____boxed(
    mut v_es_903_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_904_ = l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__3_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_(v_es_903_);
    crate::leanh::lean_dec(v_es_903_);
    return v_res_904_;
}
pub unsafe fn l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__4_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_(
    mut v___x_905_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_907_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_907_, 0, v___x_905_);
    return v___x_907_;
}
pub unsafe fn l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__4_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2____boxed(
    mut v___x_908_: *mut crate::leanh::LeanObject,
    mut v___y_909_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_910_ = l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__4_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_(v___x_908_);
    return v_res_910_;
}
pub unsafe fn l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__5_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_(
    mut v___x_911_: *mut crate::leanh::LeanObject,
    mut v_x_912_: *mut crate::leanh::LeanObject,
    mut v___y_913_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_915_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_915_, 0, v___x_911_);
    return v___x_915_;
}
pub unsafe fn l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__5_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2____boxed(
    mut v___x_916_: *mut crate::leanh::LeanObject,
    mut v_x_917_: *mut crate::leanh::LeanObject,
    mut v___y_918_: *mut crate::leanh::LeanObject,
    mut v___y_919_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_920_ = l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__5_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_(v___x_916_, v_x_917_, v___y_918_);
    crate::leanh::lean_dec_ref(v___y_918_);
    crate::leanh::lean_dec_ref(v_x_917_);
    return v_res_920_;
}
pub unsafe fn l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_953_ = l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__13_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_;
    v___x_954_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_953_);
    return v___x_954_;
}
pub unsafe fn l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2____boxed(
    mut v_a_955_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_956_ = l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_();
    return v_res_956_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__0(
    mut v_init_957_: *mut crate::leanh::LeanObject,
    mut v_t_958_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_959_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__0_spec__0(v_init_957_, v_t_958_);
    return v___x_959_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__0___boxed(
    mut v_init_960_: *mut crate::leanh::LeanObject,
    mut v_t_961_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_962_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__0(v_init_960_, v_t_961_);
    crate::leanh::lean_dec(v_t_961_);
    return v_res_962_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1(
    mut v_n_963_: *mut crate::leanh::LeanObject,
    mut v_as_964_: *mut crate::leanh::LeanObject,
    mut v_lo_965_: *mut crate::leanh::LeanObject,
    mut v_hi_966_: *mut crate::leanh::LeanObject,
    mut v_w_967_: *mut crate::leanh::LeanObject,
    mut v_hlo_968_: *mut crate::leanh::LeanObject,
    mut v_hhi_969_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_970_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1___redArg(v_n_963_, v_as_964_, v_lo_965_, v_hi_966_);
    return v___x_970_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1___boxed(
    mut v_n_971_: *mut crate::leanh::LeanObject,
    mut v_as_972_: *mut crate::leanh::LeanObject,
    mut v_lo_973_: *mut crate::leanh::LeanObject,
    mut v_hi_974_: *mut crate::leanh::LeanObject,
    mut v_w_975_: *mut crate::leanh::LeanObject,
    mut v_hlo_976_: *mut crate::leanh::LeanObject,
    mut v_hhi_977_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_978_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1(v_n_971_, v_as_972_, v_lo_973_, v_hi_974_, v_w_975_, v_hlo_976_, v_hhi_977_);
    crate::leanh::lean_dec(v_hi_974_);
    crate::leanh::lean_dec(v_n_971_);
    return v_res_978_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__2(
    mut v_00_u03b4_979_: *mut crate::leanh::LeanObject,
    mut v_t_980_: *mut crate::leanh::LeanObject,
    mut v_k_981_: *mut crate::leanh::LeanObject,
    mut v_fallback_982_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_983_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__2___redArg(v_t_980_, v_k_981_, v_fallback_982_);
    return v___x_983_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__2___boxed(
    mut v_00_u03b4_984_: *mut crate::leanh::LeanObject,
    mut v_t_985_: *mut crate::leanh::LeanObject,
    mut v_k_986_: *mut crate::leanh::LeanObject,
    mut v_fallback_987_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_988_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__2(v_00_u03b4_984_, v_t_985_, v_k_986_, v_fallback_987_);
    crate::leanh::lean_dec(v_fallback_987_);
    crate::leanh::lean_dec(v_k_986_);
    crate::leanh::lean_dec(v_t_985_);
    return v_res_988_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1_spec__2(
    mut v_n_989_: *mut crate::leanh::LeanObject,
    mut v_lo_990_: *mut crate::leanh::LeanObject,
    mut v_hi_991_: *mut crate::leanh::LeanObject,
    mut v_hhi_992_: *mut crate::leanh::LeanObject,
    mut v_pivot_993_: *mut crate::leanh::LeanObject,
    mut v_as_994_: *mut crate::leanh::LeanObject,
    mut v_i_995_: *mut crate::leanh::LeanObject,
    mut v_k_996_: *mut crate::leanh::LeanObject,
    mut v_ilo_997_: *mut crate::leanh::LeanObject,
    mut v_ik_998_: *mut crate::leanh::LeanObject,
    mut v_w_999_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1000_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_991_, v_pivot_993_, v_as_994_, v_i_995_, v_k_996_);
    return v___x_1000_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1_spec__2___boxed(
    mut v_n_1001_: *mut crate::leanh::LeanObject,
    mut v_lo_1002_: *mut crate::leanh::LeanObject,
    mut v_hi_1003_: *mut crate::leanh::LeanObject,
    mut v_hhi_1004_: *mut crate::leanh::LeanObject,
    mut v_pivot_1005_: *mut crate::leanh::LeanObject,
    mut v_as_1006_: *mut crate::leanh::LeanObject,
    mut v_i_1007_: *mut crate::leanh::LeanObject,
    mut v_k_1008_: *mut crate::leanh::LeanObject,
    mut v_ilo_1009_: *mut crate::leanh::LeanObject,
    mut v_ik_1010_: *mut crate::leanh::LeanObject,
    mut v_w_1011_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1012_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1_spec__2(v_n_1001_, v_lo_1002_, v_hi_1003_, v_hhi_1004_, v_pivot_1005_, v_as_1006_, v_i_1007_, v_k_1008_, v_ilo_1009_, v_ik_1010_, v_w_1011_);
    crate::leanh::lean_dec_ref(v_pivot_1005_);
    crate::leanh::lean_dec(v_hi_1003_);
    crate::leanh::lean_dec(v_lo_1002_);
    crate::leanh::lean_dec(v_n_1001_);
    return v_res_1012_;
}
pub unsafe fn l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__0_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_(
    mut v___y_1013_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v___y_1013_);
    return v___y_1013_;
}
pub unsafe fn l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__0_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2____boxed(
    mut v___y_1014_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1015_ = l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__0_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_(v___y_1014_);
    crate::leanh::lean_dec_ref(v___y_1014_);
    return v_res_1015_;
}
pub unsafe fn l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__1_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_(
    mut v_x_1016_: *mut crate::leanh::LeanObject,
    mut v_s_1017_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref_n(v_s_1017_, 2);
    v___x_1018_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1018_, 0, v_s_1017_);
    crate::leanh::lean_ctor_set(v___x_1018_, 1, v_s_1017_);
    crate::leanh::lean_ctor_set(v___x_1018_, 2, v_s_1017_);
    return v___x_1018_;
}
pub unsafe fn l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__1_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2____boxed(
    mut v_x_1019_: *mut crate::leanh::LeanObject,
    mut v_s_1020_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1021_ = l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__1_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_(v_x_1019_, v_s_1020_);
    crate::leanh::lean_dec_ref(v_x_1019_);
    return v_res_1021_;
}
pub unsafe fn l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__2_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_(
    mut v_x_1022_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1023_ = crate::leanh::lean_box(0);
    return v___x_1023_;
}
pub unsafe fn l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__2_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2____boxed(
    mut v_x_1024_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1025_ = l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__2_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_(v_x_1024_);
    crate::leanh::lean_dec_ref(v_x_1024_);
    return v_res_1025_;
}
pub unsafe fn l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__3_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_(
    mut v___x_1026_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1028_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1028_, 0, v___x_1026_);
    return v___x_1028_;
}
pub unsafe fn l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__3_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2____boxed(
    mut v___x_1029_: *mut crate::leanh::LeanObject,
    mut v___y_1030_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1031_ = l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__3_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_(v___x_1029_);
    return v_res_1031_;
}
pub unsafe fn l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__4_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_(
    mut v___x_1032_: *mut crate::leanh::LeanObject,
    mut v_x_1033_: *mut crate::leanh::LeanObject,
    mut v___y_1034_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1036_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1036_, 0, v___x_1032_);
    return v___x_1036_;
}
pub unsafe fn l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__4_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2____boxed(
    mut v___x_1037_: *mut crate::leanh::LeanObject,
    mut v_x_1038_: *mut crate::leanh::LeanObject,
    mut v___y_1039_: *mut crate::leanh::LeanObject,
    mut v___y_1040_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1041_ = l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__4_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_(v___x_1037_, v_x_1038_, v___y_1039_);
    crate::leanh::lean_dec_ref(v___y_1039_);
    crate::leanh::lean_dec_ref(v_x_1038_);
    return v_res_1041_;
}
pub unsafe fn l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1072_ = l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__10_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_;
    v___x_1073_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_1072_);
    return v___x_1073_;
}
pub unsafe fn l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2____boxed(
    mut v_a_1074_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1075_ = l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_();
    return v_res_1075_;
}
pub unsafe fn l_Lean_Parser_Term_Doc_addRecommendedSpelling(
    mut v_env_1076_: *mut crate::leanh::LeanObject,
    mut v_rec_1077_: *mut crate::leanh::LeanObject,
    mut v_names_1078_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_1083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_1084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1079_ = l_Lean_Parser_Term_Doc_recommendedSpellingExt;
    v_toEnvExtension_1080_ = crate::leanh::lean_ctor_get(v___x_1079_, 0);
    v_asyncMode_1081_ = crate::leanh::lean_ctor_get(v_toEnvExtension_1080_, 2);
    v___x_1082_ = l_Lean_Parser_Term_Doc_recommendedSpellingByNameExt;
    v_toEnvExtension_1083_ = crate::leanh::lean_ctor_get(v___x_1082_, 0);
    v_asyncMode_1084_ = crate::leanh::lean_ctor_get(v_toEnvExtension_1083_, 2);
    v___x_1085_ = crate::leanh::lean_box(0);
    crate::leanh::lean_inc_ref(v_rec_1077_);
    v_env_1086_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
        v___x_1079_,
        v_env_1076_,
        v_rec_1077_,
        v_asyncMode_1081_,
        v___x_1085_,
    );
    v___x_1087_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1087_, 0, v_rec_1077_);
    crate::leanh::lean_ctor_set(v___x_1087_, 1, v_names_1078_);
    v___x_1088_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
        v___x_1082_,
        v_env_1086_,
        v___x_1087_,
        v_asyncMode_1084_,
        v___x_1085_,
    );
    return v___x_1088_;
}
pub unsafe fn l_Array_binSearchAux___at___00Lean_Parser_Term_Doc_getRecommendedSpellingsForName_spec__0___redArg(
    mut v_as_1089_: *mut crate::leanh::LeanObject,
    mut v_k_1090_: *mut crate::leanh::LeanObject,
    mut v_x_1091_: *mut crate::leanh::LeanObject,
    mut v_x_1092_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: u8 = 0;
    let mut v___x_1098_: u8 = 0;
    let mut v___x_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: u8 = 0;
    let mut v___x_1102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1103_: u8 = 0;
    let mut v___x_1105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1108_: u8 = 0;
    let mut v___x_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1093_ = lean_nat_add(v_x_1091_, v_x_1092_);
                v___x_1094_ = crate::leanh::lean_unsigned_to_nat(1);
                v_m_1095_ = lean_nat_shiftr(v___x_1093_, v___x_1094_);
                crate::leanh::lean_dec(v___x_1093_);
                v_a_1096_ = lean_array_fget_borrowed(v_as_1089_, v_m_1095_);
                v___x_1097_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1___redArg___lam__0(v_a_1096_, v_k_1090_);
                if v___x_1097_ == 0 {
                    crate::leanh::lean_dec(v_x_1092_);
                    v___x_1098_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1___redArg___lam__0(v_k_1090_, v_a_1096_);
                    if v___x_1098_ == 0 {
                        crate::leanh::lean_dec(v_m_1095_);
                        crate::leanh::lean_dec(v_x_1091_);
                        crate::leanh::lean_inc(v_a_1096_);
                        v___x_1099_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1099_, 0, v_a_1096_);
                        return v___x_1099_;
                    } else {
                        v___x_1100_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_1101_ = lean_nat_dec_eq(v_m_1095_, v___x_1100_);
                        if v___x_1101_ == 0 {
                            v___x_1102_ = lean_nat_sub(v_m_1095_, v___x_1094_);
                            crate::leanh::lean_dec(v_m_1095_);
                            v___x_1103_ = lean_nat_dec_lt(v___x_1102_, v_x_1091_);
                            if v___x_1103_ == 0 {
                                v_x_1092_ = v___x_1102_;
                                state = 0;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_1102_);
                                crate::leanh::lean_dec(v_x_1091_);
                                v___x_1105_ = crate::leanh::lean_box(0);
                                return v___x_1105_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_m_1095_);
                            crate::leanh::lean_dec(v_x_1091_);
                            v___x_1106_ = crate::leanh::lean_box(0);
                            return v___x_1106_;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_x_1091_);
                    v___x_1107_ = lean_nat_add(v_m_1095_, v___x_1094_);
                    crate::leanh::lean_dec(v_m_1095_);
                    v___x_1108_ = lean_nat_dec_le(v___x_1107_, v_x_1092_);
                    if v___x_1108_ == 0 {
                        crate::leanh::lean_dec(v___x_1107_);
                        crate::leanh::lean_dec(v_x_1092_);
                        v___x_1109_ = crate::leanh::lean_box(0);
                        return v___x_1109_;
                    } else {
                        v_x_1091_ = v___x_1107_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_binSearchAux___at___00Lean_Parser_Term_Doc_getRecommendedSpellingsForName_spec__0___redArg___boxed(
    mut v_as_1111_: *mut crate::leanh::LeanObject,
    mut v_k_1112_: *mut crate::leanh::LeanObject,
    mut v_x_1113_: *mut crate::leanh::LeanObject,
    mut v_x_1114_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1115_ = l_Array_binSearchAux___at___00Lean_Parser_Term_Doc_getRecommendedSpellingsForName_spec__0___redArg(v_as_1111_, v_k_1112_, v_x_1113_, v_x_1114_);
    crate::leanh::lean_dec_ref(v_k_1112_);
    crate::leanh::lean_dec_ref(v_as_1111_);
    return v_res_1115_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Term_Doc_getRecommendedSpellingsForName_spec__1(
    mut v_declName_1116_: *mut crate::leanh::LeanObject,
    mut v_as_1117_: *mut crate::leanh::LeanObject,
    mut v_sz_1118_: usize,
    mut v_i_1119_: usize,
    mut v_b_1120_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: usize = 0;
    let mut v___x_1124_: usize = 0;
    let mut v___x_1126_: u8 = 0;
    let mut v___x_1127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1130_: u8 = 0;
    let mut v___x_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: u8 = 0;
    let mut v_spellings_1134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1126_ = lean_usize_dec_lt(v_i_1119_, v_sz_1118_);
                if v___x_1126_ == 0 {
                    crate::leanh::lean_dec(v_declName_1116_);
                    return v_b_1120_;
                } else {
                    v___x_1127_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_a_1128_ = lean_array_uget_borrowed(v_as_1117_, v_i_1119_);
                    v___x_1129_ = lean_array_get_size(v_a_1128_);
                    v___x_1130_ = lean_nat_dec_lt(v___x_1127_, v___x_1129_);
                    if v___x_1130_ == 0 {
                        v_a_1122_ = v_b_1120_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1131_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1132_ = lean_nat_sub(v___x_1129_, v___x_1131_);
                        v___x_1133_ = lean_nat_dec_le(v___x_1127_, v___x_1132_);
                        if v___x_1133_ == 0 {
                            crate::leanh::lean_dec(v___x_1132_);
                            v_a_1122_ = v_b_1120_;
                            state = 1;
                            continue;
                        } else {
                            v_spellings_1134_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__3___closed__0;
                            crate::leanh::lean_inc(v_declName_1116_);
                            v___x_1135_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1135_, 0, v_declName_1116_);
                            crate::leanh::lean_ctor_set(v___x_1135_, 1, v_spellings_1134_);
                            v___x_1136_ = l_Array_binSearchAux___at___00Lean_Parser_Term_Doc_getRecommendedSpellingsForName_spec__0___redArg(v_a_1128_, v___x_1135_, v___x_1127_, v___x_1132_);
                            crate::leanh::lean_dec_ref_known(v___x_1135_, 2);
                            if crate::leanh::lean_obj_tag(v___x_1136_) == 1 {
                                v_val_1137_ = crate::leanh::lean_ctor_get(v___x_1136_, 0);
                                crate::leanh::lean_inc(v_val_1137_);
                                crate::leanh::lean_dec_ref_known(v___x_1136_, 1);
                                v_snd_1138_ = crate::leanh::lean_ctor_get(v_val_1137_, 1);
                                crate::leanh::lean_inc(v_snd_1138_);
                                crate::leanh::lean_dec(v_val_1137_);
                                v___x_1139_ = l_Array_append___redArg(v_b_1120_, v_snd_1138_);
                                crate::leanh::lean_dec(v_snd_1138_);
                                v_a_1122_ = v___x_1139_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_1136_);
                                v_a_1122_ = v_b_1120_;
                                state = 1;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_1123_ = 1usize;
                v___x_1124_ = lean_usize_add(v_i_1119_, v___x_1123_);
                v_i_1119_ = v___x_1124_;
                v_b_1120_ = v_a_1122_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Term_Doc_getRecommendedSpellingsForName_spec__1___boxed(
    mut v_declName_1140_: *mut crate::leanh::LeanObject,
    mut v_as_1141_: *mut crate::leanh::LeanObject,
    mut v_sz_1142_: *mut crate::leanh::LeanObject,
    mut v_i_1143_: *mut crate::leanh::LeanObject,
    mut v_b_1144_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1145_: usize = 0;
    let mut v_i_boxed_1146_: usize = 0;
    let mut v_res_1147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1145_ = crate::leanh::lean_unbox_usize(v_sz_1142_);
    crate::leanh::lean_dec(v_sz_1142_);
    v_i_boxed_1146_ = crate::leanh::lean_unbox_usize(v_i_1143_);
    crate::leanh::lean_dec(v_i_1143_);
    v_res_1147_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Term_Doc_getRecommendedSpellingsForName_spec__1(v_declName_1140_, v_as_1141_, v_sz_boxed_1145_, v_i_boxed_1146_, v_b_1144_);
    crate::leanh::lean_dec_ref(v_as_1141_);
    return v_res_1147_;
}
pub unsafe fn _init_l_Lean_Parser_Term_Doc_getRecommendedSpellingsForName___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1148_ = crate::leanh::lean_box(1);
    v___x_1149_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_1148_);
    return v___x_1149_;
}
pub unsafe fn l_Lean_Parser_Term_Doc_getRecommendedSpellingsForName(
    mut v_env_1150_: *mut crate::leanh::LeanObject,
    mut v_declName_1151_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_importedEntries_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_spellings_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1161_: usize = 0;
    let mut v___x_1162_: usize = 0;
    let mut v___x_1163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1152_ = l_Lean_Parser_Term_Doc_recommendedSpellingByNameExt;
    v_toEnvExtension_1153_ = crate::leanh::lean_ctor_get(v___x_1152_, 0);
    v_asyncMode_1154_ = crate::leanh::lean_ctor_get(v_toEnvExtension_1153_, 2);
    v___x_1155_ = crate::leanh::lean_box(1);
    v___x_1156_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Term_Doc_getRecommendedSpellingsForName___closed__0),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_Term_Doc_getRecommendedSpellingsForName___closed__0_once
        ),
        _init_l_Lean_Parser_Term_Doc_getRecommendedSpellingsForName___closed__0,
    );
    v___x_1157_ = crate::leanh::lean_box(0);
    crate::leanh::lean_inc_ref(v_env_1150_);
    v___x_1158_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(
        v___x_1156_,
        v_toEnvExtension_1153_,
        v_env_1150_,
        v_asyncMode_1154_,
        v___x_1157_,
    );
    v_importedEntries_1159_ = crate::leanh::lean_ctor_get(v___x_1158_, 0);
    crate::leanh::lean_inc_ref(v_importedEntries_1159_);
    crate::leanh::lean_dec(v___x_1158_);
    v_spellings_1160_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__3___closed__0;
    v_sz_1161_ = lean_array_size(v_importedEntries_1159_);
    v___x_1162_ = 0usize;
    crate::leanh::lean_inc(v_declName_1151_);
    v___x_1163_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Term_Doc_getRecommendedSpellingsForName_spec__1(v_declName_1151_, v_importedEntries_1159_, v_sz_1161_, v___x_1162_, v_spellings_1160_);
    crate::leanh::lean_dec_ref(v_importedEntries_1159_);
    v___x_1164_ = l_Lean_PersistentEnvExtension_getState___redArg(
        v___x_1155_,
        v___x_1152_,
        v_env_1150_,
        v_asyncMode_1154_,
        v___x_1157_,
    );
    v___x_1165_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v___x_1164_,
            v_declName_1151_,
        );
    crate::leanh::lean_dec(v_declName_1151_);
    crate::leanh::lean_dec(v___x_1164_);
    if crate::leanh::lean_obj_tag(v___x_1165_) == 1 {
        let mut v_val_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1166_ = crate::leanh::lean_ctor_get(v___x_1165_, 0);
        crate::leanh::lean_inc(v_val_1166_);
        crate::leanh::lean_dec_ref_known(v___x_1165_, 1);
        v___x_1167_ = l_Array_append___redArg(v___x_1163_, v_val_1166_);
        crate::leanh::lean_dec(v_val_1166_);
        return v___x_1167_;
    } else {
        crate::leanh::lean_dec(v___x_1165_);
        return v___x_1163_;
    }
}
pub unsafe fn l_Array_binSearchAux___at___00Lean_Parser_Term_Doc_getRecommendedSpellingsForName_spec__0(
    mut v_as_1168_: *mut crate::leanh::LeanObject,
    mut v_k_1169_: *mut crate::leanh::LeanObject,
    mut v_x_1170_: *mut crate::leanh::LeanObject,
    mut v_x_1171_: *mut crate::leanh::LeanObject,
    mut v_x_1172_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1173_ = l_Array_binSearchAux___at___00Lean_Parser_Term_Doc_getRecommendedSpellingsForName_spec__0___redArg(v_as_1168_, v_k_1169_, v_x_1170_, v_x_1171_);
    return v___x_1173_;
}
pub unsafe fn l_Array_binSearchAux___at___00Lean_Parser_Term_Doc_getRecommendedSpellingsForName_spec__0___boxed(
    mut v_as_1174_: *mut crate::leanh::LeanObject,
    mut v_k_1175_: *mut crate::leanh::LeanObject,
    mut v_x_1176_: *mut crate::leanh::LeanObject,
    mut v_x_1177_: *mut crate::leanh::LeanObject,
    mut v_x_1178_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1179_ =
        l_Array_binSearchAux___at___00Lean_Parser_Term_Doc_getRecommendedSpellingsForName_spec__0(
            v_as_1174_, v_k_1175_, v_x_1176_, v_x_1177_, v_x_1178_,
        );
    crate::leanh::lean_dec_ref(v_k_1175_);
    crate::leanh::lean_dec_ref(v_as_1174_);
    return v_res_1179_;
}
pub unsafe fn l_String_Slice_Pos_skipWhile___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_indentLine_spec__0(
    mut v_s_1180_: *mut crate::leanh::LeanObject,
    mut v_pos_1181_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: u8 = 0;
    let mut v___y_1193_: u8 = 0;
    let mut v___x_1194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1196_: u8 = 0;
    let mut v___x_1197_: u32 = 0;
    let mut v___y_1199_: u8 = 0;
    let mut v___x_1200_: u32 = 0;
    let mut v___x_1201_: u8 = 0;
    let mut v___x_1202_: u32 = 0;
    let mut v___x_1203_: u8 = 0;
    let mut v___x_1204_: u32 = 0;
    let mut v___x_1205_: u8 = 0;
    let mut v___x_1206_: u32 = 0;
    let mut v___x_1207_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_1182_ = crate::leanh::lean_ctor_get(v_s_1180_, 0);
                v_startInclusive_1183_ = crate::leanh::lean_ctor_get(v_s_1180_, 1);
                v_endExclusive_1184_ = crate::leanh::lean_ctor_get(v_s_1180_, 2);
                v___x_1185_ = lean_nat_add(v_startInclusive_1183_, v_pos_1181_);
                v___x_1194_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1195_ = lean_nat_sub(v_endExclusive_1184_, v___x_1185_);
                v___x_1196_ = lean_nat_dec_eq(v___x_1194_, v___x_1195_);
                crate::leanh::lean_dec(v___x_1195_);
                if v___x_1196_ == 0 {
                    v___x_1197_ = lean_string_utf8_get_fast(v_str_1182_, v___x_1185_);
                    v___x_1204_ = 32;
                    v___x_1205_ = lean_uint32_dec_eq(v___x_1197_, v___x_1204_);
                    if v___x_1205_ == 0 {
                        v___x_1206_ = 9;
                        v___x_1207_ = lean_uint32_dec_eq(v___x_1197_, v___x_1206_);
                        v___y_1199_ = v___x_1207_;
                        state = 3;
                        continue;
                    } else {
                        v___y_1199_ = v___x_1205_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1185_);
                    return v_pos_1181_;
                }
            }
            1 => {
                v___x_1187_ = lean_string_utf8_next_fast(v_str_1182_, v___x_1185_);
                v___x_1188_ = lean_nat_sub(v___x_1187_, v___x_1185_);
                crate::leanh::lean_dec(v___x_1185_);
                v___x_1189_ = lean_nat_add(v_pos_1181_, v___x_1188_);
                crate::leanh::lean_dec(v___x_1188_);
                v___x_1190_ = lean_nat_dec_lt(v_pos_1181_, v___x_1189_);
                if v___x_1190_ == 0 {
                    crate::leanh::lean_dec(v___x_1189_);
                    return v_pos_1181_;
                } else {
                    crate::leanh::lean_dec(v_pos_1181_);
                    v_pos_1181_ = v___x_1189_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                if v___y_1193_ == 0 {
                    crate::leanh::lean_dec(v___x_1185_);
                    return v_pos_1181_;
                } else {
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v___y_1199_ == 0 {
                    v___x_1200_ = 13;
                    v___x_1201_ = lean_uint32_dec_eq(v___x_1197_, v___x_1200_);
                    if v___x_1201_ == 0 {
                        v___x_1202_ = 10;
                        v___x_1203_ = lean_uint32_dec_eq(v___x_1197_, v___x_1202_);
                        v___y_1193_ = v___x_1203_;
                        state = 2;
                        continue;
                    } else {
                        v___y_1193_ = v___x_1201_;
                        state = 2;
                        continue;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_Pos_skipWhile___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_indentLine_spec__0___boxed(
    mut v_s_1208_: *mut crate::leanh::LeanObject,
    mut v_pos_1209_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1210_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_indentLine_spec__0(v_s_1208_, v_pos_1209_);
    crate::leanh::lean_dec_ref(v_s_1208_);
    return v_res_1210_;
}
pub unsafe fn l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_indentLine(
    mut v_str_1213_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: u8 = 0;
    let mut v___x_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1218_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1219_ = lean_string_utf8_byte_size(v_str_1213_);
                crate::leanh::lean_inc_ref(v_str_1213_);
                v___x_1220_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1220_, 0, v_str_1213_);
                crate::leanh::lean_ctor_set(v___x_1220_, 1, v___x_1218_);
                crate::leanh::lean_ctor_set(v___x_1220_, 2, v___x_1219_);
                v___x_1221_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_indentLine_spec__0(v___x_1220_, v___x_1218_);
                crate::leanh::lean_dec_ref_known(v___x_1220_, 3);
                v___x_1222_ = lean_nat_dec_eq(v___x_1221_, v___x_1219_);
                crate::leanh::lean_dec(v___x_1221_);
                if v___x_1222_ == 0 {
                    v___x_1223_ = l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_indentLine___closed__1;
                    v___x_1224_ = lean_string_append(v___x_1223_, v_str_1213_);
                    crate::leanh::lean_dec_ref(v_str_1213_);
                    v___y_1215_ = v___x_1224_;
                    state = 1;
                    continue;
                } else {
                    v___y_1215_ = v_str_1213_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1216_ = l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_indentLine___closed__0;
                v___x_1217_ = lean_string_append(v___y_1215_, v___x_1216_);
                return v___x_1217_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__0(
    mut v_s_1227_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1228_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__0___closed__0;
    return v___x_1228_;
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__0___boxed(
    mut v_s_1229_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1230_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__0(v_s_1229_);
    crate::leanh::lean_dec_ref(v_s_1229_);
    return v_res_1230_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__1___redArg(
    mut v_val_1231_: *mut crate::leanh::LeanObject,
    mut v___x_1232_: *mut crate::leanh::LeanObject,
    mut v___x_1233_: *mut crate::leanh::LeanObject,
    mut v_a_1234_: *mut crate::leanh::LeanObject,
    mut v_b_1235_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_it_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currPos_1244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1248_: u8 = 0;
    let mut v_startInclusive_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1252_: u8 = 0;
    let mut v___x_1253_: u32 = 0;
    let mut v___x_1254_: u32 = 0;
    let mut v___x_1255_: u8 = 0;
    let mut v___x_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_slice_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIt_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1271_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_1234_) == 0 {
                    v_currPos_1244_ = crate::leanh::lean_ctor_get(v_a_1234_, 0);
                    v_searcher_1245_ = crate::leanh::lean_ctor_get(v_a_1234_, 1);
                    v_isSharedCheck_1271_ = (!crate::leanh::lean_is_exclusive(v_a_1234_)) as u8;
                    if v_isSharedCheck_1271_ == 0 {
                        v___x_1247_ = v_a_1234_;
                        v_isShared_1248_ = v_isSharedCheck_1271_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_searcher_1245_);
                        crate::leanh::lean_inc(v_currPos_1244_);
                        crate::leanh::lean_dec(v_a_1234_);
                        v___x_1247_ = crate::leanh::lean_box(0);
                        v_isShared_1248_ = v_isSharedCheck_1271_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1233_);
                    crate::leanh::lean_dec_ref(v_val_1231_);
                    return v_b_1235_;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_val_1231_);
                v___x_1240_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1240_, 0, v_val_1231_);
                crate::leanh::lean_ctor_set(v___x_1240_, 1, v_startInclusive_1238_);
                crate::leanh::lean_ctor_set(v___x_1240_, 2, v_endExclusive_1239_);
                v___x_1241_ = l_String_Slice_toString(v___x_1240_);
                crate::leanh::lean_dec_ref_known(v___x_1240_, 3);
                v___x_1242_ = lean_array_push(v_b_1235_, v___x_1241_);
                v_a_1234_ = v_it_1237_;
                v_b_1235_ = v___x_1242_;
                state = 0;
                continue;
            }
            2 => {
                v_startInclusive_1249_ = crate::leanh::lean_ctor_get(v___x_1232_, 1);
                v_endExclusive_1250_ = crate::leanh::lean_ctor_get(v___x_1232_, 2);
                v___x_1251_ = lean_nat_sub(v_endExclusive_1250_, v_startInclusive_1249_);
                v___x_1252_ = lean_nat_dec_eq(v_searcher_1245_, v___x_1251_);
                crate::leanh::lean_dec(v___x_1251_);
                if v___x_1252_ == 0 {
                    v___x_1253_ = 10;
                    v___x_1254_ = lean_string_utf8_get_fast(v_val_1231_, v_searcher_1245_);
                    v___x_1255_ = lean_uint32_dec_eq(v___x_1254_, v___x_1253_);
                    if v___x_1255_ == 0 {
                        v___x_1256_ = lean_string_utf8_next_fast(v_val_1231_, v_searcher_1245_);
                        crate::leanh::lean_dec(v_searcher_1245_);
                        if v_isShared_1248_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1247_, 1, v___x_1256_);
                            v___x_1258_ = v___x_1247_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1260_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_currPos_1244_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1260_, 1, v___x_1256_);
                            v___x_1258_ = v_reuseFailAlloc_1260_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1261_ = lean_string_utf8_next_fast(v_val_1231_, v_searcher_1245_);
                        v___x_1262_ = lean_nat_sub(v___x_1261_, v_searcher_1245_);
                        v___x_1263_ = lean_nat_add(v_searcher_1245_, v___x_1262_);
                        crate::leanh::lean_dec(v___x_1262_);
                        v_slice_1264_ = l_String_Slice_subslice_x21(
                            v___x_1232_,
                            v_currPos_1244_,
                            v_searcher_1245_,
                        );
                        crate::leanh::lean_inc(v___x_1263_);
                        if v_isShared_1248_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1247_, 1, v___x_1263_);
                            crate::leanh::lean_ctor_set(v___x_1247_, 0, v___x_1263_);
                            v_nextIt_1266_ = v___x_1247_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1269_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1269_, 0, v___x_1263_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1269_, 1, v___x_1263_);
                            v_nextIt_1266_ = v_reuseFailAlloc_1269_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1247_);
                    crate::leanh::lean_dec(v_searcher_1245_);
                    v___x_1270_ = crate::leanh::lean_box(1);
                    crate::leanh::lean_inc(v___x_1233_);
                    v_it_1237_ = v___x_1270_;
                    v_startInclusive_1238_ = v_currPos_1244_;
                    v_endExclusive_1239_ = v___x_1233_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v_a_1234_ = v___x_1258_;
                state = 0;
                continue;
            }
            4 => {
                v_startInclusive_1267_ = crate::leanh::lean_ctor_get(v_slice_1264_, 0);
                crate::leanh::lean_inc(v_startInclusive_1267_);
                v_endExclusive_1268_ = crate::leanh::lean_ctor_get(v_slice_1264_, 1);
                crate::leanh::lean_inc(v_endExclusive_1268_);
                crate::leanh::lean_dec_ref(v_slice_1264_);
                v_it_1237_ = v_nextIt_1266_;
                v_startInclusive_1238_ = v_startInclusive_1267_;
                v_endExclusive_1239_ = v_endExclusive_1268_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__1___redArg___boxed(
    mut v_val_1272_: *mut crate::leanh::LeanObject,
    mut v___x_1273_: *mut crate::leanh::LeanObject,
    mut v___x_1274_: *mut crate::leanh::LeanObject,
    mut v_a_1275_: *mut crate::leanh::LeanObject,
    mut v_b_1276_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1277_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__1___redArg(v_val_1272_, v___x_1273_, v___x_1274_, v_a_1275_, v_b_1276_);
    crate::leanh::lean_dec_ref(v___x_1273_);
    return v_res_1277_;
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__3(
    mut v_a_1278_: *mut crate::leanh::LeanObject,
    mut v_a_1279_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1285_: u8 = 0;
    let mut v___x_1286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1291_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_1278_) == 0 {
                    v___x_1280_ = l_List_reverse___redArg(v_a_1279_);
                    return v___x_1280_;
                } else {
                    v_head_1281_ = crate::leanh::lean_ctor_get(v_a_1278_, 0);
                    v_tail_1282_ = crate::leanh::lean_ctor_get(v_a_1278_, 1);
                    v_isSharedCheck_1291_ = (!crate::leanh::lean_is_exclusive(v_a_1278_)) as u8;
                    if v_isSharedCheck_1291_ == 0 {
                        v___x_1284_ = v_a_1278_;
                        v_isShared_1285_ = v_isSharedCheck_1291_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1282_);
                        crate::leanh::lean_inc(v_head_1281_);
                        crate::leanh::lean_dec(v_a_1278_);
                        v___x_1284_ = crate::leanh::lean_box(0);
                        v_isShared_1285_ = v_isSharedCheck_1291_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1286_ = l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_indentLine(v_head_1281_);
                if v_isShared_1285_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1284_, 1, v_a_1279_);
                    crate::leanh::lean_ctor_set(v___x_1284_, 0, v___x_1286_);
                    v___x_1288_ = v___x_1284_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1290_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1290_, 0, v___x_1286_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1290_, 1, v_a_1279_);
                    v___x_1288_ = v_reuseFailAlloc_1290_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_1278_ = v_tail_1282_;
                v_a_1279_ = v___x_1288_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__2(
    mut v_s_1292_: *mut crate::leanh::LeanObject,
    mut v_pos_1293_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: u8 = 0;
    let mut v___x_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: u8 = 0;
    let mut v___y_1308_: u8 = 0;
    let mut v___x_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: u32 = 0;
    let mut v___y_1312_: u8 = 0;
    let mut v___x_1313_: u32 = 0;
    let mut v___x_1314_: u8 = 0;
    let mut v___x_1315_: u32 = 0;
    let mut v___x_1316_: u8 = 0;
    let mut v___x_1317_: u32 = 0;
    let mut v___x_1318_: u8 = 0;
    let mut v___x_1319_: u32 = 0;
    let mut v___x_1320_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_1294_ = crate::leanh::lean_ctor_get(v_s_1292_, 0);
                v_startInclusive_1295_ = crate::leanh::lean_ctor_get(v_s_1292_, 1);
                v___x_1296_ = lean_nat_add(v_startInclusive_1295_, v_pos_1293_);
                v___x_1297_ = lean_nat_sub(v___x_1296_, v_startInclusive_1295_);
                v___x_1298_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1299_ = lean_nat_dec_eq(v___x_1297_, v___x_1298_);
                if v___x_1299_ == 0 {
                    crate::leanh::lean_inc(v_startInclusive_1295_);
                    crate::leanh::lean_inc_ref(v_str_1294_);
                    v___x_1300_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1300_, 0, v_str_1294_);
                    crate::leanh::lean_ctor_set(v___x_1300_, 1, v_startInclusive_1295_);
                    crate::leanh::lean_ctor_set(v___x_1300_, 2, v___x_1296_);
                    v___x_1301_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1302_ = lean_nat_sub(v___x_1297_, v___x_1301_);
                    crate::leanh::lean_dec(v___x_1297_);
                    v___x_1303_ = l_String_Slice_posLE(v___x_1300_, v___x_1302_);
                    crate::leanh::lean_dec_ref_known(v___x_1300_, 3);
                    v___x_1309_ = lean_nat_add(v_startInclusive_1295_, v___x_1303_);
                    v___x_1310_ = lean_string_utf8_get_fast(v_str_1294_, v___x_1309_);
                    crate::leanh::lean_dec(v___x_1309_);
                    v___x_1317_ = 32;
                    v___x_1318_ = lean_uint32_dec_eq(v___x_1310_, v___x_1317_);
                    if v___x_1318_ == 0 {
                        v___x_1319_ = 9;
                        v___x_1320_ = lean_uint32_dec_eq(v___x_1310_, v___x_1319_);
                        v___y_1312_ = v___x_1320_;
                        state = 3;
                        continue;
                    } else {
                        v___y_1312_ = v___x_1318_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1297_);
                    crate::leanh::lean_dec(v___x_1296_);
                    return v_pos_1293_;
                }
            }
            1 => {
                v___x_1305_ = lean_nat_dec_lt(v___x_1303_, v_pos_1293_);
                if v___x_1305_ == 0 {
                    crate::leanh::lean_dec(v___x_1303_);
                    return v_pos_1293_;
                } else {
                    crate::leanh::lean_dec(v_pos_1293_);
                    v_pos_1293_ = v___x_1303_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                if v___y_1308_ == 0 {
                    crate::leanh::lean_dec(v___x_1303_);
                    return v_pos_1293_;
                } else {
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v___y_1312_ == 0 {
                    v___x_1313_ = 13;
                    v___x_1314_ = lean_uint32_dec_eq(v___x_1310_, v___x_1313_);
                    if v___x_1314_ == 0 {
                        v___x_1315_ = 10;
                        v___x_1316_ = lean_uint32_dec_eq(v___x_1310_, v___x_1315_);
                        v___y_1308_ = v___x_1316_;
                        state = 2;
                        continue;
                    } else {
                        v___y_1308_ = v___x_1314_;
                        state = 2;
                        continue;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__2___boxed(
    mut v_s_1321_: *mut crate::leanh::LeanObject,
    mut v_pos_1322_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1323_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__2(v_s_1321_, v_pos_1322_);
    crate::leanh::lean_dec_ref(v_s_1321_);
    return v_res_1323_;
}
pub unsafe fn l_List_foldl___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__4(
    mut v_x_1324_: *mut crate::leanh::LeanObject,
    mut v_x_1325_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1325_) == 0 {
                    return v_x_1324_;
                } else {
                    v_head_1326_ = crate::leanh::lean_ctor_get(v_x_1325_, 0);
                    v_tail_1327_ = crate::leanh::lean_ctor_get(v_x_1325_, 1);
                    v___x_1328_ = lean_string_append(v_x_1324_, v_head_1326_);
                    v_x_1324_ = v___x_1328_;
                    v_x_1325_ = v_tail_1327_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__4___boxed(
    mut v_x_1330_: *mut crate::leanh::LeanObject,
    mut v_x_1331_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1332_ = l_List_foldl___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__4(v_x_1330_, v_x_1331_);
    crate::leanh::lean_dec(v_x_1331_);
    return v_res_1332_;
}
pub unsafe fn l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet(
    mut v_spelling_1343_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_notation_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_recommendedSpelling_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_additionalInformation_x3f_1346_: *mut crate::leanh::LeanObject =
        core::ptr::null_mut();
    let mut v___x_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1349_: u8 = 0;
    let mut v___x_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_firstLine_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1391_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_notation_1344_ = crate::leanh::lean_ctor_get(v_spelling_1343_, 0);
                v_recommendedSpelling_1345_ = crate::leanh::lean_ctor_get(v_spelling_1343_, 1);
                v_additionalInformation_x3f_1346_ =
                    crate::leanh::lean_ctor_get(v_spelling_1343_, 2);
                v_isSharedCheck_1391_ = (!crate::leanh::lean_is_exclusive(v_spelling_1343_)) as u8;
                if v_isSharedCheck_1391_ == 0 {
                    v___x_1348_ = v_spelling_1343_;
                    v_isShared_1349_ = v_isSharedCheck_1391_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_additionalInformation_x3f_1346_);
                    crate::leanh::lean_inc(v_recommendedSpelling_1345_);
                    crate::leanh::lean_inc(v_notation_1344_);
                    crate::leanh::lean_dec(v_spelling_1343_);
                    v___x_1348_ = crate::leanh::lean_box(0);
                    v_isShared_1349_ = v_isSharedCheck_1391_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1350_ = l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__0;
                v___x_1351_ = lean_string_append(v___x_1350_, v_notation_1344_);
                crate::leanh::lean_dec_ref(v_notation_1344_);
                v___x_1352_ = l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__1;
                v___x_1353_ = lean_string_append(v___x_1351_, v___x_1352_);
                v___x_1354_ = lean_string_append(v___x_1353_, v_recommendedSpelling_1345_);
                crate::leanh::lean_dec_ref(v_recommendedSpelling_1345_);
                v___x_1355_ = l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__2;
                v_firstLine_1356_ = lean_string_append(v___x_1354_, v___x_1355_);
                if crate::leanh::lean_obj_tag(v_additionalInformation_x3f_1346_) == 0 {
                    crate::leanh::lean_del_object(v___x_1348_);
                    state = 2;
                    continue;
                } else {
                    v_val_1360_ = crate::leanh::lean_ctor_get(v_additionalInformation_x3f_1346_, 0);
                    crate::leanh::lean_inc_n(v_val_1360_, 2);
                    crate::leanh::lean_dec_ref_known(v_additionalInformation_x3f_1346_, 1);
                    v___x_1361_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1362_ = lean_string_utf8_byte_size(v_val_1360_);
                    if v_isShared_1349_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1348_, 2, v___x_1362_);
                        crate::leanh::lean_ctor_set(v___x_1348_, 1, v___x_1361_);
                        crate::leanh::lean_ctor_set(v___x_1348_, 0, v_val_1360_);
                        v___x_1364_ = v___x_1348_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1390_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1390_, 0, v_val_1360_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1390_, 1, v___x_1361_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1390_, 2, v___x_1362_);
                        v___x_1364_ = v_reuseFailAlloc_1390_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1358_ = l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__3;
                v___x_1359_ = lean_string_append(v_firstLine_1356_, v___x_1358_);
                return v___x_1359_;
            }
            3 => {
                v___x_1365_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__0(v___x_1364_);
                v___x_1366_ = l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__4;
                v___x_1367_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__1___redArg(v_val_1360_, v___x_1364_, v___x_1362_, v___x_1365_, v___x_1366_);
                crate::leanh::lean_dec_ref(v___x_1364_);
                v___x_1368_ = lean_array_to_list(v___x_1367_);
                if crate::leanh::lean_obj_tag(v___x_1368_) == 0 {
                    state = 2;
                    continue;
                } else {
                    v_tail_1369_ = crate::leanh::lean_ctor_get(v___x_1368_, 1);
                    crate::leanh::lean_inc(v_tail_1369_);
                    if crate::leanh::lean_obj_tag(v_tail_1369_) == 0 {
                        v_head_1370_ = crate::leanh::lean_ctor_get(v___x_1368_, 0);
                        crate::leanh::lean_inc_n(v_head_1370_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_1368_, 2);
                        v___x_1371_ = l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__5;
                        v___x_1372_ = lean_string_utf8_byte_size(v_head_1370_);
                        v___x_1373_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1373_, 0, v_head_1370_);
                        crate::leanh::lean_ctor_set(v___x_1373_, 1, v___x_1361_);
                        crate::leanh::lean_ctor_set(v___x_1373_, 2, v___x_1372_);
                        v___x_1374_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__2(v___x_1373_, v___x_1372_);
                        crate::leanh::lean_dec_ref_known(v___x_1373_, 3);
                        v___x_1375_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1375_, 0, v_head_1370_);
                        crate::leanh::lean_ctor_set(v___x_1375_, 1, v___x_1361_);
                        crate::leanh::lean_ctor_set(v___x_1375_, 2, v___x_1374_);
                        v___x_1376_ = l_String_Slice_toString(v___x_1375_);
                        crate::leanh::lean_dec_ref_known(v___x_1375_, 3);
                        v___x_1377_ = lean_string_append(v___x_1371_, v___x_1376_);
                        crate::leanh::lean_dec_ref(v___x_1376_);
                        v___x_1378_ = l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__6;
                        v___x_1379_ = lean_string_append(v___x_1377_, v___x_1378_);
                        v___x_1380_ = lean_string_append(v_firstLine_1356_, v___x_1379_);
                        crate::leanh::lean_dec_ref(v___x_1379_);
                        return v___x_1380_;
                    } else {
                        crate::leanh::lean_dec(v_tail_1369_);
                        v___x_1381_ = l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__3;
                        v___x_1382_ = lean_string_append(v_firstLine_1356_, v___x_1381_);
                        v___x_1383_ = crate::leanh::lean_box(0);
                        v___x_1384_ = l_List_mapTR_loop___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__3(v___x_1368_, v___x_1383_);
                        v___x_1385_ = l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__7;
                        v___x_1386_ = l_List_foldl___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__4(v___x_1385_, v___x_1384_);
                        crate::leanh::lean_dec(v___x_1384_);
                        v___x_1387_ = lean_string_append(v___x_1382_, v___x_1386_);
                        crate::leanh::lean_dec_ref(v___x_1386_);
                        v___x_1388_ = l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__8;
                        v___x_1389_ = lean_string_append(v___x_1387_, v___x_1388_);
                        return v___x_1389_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__1(
    mut v_val_1392_: *mut crate::leanh::LeanObject,
    mut v___x_1393_: *mut crate::leanh::LeanObject,
    mut v___x_1394_: *mut crate::leanh::LeanObject,
    mut v_inst_1395_: *mut crate::leanh::LeanObject,
    mut v_R_1396_: *mut crate::leanh::LeanObject,
    mut v_a_1397_: *mut crate::leanh::LeanObject,
    mut v_b_1398_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1399_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__1___redArg(v_val_1392_, v___x_1393_, v___x_1394_, v_a_1397_, v_b_1398_);
    return v___x_1399_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__1___boxed(
    mut v_val_1400_: *mut crate::leanh::LeanObject,
    mut v___x_1401_: *mut crate::leanh::LeanObject,
    mut v___x_1402_: *mut crate::leanh::LeanObject,
    mut v_inst_1403_: *mut crate::leanh::LeanObject,
    mut v_R_1404_: *mut crate::leanh::LeanObject,
    mut v_a_1405_: *mut crate::leanh::LeanObject,
    mut v_b_1406_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1407_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__1(v_val_1400_, v___x_1401_, v___x_1402_, v_inst_1403_, v_R_1404_, v_a_1405_, v_b_1406_);
    crate::leanh::lean_dec_ref(v___x_1401_);
    return v_res_1407_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Parser_Term_Doc_getRecommendedSpellingString_spec__0(
    mut v_a_1408_: *mut crate::leanh::LeanObject,
    mut v_a_1409_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1415_: u8 = 0;
    let mut v___x_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1421_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_1408_) == 0 {
                    v___x_1410_ = l_List_reverse___redArg(v_a_1409_);
                    return v___x_1410_;
                } else {
                    v_head_1411_ = crate::leanh::lean_ctor_get(v_a_1408_, 0);
                    v_tail_1412_ = crate::leanh::lean_ctor_get(v_a_1408_, 1);
                    v_isSharedCheck_1421_ = (!crate::leanh::lean_is_exclusive(v_a_1408_)) as u8;
                    if v_isSharedCheck_1421_ == 0 {
                        v___x_1414_ = v_a_1408_;
                        v_isShared_1415_ = v_isSharedCheck_1421_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1412_);
                        crate::leanh::lean_inc(v_head_1411_);
                        crate::leanh::lean_dec(v_a_1408_);
                        v___x_1414_ = crate::leanh::lean_box(0);
                        v_isShared_1415_ = v_isSharedCheck_1421_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1416_ = l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet(v_head_1411_);
                if v_isShared_1415_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1414_, 1, v_a_1409_);
                    crate::leanh::lean_ctor_set(v___x_1414_, 0, v___x_1416_);
                    v___x_1418_ = v___x_1414_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1420_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1420_, 0, v___x_1416_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1420_, 1, v_a_1409_);
                    v___x_1418_ = v_reuseFailAlloc_1420_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_1408_ = v_tail_1412_;
                v_a_1409_ = v___x_1418_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Parser_Term_Doc_getRecommendedSpellingString(
    mut v_env_1423_: *mut crate::leanh::LeanObject,
    mut v_declName_1424_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_spellings_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: u8 = 0;
    v_spellings_1425_ =
        l_Lean_Parser_Term_Doc_getRecommendedSpellingsForName(v_env_1423_, v_declName_1424_);
    v___x_1426_ = lean_array_get_size(v_spellings_1425_);
    v___x_1427_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1428_ = lean_nat_dec_eq(v___x_1426_, v___x_1427_);
    if v___x_1428_ == 0 {
        let mut v___x_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1429_ = l_Lean_Parser_Term_Doc_getRecommendedSpellingString___closed__0;
        v___x_1430_ = lean_array_to_list(v_spellings_1425_);
        v___x_1431_ = crate::leanh::lean_box(0);
        v___x_1432_ =
            l_List_mapTR_loop___at___00Lean_Parser_Term_Doc_getRecommendedSpellingString_spec__0(
                v___x_1430_,
                v___x_1431_,
            );
        v___x_1433_ = l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__7;
        v___x_1434_ = l_List_foldl___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__4(v___x_1433_, v___x_1432_);
        crate::leanh::lean_dec(v___x_1432_);
        v___x_1435_ = lean_string_append(v___x_1429_, v___x_1434_);
        crate::leanh::lean_dec_ref(v___x_1434_);
        v___x_1436_ = lean_string_utf8_byte_size(v___x_1435_);
        crate::leanh::lean_inc_ref(v___x_1435_);
        v___x_1437_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1437_, 0, v___x_1435_);
        crate::leanh::lean_ctor_set(v___x_1437_, 1, v___x_1427_);
        crate::leanh::lean_ctor_set(v___x_1437_, 2, v___x_1436_);
        v___x_1438_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__2(v___x_1437_, v___x_1436_);
        crate::leanh::lean_dec_ref_known(v___x_1437_, 3);
        v___x_1439_ = lean_string_utf8_extract(v___x_1435_, v___x_1427_, v___x_1438_);
        crate::leanh::lean_dec(v___x_1438_);
        crate::leanh::lean_dec_ref(v___x_1435_);
        return v___x_1439_;
    } else {
        let mut v___x_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_spellings_1425_);
        v___x_1440_ = l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__7;
        return v___x_1440_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Parser_Term_Doc(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Parser_Extension(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Parser_Term_Doc_recommendedSpellingByNameExt =
        crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Term_Doc_recommendedSpellingByNameExt);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Parser_Term_Doc_recommendedSpellingExt = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Term_Doc_recommendedSpellingExt);
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Parser_Term_Doc(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Parser_Term_Doc(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Parser_Extension(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Parser_Term_Doc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Parser_Term_Doc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Parser_Term_Doc(builtin);
}
