// Lean compiler output
// Module: Init.Data.Array.Sort.Basic
// Imports: Init.Data.Array.Subarray.Split Init.Data.Slice.Array Init.Omega
use crate::r#gen::Init::Data::Array::Subarray::Split::{
    initialize_Init_Data_Array_Subarray_Split, l_Subarray_drop___redArg,
    runtime_initialize_Init_Data_Array_Subarray_Split,
};
use crate::r#gen::Init::Data::Array::Subarray::{
    l_Array_toSubarray___redArg, l_Subarray_get___redArg,
};
use crate::r#gen::Init::Data::Slice::Array::{
    initialize_Init_Data_Slice_Array, runtime_initialize_Init_Data_Slice_Array,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::l_Lean_mkAtom;
use crate::ffi::lean_nat_shiftr;
use crate::ffi::{
    lean_array_fget, lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity,
    lean_nat_add, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_string_utf8_byte_size,
};
pub static l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__2_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__3_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0]};
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__3_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__2_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__4_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__3_value) as *mut crate::leanh::LeanObject,8504843326314613972 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__5_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__6_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0]};
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__6_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__7_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__7_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__7_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__7_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__7_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__2_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__7_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__7_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__6_value) as *mut crate::leanh::LeanObject,17228437386856258271 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__8_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__9_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__8_value) as *mut crate::leanh::LeanObject,9855511589286918680 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__10_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [101, 120, 97, 99, 116, 0]};
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__10_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__11_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__11_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__11_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__11_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__11_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__2_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__11_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__11_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__10_value) as *mut crate::leanh::LeanObject,14997215300048349804 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__11_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__12_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__12: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__13_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__13: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__14_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__15_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [112, 97, 114, 101, 110, 0]};
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__15_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__16_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__16_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__16_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__16_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__16_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__14_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__16_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__16_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__15_value) as *mut crate::leanh::LeanObject,7932075773091973500 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__16_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__17_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [104, 121, 103, 105, 101, 110, 105, 99, 76, 80, 97, 114, 101, 110, 0]};
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__17_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__18_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__18_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__18_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__18_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__18_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__14_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__18_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__18_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__17_value) as *mut crate::leanh::LeanObject,7306243862518720553 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__18_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__19_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__19: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__19_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__20_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__20: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__21_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__21: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__22_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0]};
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__22: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__22_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__23_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__22_value) as *mut crate::leanh::LeanObject,9871775667037945883 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__23: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__23_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__24_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [91, 97, 110, 111, 110, 121, 109, 111, 117, 115, 93, 0]};
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__24: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__24_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__25_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__25: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__26_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__26: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__27_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__27: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__28_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__28: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__29_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__29: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__30_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__30: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__31_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__31: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__32_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__32: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__33_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 7, m_data: [116, 101, 114, 109, 95, 226, 137, 164, 95, 0]};
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__33: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__33_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__34_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__33_value) as *mut crate::leanh::LeanObject,8748957123817046895 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__34: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__34_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__35_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [99, 100, 111, 116, 0]};
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__35: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__35_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__36_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__36_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__36_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__36_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__36_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__14_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__36_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__36_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__35_value) as *mut crate::leanh::LeanObject,6167508377434939095 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__36: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__36_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__37_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 1, m_data: [194, 183, 0]};
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__37: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__37_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__38_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__38: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__39_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__39: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__40_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__40: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__41_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__41: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__42_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__42: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__43_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 137, 164, 0]};
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__43: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__43_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__44_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__44: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__45_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__45: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__46_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__46: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__47_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__47: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__48_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__48: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__49_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__49: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__49_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__50_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__50: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__51_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__51: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__52_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__52: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__53_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__53: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__54_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__54: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__55_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__55: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__56_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__56: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__57_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__57: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__58_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__58: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__59_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__59: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__60_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__60: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Subarray_mergeSort___auto__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Subarray_mergeSort___redArg___closed__0_value: crate::leanh::LeanArrayObject<0> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Subarray_mergeSort___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Subarray_mergeSort___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Array_mergeSort___auto__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_346_ = l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__10;
    v___x_347_ = l_Lean_mkAtom(v___x_346_);
    return v___x_347_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_348_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__12), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__12_once), _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__12);
    v___x_349_ = l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__5;
    v___x_350_ = lean_array_push(v___x_349_, v___x_348_);
    return v___x_350_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__20()
-> *mut crate::leanh::LeanObject {
    let mut v___x_365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_365_ = l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__19;
    v___x_366_ = l_Lean_mkAtom(v___x_365_);
    return v___x_366_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__21()
-> *mut crate::leanh::LeanObject {
    let mut v___x_367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_367_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__20), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__20_once), _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__20);
    v___x_368_ = l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__5;
    v___x_369_ = lean_array_push(v___x_368_, v___x_367_);
    return v___x_369_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__25()
-> *mut crate::leanh::LeanObject {
    let mut v___x_374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_374_ = l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__24;
    v___x_375_ = lean_string_utf8_byte_size(v___x_374_);
    return v___x_375_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__26()
-> *mut crate::leanh::LeanObject {
    let mut v___x_376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_376_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__25), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__25_once), _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__25);
    v___x_377_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_378_ = l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__24;
    v___x_379_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_379_, 0, v___x_378_);
    crate::leanh::lean_ctor_set(v___x_379_, 1, v___x_377_);
    crate::leanh::lean_ctor_set(v___x_379_, 2, v___x_376_);
    return v___x_379_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__27()
-> *mut crate::leanh::LeanObject {
    let mut v___x_380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_380_ = crate::leanh::lean_box(0);
    v___x_381_ = crate::leanh::lean_box(0);
    v___x_382_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__26), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__26_once), _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__26);
    v___x_383_ = crate::leanh::lean_box(2);
    v___x_384_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_384_, 0, v___x_383_);
    crate::leanh::lean_ctor_set(v___x_384_, 1, v___x_382_);
    crate::leanh::lean_ctor_set(v___x_384_, 2, v___x_381_);
    crate::leanh::lean_ctor_set(v___x_384_, 3, v___x_380_);
    return v___x_384_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__28()
-> *mut crate::leanh::LeanObject {
    let mut v___x_385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_385_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__27), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__27_once), _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__27);
    v___x_386_ = l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__5;
    v___x_387_ = lean_array_push(v___x_386_, v___x_385_);
    return v___x_387_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__29()
-> *mut crate::leanh::LeanObject {
    let mut v___x_388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_388_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__28), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__28_once), _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__28);
    v___x_389_ = l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__23;
    v___x_390_ = crate::leanh::lean_box(2);
    v___x_391_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_391_, 0, v___x_390_);
    crate::leanh::lean_ctor_set(v___x_391_, 1, v___x_389_);
    crate::leanh::lean_ctor_set(v___x_391_, 2, v___x_388_);
    return v___x_391_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__30()
-> *mut crate::leanh::LeanObject {
    let mut v___x_392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_392_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__29), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__29_once), _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__29);
    v___x_393_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__21), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__21_once), _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__21);
    v___x_394_ = lean_array_push(v___x_393_, v___x_392_);
    return v___x_394_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__31()
-> *mut crate::leanh::LeanObject {
    let mut v___x_395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_395_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__30), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__30_once), _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__30);
    v___x_396_ = l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__18;
    v___x_397_ = crate::leanh::lean_box(2);
    v___x_398_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_398_, 0, v___x_397_);
    crate::leanh::lean_ctor_set(v___x_398_, 1, v___x_396_);
    crate::leanh::lean_ctor_set(v___x_398_, 2, v___x_395_);
    return v___x_398_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__32()
-> *mut crate::leanh::LeanObject {
    let mut v___x_399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_399_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__31), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__31_once), _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__31);
    v___x_400_ = l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__5;
    v___x_401_ = lean_array_push(v___x_400_, v___x_399_);
    return v___x_401_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__38()
-> *mut crate::leanh::LeanObject {
    let mut v___x_412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_412_ = l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__37;
    v___x_413_ = l_Lean_mkAtom(v___x_412_);
    return v___x_413_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__39()
-> *mut crate::leanh::LeanObject {
    let mut v___x_414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_414_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__38), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__38_once), _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__38);
    v___x_415_ = l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__5;
    v___x_416_ = lean_array_push(v___x_415_, v___x_414_);
    return v___x_416_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__40()
-> *mut crate::leanh::LeanObject {
    let mut v___x_417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_417_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__29), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__29_once), _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__29);
    v___x_418_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__39), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__39_once), _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__39);
    v___x_419_ = lean_array_push(v___x_418_, v___x_417_);
    return v___x_419_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__41()
-> *mut crate::leanh::LeanObject {
    let mut v___x_420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_420_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__40), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__40_once), _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__40);
    v___x_421_ = l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__36;
    v___x_422_ = crate::leanh::lean_box(2);
    v___x_423_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_423_, 0, v___x_422_);
    crate::leanh::lean_ctor_set(v___x_423_, 1, v___x_421_);
    crate::leanh::lean_ctor_set(v___x_423_, 2, v___x_420_);
    return v___x_423_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__42()
-> *mut crate::leanh::LeanObject {
    let mut v___x_424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_424_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__41), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__41_once), _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__41);
    v___x_425_ = l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__5;
    v___x_426_ = lean_array_push(v___x_425_, v___x_424_);
    return v___x_426_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__44()
-> *mut crate::leanh::LeanObject {
    let mut v___x_428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_428_ = l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__43;
    v___x_429_ = l_Lean_mkAtom(v___x_428_);
    return v___x_429_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__45()
-> *mut crate::leanh::LeanObject {
    let mut v___x_430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_430_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__44), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__44_once), _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__44);
    v___x_431_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__42), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__42_once), _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__42);
    v___x_432_ = lean_array_push(v___x_431_, v___x_430_);
    return v___x_432_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__46()
-> *mut crate::leanh::LeanObject {
    let mut v___x_433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_433_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__41), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__41_once), _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__41);
    v___x_434_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__45), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__45_once), _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__45);
    v___x_435_ = lean_array_push(v___x_434_, v___x_433_);
    return v___x_435_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__47()
-> *mut crate::leanh::LeanObject {
    let mut v___x_436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_436_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__46), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__46_once), _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__46);
    v___x_437_ = l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__34;
    v___x_438_ = crate::leanh::lean_box(2);
    v___x_439_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_439_, 0, v___x_438_);
    crate::leanh::lean_ctor_set(v___x_439_, 1, v___x_437_);
    crate::leanh::lean_ctor_set(v___x_439_, 2, v___x_436_);
    return v___x_439_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__48()
-> *mut crate::leanh::LeanObject {
    let mut v___x_440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_440_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__47), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__47_once), _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__47);
    v___x_441_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__32), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__32_once), _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__32);
    v___x_442_ = lean_array_push(v___x_441_, v___x_440_);
    return v___x_442_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__50()
-> *mut crate::leanh::LeanObject {
    let mut v___x_444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_444_ = l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__49;
    v___x_445_ = l_Lean_mkAtom(v___x_444_);
    return v___x_445_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__51()
-> *mut crate::leanh::LeanObject {
    let mut v___x_446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_446_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__50), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__50_once), _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__50);
    v___x_447_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__48), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__48_once), _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__48);
    v___x_448_ = lean_array_push(v___x_447_, v___x_446_);
    return v___x_448_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__52()
-> *mut crate::leanh::LeanObject {
    let mut v___x_449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_449_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__51), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__51_once), _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__51);
    v___x_450_ = l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__16;
    v___x_451_ = crate::leanh::lean_box(2);
    v___x_452_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_452_, 0, v___x_451_);
    crate::leanh::lean_ctor_set(v___x_452_, 1, v___x_450_);
    crate::leanh::lean_ctor_set(v___x_452_, 2, v___x_449_);
    return v___x_452_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__53()
-> *mut crate::leanh::LeanObject {
    let mut v___x_453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_453_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__52), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__52_once), _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__52);
    v___x_454_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__13), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__13_once), _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__13);
    v___x_455_ = lean_array_push(v___x_454_, v___x_453_);
    return v___x_455_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__54()
-> *mut crate::leanh::LeanObject {
    let mut v___x_456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_456_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__53), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__53_once), _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__53);
    v___x_457_ = l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__11;
    v___x_458_ = crate::leanh::lean_box(2);
    v___x_459_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_459_, 0, v___x_458_);
    crate::leanh::lean_ctor_set(v___x_459_, 1, v___x_457_);
    crate::leanh::lean_ctor_set(v___x_459_, 2, v___x_456_);
    return v___x_459_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__55()
-> *mut crate::leanh::LeanObject {
    let mut v___x_460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_460_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__54), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__54_once), _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__54);
    v___x_461_ = l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__5;
    v___x_462_ = lean_array_push(v___x_461_, v___x_460_);
    return v___x_462_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__56()
-> *mut crate::leanh::LeanObject {
    let mut v___x_463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_463_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__55), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__55_once), _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__55);
    v___x_464_ = l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__9;
    v___x_465_ = crate::leanh::lean_box(2);
    v___x_466_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_466_, 0, v___x_465_);
    crate::leanh::lean_ctor_set(v___x_466_, 1, v___x_464_);
    crate::leanh::lean_ctor_set(v___x_466_, 2, v___x_463_);
    return v___x_466_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__57()
-> *mut crate::leanh::LeanObject {
    let mut v___x_467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_467_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__56), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__56_once), _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__56);
    v___x_468_ = l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__5;
    v___x_469_ = lean_array_push(v___x_468_, v___x_467_);
    return v___x_469_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__58()
-> *mut crate::leanh::LeanObject {
    let mut v___x_470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_470_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__57), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__57_once), _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__57);
    v___x_471_ = l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__7;
    v___x_472_ = crate::leanh::lean_box(2);
    v___x_473_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_473_, 0, v___x_472_);
    crate::leanh::lean_ctor_set(v___x_473_, 1, v___x_471_);
    crate::leanh::lean_ctor_set(v___x_473_, 2, v___x_470_);
    return v___x_473_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__59()
-> *mut crate::leanh::LeanObject {
    let mut v___x_474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_474_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__58), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__58_once), _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__58);
    v___x_475_ = l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__5;
    v___x_476_ = lean_array_push(v___x_475_, v___x_474_);
    return v___x_476_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__60()
-> *mut crate::leanh::LeanObject {
    let mut v___x_477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_477_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__59), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__59_once), _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__59);
    v___x_478_ = l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__4;
    v___x_479_ = crate::leanh::lean_box(2);
    v___x_480_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_480_, 0, v___x_479_);
    crate::leanh::lean_ctor_set(v___x_480_, 1, v___x_478_);
    crate::leanh::lean_ctor_set(v___x_480_, 2, v___x_477_);
    return v___x_480_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_481_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__60), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__60_once), _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__60);
    return v___x_481_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge_go_spec__0___redArg(
    mut v_a_482_: *mut crate::leanh::LeanObject,
    mut v_b_483_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_array_484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_489_: u8 = 0;
    let mut v___x_490_: u8 = 0;
    let mut v___x_491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_499_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_484_ = crate::leanh::lean_ctor_get(v_a_482_, 0);
                v_start_485_ = crate::leanh::lean_ctor_get(v_a_482_, 1);
                v_stop_486_ = crate::leanh::lean_ctor_get(v_a_482_, 2);
                v_isSharedCheck_499_ = (!crate::leanh::lean_is_exclusive(v_a_482_)) as u8;
                if v_isSharedCheck_499_ == 0 {
                    v___x_488_ = v_a_482_;
                    v_isShared_489_ = v_isSharedCheck_499_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_stop_486_);
                    crate::leanh::lean_inc(v_start_485_);
                    crate::leanh::lean_inc(v_array_484_);
                    crate::leanh::lean_dec(v_a_482_);
                    v___x_488_ = crate::leanh::lean_box(0);
                    v_isShared_489_ = v_isSharedCheck_499_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_490_ = lean_nat_dec_lt(v_start_485_, v_stop_486_);
                if v___x_490_ == 0 {
                    crate::leanh::lean_del_object(v___x_488_);
                    crate::leanh::lean_dec(v_stop_486_);
                    crate::leanh::lean_dec(v_start_485_);
                    crate::leanh::lean_dec_ref(v_array_484_);
                    return v_b_483_;
                } else {
                    v___x_491_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_492_ = lean_nat_add(v_start_485_, v___x_491_);
                    crate::leanh::lean_inc_ref(v_array_484_);
                    if v_isShared_489_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_488_, 1, v___x_492_);
                        v___x_494_ = v___x_488_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_498_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_498_, 0, v_array_484_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_498_, 1, v___x_492_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_498_, 2, v_stop_486_);
                        v___x_494_ = v_reuseFailAlloc_498_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_495_ = lean_array_fget(v_array_484_, v_start_485_);
                crate::leanh::lean_dec(v_start_485_);
                crate::leanh::lean_dec_ref(v_array_484_);
                v___x_496_ = lean_array_push(v_b_483_, v___x_495_);
                v_a_482_ = v___x_494_;
                v_b_483_ = v___x_496_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge_go___redArg(
    mut v_le_500_: *mut crate::leanh::LeanObject,
    mut v_xs_501_: *mut crate::leanh::LeanObject,
    mut v_ys_502_: *mut crate::leanh::LeanObject,
    mut v_acc_503_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_start_504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_512_: u8 = 0;
    let mut v___x_513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_515_: u8 = 0;
    let mut v___x_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_523_: u8 = 0;
    let mut v___x_524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_start_504_ = crate::leanh::lean_ctor_get(v_xs_501_, 1);
                v_stop_505_ = crate::leanh::lean_ctor_get(v_xs_501_, 2);
                v_start_506_ = crate::leanh::lean_ctor_get(v_ys_502_, 1);
                v_stop_507_ = crate::leanh::lean_ctor_get(v_ys_502_, 2);
                v___x_508_ = crate::leanh::lean_unsigned_to_nat(0);
                v_x_509_ = l_Subarray_get___redArg(v_xs_501_, v___x_508_);
                v_y_510_ = l_Subarray_get___redArg(v_ys_502_, v___x_508_);
                crate::leanh::lean_inc_ref(v_le_500_);
                crate::leanh::lean_inc(v_y_510_);
                crate::leanh::lean_inc(v_x_509_);
                v___x_511_ = crate::leanh::lean_apply_2(v_le_500_, v_x_509_, v_y_510_);
                v___x_512_ = (crate::leanh::lean_unbox(v___x_511_) as u8);
                if v___x_512_ == 0 {
                    crate::leanh::lean_dec(v_x_509_);
                    v___x_513_ = lean_nat_sub(v_stop_507_, v_start_506_);
                    v___x_514_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_515_ = lean_nat_dec_lt(v___x_514_, v___x_513_);
                    crate::leanh::lean_dec(v___x_513_);
                    if v___x_515_ == 0 {
                        crate::leanh::lean_dec_ref(v_ys_502_);
                        crate::leanh::lean_dec_ref(v_le_500_);
                        v___x_516_ = lean_array_push(v_acc_503_, v_y_510_);
                        v___x_517_ = l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge_go_spec__0___redArg(v_xs_501_, v___x_516_);
                        return v___x_517_;
                    } else {
                        v___x_518_ = l_Subarray_drop___redArg(v_ys_502_, v___x_514_);
                        v___x_519_ = lean_array_push(v_acc_503_, v_y_510_);
                        v_ys_502_ = v___x_518_;
                        v_acc_503_ = v___x_519_;
                        state = 0;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_y_510_);
                    v___x_521_ = lean_nat_sub(v_stop_505_, v_start_504_);
                    v___x_522_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_523_ = lean_nat_dec_lt(v___x_522_, v___x_521_);
                    crate::leanh::lean_dec(v___x_521_);
                    if v___x_523_ == 0 {
                        crate::leanh::lean_dec_ref(v_xs_501_);
                        crate::leanh::lean_dec_ref(v_le_500_);
                        v___x_524_ = lean_array_push(v_acc_503_, v_x_509_);
                        v___x_525_ = l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge_go_spec__0___redArg(v_ys_502_, v___x_524_);
                        return v___x_525_;
                    } else {
                        v___x_526_ = l_Subarray_drop___redArg(v_xs_501_, v___x_522_);
                        v___x_527_ = lean_array_push(v_acc_503_, v_x_509_);
                        v_xs_501_ = v___x_526_;
                        v_acc_503_ = v___x_527_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge_go(
    mut v_00_u03b1_529_: *mut crate::leanh::LeanObject,
    mut v_le_530_: *mut crate::leanh::LeanObject,
    mut v_xs_531_: *mut crate::leanh::LeanObject,
    mut v_ys_532_: *mut crate::leanh::LeanObject,
    mut v_hxs_533_: *mut crate::leanh::LeanObject,
    mut v_hys_534_: *mut crate::leanh::LeanObject,
    mut v_acc_535_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_536_ =
        l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge_go___redArg(
            v_le_530_, v_xs_531_, v_ys_532_, v_acc_535_,
        );
    return v___x_536_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge_go_spec__0(
    mut v_00_u03b1_537_: *mut crate::leanh::LeanObject,
    mut v_inst_538_: *mut crate::leanh::LeanObject,
    mut v_R_539_: *mut crate::leanh::LeanObject,
    mut v_a_540_: *mut crate::leanh::LeanObject,
    mut v_b_541_: *mut crate::leanh::LeanObject,
    mut v_c_542_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_543_ = l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge_go_spec__0___redArg(v_a_540_, v_b_541_);
    return v___x_543_;
}
pub unsafe fn l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___redArg(
    mut v_xs_544_: *mut crate::leanh::LeanObject,
    mut v_ys_545_: *mut crate::leanh::LeanObject,
    mut v_le_546_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_549_: u8 = 0;
    v___x_547_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_548_ = lean_array_get_size(v_xs_544_);
    v___x_549_ = lean_nat_dec_lt(v___x_547_, v___x_548_);
    if v___x_549_ == 0 {
        crate::leanh::lean_dec_ref(v_le_546_);
        crate::leanh::lean_dec_ref(v_xs_544_);
        return v_ys_545_;
    } else {
        let mut v___x_550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_551_: u8 = 0;
        v___x_550_ = lean_array_get_size(v_ys_545_);
        v___x_551_ = lean_nat_dec_lt(v___x_547_, v___x_550_);
        if v___x_551_ == 0 {
            crate::leanh::lean_dec_ref(v_le_546_);
            crate::leanh::lean_dec_ref(v_ys_545_);
            return v_xs_544_;
        } else {
            let mut v___x_552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_552_ = l_Array_toSubarray___redArg(v_xs_544_, v___x_547_, v___x_548_);
            v___x_553_ = l_Array_toSubarray___redArg(v_ys_545_, v___x_547_, v___x_550_);
            v___x_554_ = lean_nat_add(v___x_548_, v___x_550_);
            v___x_555_ = lean_mk_empty_array_with_capacity(v___x_554_);
            crate::leanh::lean_dec(v___x_554_);
            v___x_556_ = l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge_go___redArg(v_le_546_, v___x_552_, v___x_553_, v___x_555_);
            return v___x_556_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge(
    mut v_00_u03b1_557_: *mut crate::leanh::LeanObject,
    mut v_xs_558_: *mut crate::leanh::LeanObject,
    mut v_ys_559_: *mut crate::leanh::LeanObject,
    mut v_le_560_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_561_ = l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___redArg(
        v_xs_558_, v_ys_559_, v_le_560_,
    );
    return v___x_561_;
}
pub unsafe fn _init_l_Subarray_mergeSort___auto__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_562_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__60), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__60_once), _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__60);
    return v___x_562_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Subarray_mergeSort_spec__0___redArg(
    mut v_a_563_: *mut crate::leanh::LeanObject,
    mut v_b_564_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_array_565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_570_: u8 = 0;
    let mut v___x_571_: u8 = 0;
    let mut v___x_572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_580_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_565_ = crate::leanh::lean_ctor_get(v_a_563_, 0);
                v_start_566_ = crate::leanh::lean_ctor_get(v_a_563_, 1);
                v_stop_567_ = crate::leanh::lean_ctor_get(v_a_563_, 2);
                v_isSharedCheck_580_ = (!crate::leanh::lean_is_exclusive(v_a_563_)) as u8;
                if v_isSharedCheck_580_ == 0 {
                    v___x_569_ = v_a_563_;
                    v_isShared_570_ = v_isSharedCheck_580_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_stop_567_);
                    crate::leanh::lean_inc(v_start_566_);
                    crate::leanh::lean_inc(v_array_565_);
                    crate::leanh::lean_dec(v_a_563_);
                    v___x_569_ = crate::leanh::lean_box(0);
                    v_isShared_570_ = v_isSharedCheck_580_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_571_ = lean_nat_dec_lt(v_start_566_, v_stop_567_);
                if v___x_571_ == 0 {
                    crate::leanh::lean_del_object(v___x_569_);
                    crate::leanh::lean_dec(v_stop_567_);
                    crate::leanh::lean_dec(v_start_566_);
                    crate::leanh::lean_dec_ref(v_array_565_);
                    return v_b_564_;
                } else {
                    v___x_572_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_573_ = lean_nat_add(v_start_566_, v___x_572_);
                    crate::leanh::lean_inc_ref(v_array_565_);
                    if v_isShared_570_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_569_, 1, v___x_573_);
                        v___x_575_ = v___x_569_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_579_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_579_, 0, v_array_565_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_579_, 1, v___x_573_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_579_, 2, v_stop_567_);
                        v___x_575_ = v_reuseFailAlloc_579_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_576_ = lean_array_fget(v_array_565_, v_start_566_);
                crate::leanh::lean_dec(v_start_566_);
                crate::leanh::lean_dec_ref(v_array_565_);
                v___x_577_ = lean_array_push(v_b_564_, v___x_576_);
                v_a_563_ = v___x_575_;
                v_b_564_ = v___x_577_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Subarray_mergeSort___redArg(
    mut v_xs_583_: *mut crate::leanh::LeanObject,
    mut v_le_584_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_array_585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_600_: u8 = 0;
    let mut v___x_601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_splitIdx_604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_612_: u8 = 0;
    let mut v___x_613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_614_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_585_ = crate::leanh::lean_ctor_get(v_xs_583_, 0);
                v_start_586_ = crate::leanh::lean_ctor_get(v_xs_583_, 1);
                v_stop_587_ = crate::leanh::lean_ctor_get(v_xs_583_, 2);
                v___x_598_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_599_ = lean_nat_sub(v_stop_587_, v_start_586_);
                v___x_600_ = lean_nat_dec_lt(v___x_598_, v___x_599_);
                if v___x_600_ == 0 {
                    crate::leanh::lean_dec(v___x_599_);
                    crate::leanh::lean_dec_ref(v_le_584_);
                    v___x_601_ = l_Subarray_mergeSort___redArg___closed__0;
                    v___x_602_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Subarray_mergeSort_spec__0___redArg(v_xs_583_, v___x_601_);
                    return v___x_602_;
                } else {
                    crate::leanh::lean_inc(v_start_586_);
                    crate::leanh::lean_inc_ref(v_array_585_);
                    crate::leanh::lean_dec_ref(v_xs_583_);
                    v___x_603_ = lean_nat_add(v___x_599_, v___x_598_);
                    v_splitIdx_604_ = lean_nat_shiftr(v___x_603_, v___x_598_);
                    crate::leanh::lean_dec(v___x_603_);
                    v___x_613_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_614_ = lean_nat_dec_le(v_splitIdx_604_, v___x_599_);
                    if v___x_614_ == 0 {
                        crate::leanh::lean_inc(v___x_599_);
                        v_lower_606_ = v___x_613_;
                        v_upper_607_ = v___x_599_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_splitIdx_604_);
                        v_lower_606_ = v___x_613_;
                        v_upper_607_ = v_splitIdx_604_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_592_ = lean_nat_add(v_lower_590_, v_start_586_);
                crate::leanh::lean_dec(v_lower_590_);
                v___x_593_ = lean_nat_add(v_upper_591_, v_start_586_);
                crate::leanh::lean_dec(v_start_586_);
                crate::leanh::lean_dec(v_upper_591_);
                v___x_594_ = l_Array_toSubarray___redArg(v_array_585_, v___x_592_, v___x_593_);
                crate::leanh::lean_inc_ref_n(v_le_584_, 2);
                v___x_595_ = l_Subarray_mergeSort___redArg(v___y_589_, v_le_584_);
                v___x_596_ = l_Subarray_mergeSort___redArg(v___x_594_, v_le_584_);
                v___x_597_ = l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___redArg(v___x_595_, v___x_596_, v_le_584_);
                return v___x_597_;
            }
            2 => {
                v___x_608_ = lean_nat_add(v_lower_606_, v_start_586_);
                v___x_609_ = lean_nat_add(v_upper_607_, v_start_586_);
                crate::leanh::lean_dec(v_upper_607_);
                crate::leanh::lean_inc_ref(v_array_585_);
                v___x_610_ = l_Array_toSubarray___redArg(v_array_585_, v___x_608_, v___x_609_);
                v___x_611_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_612_ = lean_nat_dec_le(v_splitIdx_604_, v___x_611_);
                if v___x_612_ == 0 {
                    v___y_589_ = v___x_610_;
                    v_lower_590_ = v_splitIdx_604_;
                    v_upper_591_ = v___x_599_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_splitIdx_604_);
                    v___y_589_ = v___x_610_;
                    v_lower_590_ = v___x_611_;
                    v_upper_591_ = v___x_599_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Subarray_mergeSort(
    mut v_00_u03b1_615_: *mut crate::leanh::LeanObject,
    mut v_xs_616_: *mut crate::leanh::LeanObject,
    mut v_le_617_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_618_ = l_Subarray_mergeSort___redArg(v_xs_616_, v_le_617_);
    return v___x_618_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Subarray_mergeSort_spec__0(
    mut v_00_u03b1_619_: *mut crate::leanh::LeanObject,
    mut v_inst_620_: *mut crate::leanh::LeanObject,
    mut v_R_621_: *mut crate::leanh::LeanObject,
    mut v_a_622_: *mut crate::leanh::LeanObject,
    mut v_b_623_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_624_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Subarray_mergeSort_spec__0___redArg(v_a_622_, v_b_623_);
    return v___x_624_;
}
pub unsafe fn _init_l_Array_mergeSort___auto__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_625_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__60), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__60_once), _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__60);
    return v___x_625_;
}
pub unsafe fn l_Array_mergeSort___redArg(
    mut v_xs_626_: *mut crate::leanh::LeanObject,
    mut v_le_627_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_628_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_629_ = lean_array_get_size(v_xs_626_);
    v___x_630_ = l_Array_toSubarray___redArg(v_xs_626_, v___x_628_, v___x_629_);
    v___x_631_ = l_Subarray_mergeSort___redArg(v___x_630_, v_le_627_);
    return v___x_631_;
}
pub unsafe fn l_Array_mergeSort(
    mut v_00_u03b1_632_: *mut crate::leanh::LeanObject,
    mut v_xs_633_: *mut crate::leanh::LeanObject,
    mut v_le_634_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_635_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_636_ = lean_array_get_size(v_xs_633_);
    v___x_637_ = l_Array_toSubarray___redArg(v_xs_633_, v___x_635_, v___x_636_);
    v___x_638_ = l_Subarray_mergeSort___redArg(v___x_637_, v_le_634_);
    return v___x_638_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Array_Sort_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Array_Subarray_Split(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Slice_Array(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Array_Sort_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1 =
        _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1();
    crate::leanh::lean_mark_persistent(
        l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1,
    );
    l_Subarray_mergeSort___auto__1 = _init_l_Subarray_mergeSort___auto__1();
    crate::leanh::lean_mark_persistent(l_Subarray_mergeSort___auto__1);
    l_Array_mergeSort___auto__1 = _init_l_Array_mergeSort___auto__1();
    crate::leanh::lean_mark_persistent(l_Array_mergeSort___auto__1);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Array_Sort_Basic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Array_Subarray_Split(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Slice_Array(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Sort_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Array_Sort_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Array_Sort_Basic(builtin);
}
