// Lean compiler output
// Module: phashmap3
// Imports: public import Init public meta import Init public import Lean.Data.PersistentHashMap public import Lean.Data.Format
use lean_runtime::generated_abi::*;
extern "C" {
    fn lean_get_stdout() -> *mut lean_object;
    fn lean_usize_shift_left(_: usize, _: usize) -> usize;
    fn lean_usize_sub(_: usize, _: usize) -> usize;
    fn lean_usize_land(_: usize, _: usize) -> usize;
    fn lean_usize_to_nat(_: usize) -> *mut lean_object;
    fn lean_array_get(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_nat_dec_eq(_: *mut lean_object, _: *mut lean_object) -> u8;
    fn lean_array_set(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_usize_shift_right(_: usize, _: usize) -> usize;
    fn l_Lean_PersistentHashMap_isUnaryNode___redArg(_: *mut lean_object) -> *mut lean_object;
    fn lean_array_get_size(_: *mut lean_object) -> *mut lean_object;
    fn lean_nat_dec_lt(_: *mut lean_object, _: *mut lean_object) -> u8;
    fn lean_array_fget_borrowed(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_nat_add(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_Array_eraseIdx___redArg(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_uint64_of_nat(_: *mut lean_object) -> u64;
    fn lean_uint64_to_usize(_: u64) -> usize;
    fn lean_usize_mul(_: usize, _: usize) -> usize;
    fn lean_array_fget(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_array_fset(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_Lean_PersistentHashMap_mkCollisionNode___redArg(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_usize_add(_: usize, _: usize) -> usize;
    fn lean_array_push(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_Lean_PersistentHashMap_mkEmptyEntries(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_usize_dec_le(_: usize, _: usize) -> u8;
    fn l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(_: *mut lean_object) -> *mut lean_object;
    fn lean_nat_sub(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_Nat_reprFast(_: *mut lean_object) -> *mut lean_object;
    fn lean_string_length(_: *mut lean_object) -> *mut lean_object;
    fn lean_nat_to_int(_: *mut lean_object) -> *mut lean_object;
    fn lean_array_get_borrowed(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_Lean_PersistentHashMap_mkEmptyEntriesArray(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_string_push(_: *mut lean_object, _: u32) -> *mut lean_object;
    fn l_Lean_PersistentHashMap_collectStats___redArg(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_Lean_PersistentHashMap_Stats_toString(_: *mut lean_object) -> *mut lean_object;
}
#[no_mangle] pub static l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__0_value: lean_string_object<3> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [99, 64, 0]};
static mut l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__0: *mut lean_object = core::ptr::addr_of!(l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__1_value: lean_ctor_object<1> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*1 + 0) as u16, m_other: 1, m_tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__0_value) as *mut lean_object] };
static mut l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__1: *mut lean_object = core::ptr::addr_of!(l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__1_value) as *mut lean_object;
#[no_mangle] pub static l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__2_value: lean_string_object<5> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [32, 61, 62, 32, 0]};
static mut l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__2: *mut lean_object = core::ptr::addr_of!(l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__2_value) as *mut lean_object;
#[no_mangle] pub static l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__3_value: lean_ctor_object<1> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*1 + 0) as u16, m_other: 1, m_tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__2_value) as *mut lean_object] };
static mut l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__3: *mut lean_object = core::ptr::addr_of!(l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__3_value) as *mut lean_object;
#[no_mangle] pub static l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__4_value: lean_string_object<2> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__4: *mut lean_object = core::ptr::addr_of!(l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__4_value) as *mut lean_object;
#[no_mangle] pub static l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__5_value: lean_string_object<2> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__5: *mut lean_object = core::ptr::addr_of!(l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__5_value) as *mut lean_object;
static mut l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__6_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__6: *mut lean_object = core::ptr::null_mut();
static mut l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__7_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__7: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__8_value: lean_ctor_object<1> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*1 + 0) as u16, m_other: 1, m_tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__4_value) as *mut lean_object] };
static mut l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__8: *mut lean_object = core::ptr::addr_of!(l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__8_value) as *mut lean_object;
#[no_mangle] pub static l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__9_value: lean_ctor_object<1> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*1 + 0) as u16, m_other: 1, m_tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__5_value) as *mut lean_object] };
static mut l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__9: *mut lean_object = core::ptr::addr_of!(l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__9_value) as *mut lean_object;
#[no_mangle] pub static l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__10_value: lean_string_object<2> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [44, 0]};
static mut l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__10: *mut lean_object = core::ptr::addr_of!(l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__10_value) as *mut lean_object;
#[no_mangle] pub static l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__11_value: lean_ctor_object<1> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*1 + 0) as u16, m_other: 1, m_tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__10_value) as *mut lean_object] };
static mut l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__11: *mut lean_object = core::ptr::addr_of!(l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__11_value) as *mut lean_object;
#[no_mangle] pub static l_formatMap___closed__0_value: lean_string_object<2> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [91, 0]};
static mut l_formatMap___closed__0: *mut lean_object = core::ptr::addr_of!(l_formatMap___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_formatMap___closed__1_value: lean_string_object<2> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l_formatMap___closed__1: *mut lean_object = core::ptr::addr_of!(l_formatMap___closed__1_value) as *mut lean_object;
static mut l_formatMap___closed__2_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_formatMap___closed__2: *mut lean_object = core::ptr::null_mut();
static mut l_formatMap___closed__3_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_formatMap___closed__3: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static l_formatMap___closed__4_value: lean_ctor_object<1> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*1 + 0) as u16, m_other: 1, m_tag: 3 }, m_objs: [core::ptr::addr_of!(l_formatMap___closed__0_value) as *mut lean_object] };
static mut l_formatMap___closed__4: *mut lean_object = core::ptr::addr_of!(l_formatMap___closed__4_value) as *mut lean_object;
#[no_mangle] pub static l_formatMap___closed__5_value: lean_ctor_object<1> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*1 + 0) as u16, m_other: 1, m_tag: 3 }, m_objs: [core::ptr::addr_of!(l_formatMap___closed__1_value) as *mut lean_object] };
static mut l_formatMap___closed__5: *mut lean_object = core::ptr::addr_of!(l_formatMap___closed__5_value) as *mut lean_object;
#[no_mangle] pub static l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__0_spec__0___redArg___closed__0_value: lean_string_object<7> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [60, 110, 117, 108, 108, 62, 0]};
static mut l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__0_spec__0___redArg___closed__0: *mut lean_object = core::ptr::addr_of!(l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__0_spec__0___redArg___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__0_spec__0___redArg___closed__1_value: lean_ctor_object<1> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*1 + 0) as u16, m_other: 1, m_tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__0_spec__0___redArg___closed__0_value) as *mut lean_object] };
static mut l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__0_spec__0___redArg___closed__1: *mut lean_object = core::ptr::addr_of!(l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__0_spec__0___redArg___closed__1_value) as *mut lean_object;
#[no_mangle] pub static l_Lean_PersistentHashMap_stats___at___00checkState_spec__0___redArg___closed__0_value: lean_ctor_object<4> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*4 + 0) as u16, m_other: 4, m_tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut lean_object,((( 0 as usize) << 1) | 1) as *mut lean_object,((( 0 as usize) << 1) | 1) as *mut lean_object,((( 0 as usize) << 1) | 1) as *mut lean_object] };
static mut l_Lean_PersistentHashMap_stats___at___00checkState_spec__0___redArg___closed__0: *mut lean_object = core::ptr::addr_of!(l_Lean_PersistentHashMap_stats___at___00checkState_spec__0___redArg___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_checkState___closed__0_value: lean_string_object<32> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 32, m_capacity: 32, m_length: 31, m_data: [117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 110, 117, 109, 98, 101, 114, 32, 111, 102, 32, 99, 111, 108, 108, 105, 115, 105, 111, 110, 115, 0]};
static mut l_checkState___closed__0: *mut lean_object = core::ptr::addr_of!(l_checkState___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_checkState___closed__1_value: lean_string_object<21> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 109, 97, 120, 32, 100, 101, 112, 116, 104, 0]};
static mut l_checkState___closed__1: *mut lean_object = core::ptr::addr_of!(l_checkState___closed__1_value) as *mut lean_object;
static mut l_Lean_PersistentHashMap_empty___at___00main_spec__0___closed__0_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_PersistentHashMap_empty___at___00main_spec__0___closed__0: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_empty___at___00main_spec__0___closed__1_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_PersistentHashMap_empty___at___00main_spec__0___closed__1: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__1_spec__1___redArg___closed__0_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__1_spec__1___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__1_spec__1___redArg___closed__1_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__1_spec__1___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__1_spec__1___redArg___closed__2_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__1_spec__1___redArg___closed__2: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__0_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__0: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__1_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__1: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__2_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__2: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__3_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__3: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__4_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__4: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__5_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__5: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__6_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__6: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__7_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__7: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__8_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__8: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__9_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__9: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__10_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__10: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub unsafe extern "C" fn _init_l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__6() -> *mut lean_object{
let mut v___x_9_: *mut lean_object = core::ptr::null_mut(); let mut v___x_10_: *mut lean_object = core::ptr::null_mut(); 
v___x_9_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__4;
v___x_10_ = lean_string_length(v___x_9_);
return v___x_10_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__7() -> *mut lean_object{
let mut v___x_11_: *mut lean_object = core::ptr::null_mut(); let mut v___x_12_: *mut lean_object = core::ptr::null_mut(); 
v___x_11_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__6), core::ptr::addr_of_mut!(l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__6_once), _init_l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__6);
v___x_12_ = lean_nat_to_int(v___x_11_);
return v___x_12_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg(mut v_ks_20_: *mut lean_object, mut v_vs_21_: *mut lean_object, mut v_n_22_: *mut lean_object, mut v_j_23_: *mut lean_object, mut v_a_24_: *mut lean_object) -> *mut lean_object{
let mut v_zero_25_: *mut lean_object = core::ptr::null_mut(); let mut v_isZero_26_: u8 = 0; let mut v_one_27_: *mut lean_object = core::ptr::null_mut(); let mut v_n_28_: *mut lean_object = core::ptr::null_mut(); let mut v___x_29_: *mut lean_object = core::ptr::null_mut(); let mut v_k_30_: *mut lean_object = core::ptr::null_mut(); let mut v_v_31_: *mut lean_object = core::ptr::null_mut(); let mut v___y_33_: *mut lean_object = core::ptr::null_mut(); let mut v___x_34_: *mut lean_object = core::ptr::null_mut(); let mut v___x_35_: *mut lean_object = core::ptr::null_mut(); let mut v___x_36_: *mut lean_object = core::ptr::null_mut(); let mut v___x_37_: *mut lean_object = core::ptr::null_mut(); let mut v___x_38_: *mut lean_object = core::ptr::null_mut(); let mut v___x_39_: *mut lean_object = core::ptr::null_mut(); let mut v___x_40_: *mut lean_object = core::ptr::null_mut(); let mut v___x_41_: *mut lean_object = core::ptr::null_mut(); let mut v___x_42_: *mut lean_object = core::ptr::null_mut(); let mut v___x_43_: *mut lean_object = core::ptr::null_mut(); let mut v___x_44_: *mut lean_object = core::ptr::null_mut(); let mut v___x_45_: *mut lean_object = core::ptr::null_mut(); let mut v___x_46_: *mut lean_object = core::ptr::null_mut(); let mut v___x_47_: *mut lean_object = core::ptr::null_mut(); let mut v___x_48_: *mut lean_object = core::ptr::null_mut(); let mut v___x_49_: u8 = 0; let mut v___x_50_: *mut lean_object = core::ptr::null_mut(); let mut v___x_51_: *mut lean_object = core::ptr::null_mut(); let mut v___x_53_: u8 = 0; let mut v___x_54_: *mut lean_object = core::ptr::null_mut(); let mut v___x_55_: *mut lean_object = core::ptr::null_mut(); let mut v___x_56_: *mut lean_object = core::ptr::null_mut(); let mut v___x_57_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v_zero_25_ = lean_unsigned_to_nat(0);
v_isZero_26_ = lean_nat_dec_eq(v_j_23_, v_zero_25_);
if v_isZero_26_ == 1 {
lean_dec(v_j_23_);
return v_a_24_;
} else {
let mut v_one_27_: *mut lean_object = core::ptr::null_mut(); let mut v_n_28_: *mut lean_object = core::ptr::null_mut(); let mut v___x_29_: *mut lean_object = core::ptr::null_mut(); let mut v_k_30_: *mut lean_object = core::ptr::null_mut(); let mut v_v_31_: *mut lean_object = core::ptr::null_mut(); let mut v___y_33_: *mut lean_object = core::ptr::null_mut(); let mut v___x_53_: u8 = 0; 
v_one_27_ = lean_unsigned_to_nat(1);
v_n_28_ = lean_nat_sub(v_j_23_, v_one_27_);
v___x_29_ = lean_nat_sub(v_n_22_, v_j_23_);
lean_dec(v_j_23_);
v_k_30_ = lean_array_fget_borrowed(v_ks_20_, v___x_29_);
v_v_31_ = lean_array_get_borrowed(v_zero_25_, v_vs_21_, v___x_29_);
v___x_53_ = lean_nat_dec_lt(v_zero_25_, v___x_29_);
lean_dec(v___x_29_);
if v___x_53_ == 0 {
v___y_33_ = v_a_24_;
state = 1; continue;
} else {
let mut v___x_54_: *mut lean_object = core::ptr::null_mut(); let mut v___x_55_: *mut lean_object = core::ptr::null_mut(); let mut v___x_56_: *mut lean_object = core::ptr::null_mut(); let mut v___x_57_: *mut lean_object = core::ptr::null_mut(); 
v___x_54_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__11;
v___x_55_ = lean_alloc_ctor(5, 2, (0) as u32);
lean_ctor_set(v___x_55_, 0, v_a_24_);
lean_ctor_set(v___x_55_, 1, v___x_54_);
v___x_56_ = lean_box(1);
v___x_57_ = lean_alloc_ctor(5, 2, (0) as u32);
lean_ctor_set(v___x_57_, 0, v___x_55_);
lean_ctor_set(v___x_57_, 1, v___x_56_);
v___y_33_ = v___x_57_;
state = 1; continue;
}
}
}
1 => {
v___x_34_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__1;
v___x_35_ = lean_alloc_ctor(5, 2, (0) as u32);
lean_ctor_set(v___x_35_, 0, v___y_33_);
lean_ctor_set(v___x_35_, 1, v___x_34_);
lean_inc(v_k_30_);
v___x_36_ = l_Nat_reprFast(v_k_30_);
v___x_37_ = lean_alloc_ctor(3, 1, (0) as u32);
lean_ctor_set(v___x_37_, 0, v___x_36_);
v___x_38_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__3;
v___x_39_ = lean_alloc_ctor(5, 2, (0) as u32);
lean_ctor_set(v___x_39_, 0, v___x_37_);
lean_ctor_set(v___x_39_, 1, v___x_38_);
lean_inc(v_v_31_);
v___x_40_ = l_Nat_reprFast(v_v_31_);
v___x_41_ = lean_alloc_ctor(3, 1, (0) as u32);
lean_ctor_set(v___x_41_, 0, v___x_40_);
v___x_42_ = lean_alloc_ctor(5, 2, (0) as u32);
lean_ctor_set(v___x_42_, 0, v___x_39_);
lean_ctor_set(v___x_42_, 1, v___x_41_);
v___x_43_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__7), core::ptr::addr_of_mut!(l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__7_once), _init_l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__7);
v___x_44_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__8;
v___x_45_ = lean_alloc_ctor(5, 2, (0) as u32);
lean_ctor_set(v___x_45_, 0, v___x_44_);
lean_ctor_set(v___x_45_, 1, v___x_42_);
v___x_46_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__9;
v___x_47_ = lean_alloc_ctor(5, 2, (0) as u32);
lean_ctor_set(v___x_47_, 0, v___x_45_);
lean_ctor_set(v___x_47_, 1, v___x_46_);
v___x_48_ = lean_alloc_ctor(4, 2, (0) as u32);
lean_ctor_set(v___x_48_, 0, v___x_43_);
lean_ctor_set(v___x_48_, 1, v___x_47_);
v___x_49_ = 0;
v___x_50_ = lean_alloc_ctor(6, 1, (1) as u32);
lean_ctor_set(v___x_50_, 0, v___x_48_);
lean_ctor_set_uint8(v___x_50_, (core::mem::size_of::<*mut lean_object>()*1) as u32, v___x_49_);
v___x_51_ = lean_alloc_ctor(5, 2, (0) as u32);
lean_ctor_set(v___x_51_, 0, v___x_35_);
lean_ctor_set(v___x_51_, 1, v___x_50_);
v_j_23_ = v_n_28_;
v_a_24_ = v___x_51_;
state = 0; continue;
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___boxed(mut v_ks_58_: *mut lean_object, mut v_vs_59_: *mut lean_object, mut v_n_60_: *mut lean_object, mut v_j_61_: *mut lean_object, mut v_a_62_: *mut lean_object) -> *mut lean_object{
let mut v_res_63_: *mut lean_object = core::ptr::null_mut(); 
v_res_63_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg(v_ks_58_, v_vs_59_, v_n_60_, v_j_61_, v_a_62_);
lean_dec(v_n_60_);
lean_dec_ref(v_vs_59_);
lean_dec_ref(v_ks_58_);
return v_res_63_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1___redArg(mut v_ks_64_: *mut lean_object, mut v_vs_65_: *mut lean_object, mut v_n_66_: *mut lean_object, mut v_j_67_: *mut lean_object, mut v_a_68_: *mut lean_object) -> *mut lean_object{
let mut v_zero_69_: *mut lean_object = core::ptr::null_mut(); let mut v_isZero_70_: u8 = 0; let mut v_one_71_: *mut lean_object = core::ptr::null_mut(); let mut v_n_72_: *mut lean_object = core::ptr::null_mut(); let mut v___x_73_: *mut lean_object = core::ptr::null_mut(); let mut v_k_74_: *mut lean_object = core::ptr::null_mut(); let mut v_v_75_: *mut lean_object = core::ptr::null_mut(); let mut v___y_77_: *mut lean_object = core::ptr::null_mut(); let mut v___x_78_: *mut lean_object = core::ptr::null_mut(); let mut v___x_79_: *mut lean_object = core::ptr::null_mut(); let mut v___x_80_: *mut lean_object = core::ptr::null_mut(); let mut v___x_81_: *mut lean_object = core::ptr::null_mut(); let mut v___x_82_: *mut lean_object = core::ptr::null_mut(); let mut v___x_83_: *mut lean_object = core::ptr::null_mut(); let mut v___x_84_: *mut lean_object = core::ptr::null_mut(); let mut v___x_85_: *mut lean_object = core::ptr::null_mut(); let mut v___x_86_: *mut lean_object = core::ptr::null_mut(); let mut v___x_87_: *mut lean_object = core::ptr::null_mut(); let mut v___x_88_: *mut lean_object = core::ptr::null_mut(); let mut v___x_89_: *mut lean_object = core::ptr::null_mut(); let mut v___x_90_: *mut lean_object = core::ptr::null_mut(); let mut v___x_91_: *mut lean_object = core::ptr::null_mut(); let mut v___x_92_: *mut lean_object = core::ptr::null_mut(); let mut v___x_93_: u8 = 0; let mut v___x_94_: *mut lean_object = core::ptr::null_mut(); let mut v___x_95_: *mut lean_object = core::ptr::null_mut(); let mut v___x_96_: *mut lean_object = core::ptr::null_mut(); let mut v___x_97_: u8 = 0; let mut v___x_98_: *mut lean_object = core::ptr::null_mut(); let mut v___x_99_: *mut lean_object = core::ptr::null_mut(); let mut v___x_100_: *mut lean_object = core::ptr::null_mut(); let mut v___x_101_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v_zero_69_ = lean_unsigned_to_nat(0);
v_isZero_70_ = lean_nat_dec_eq(v_j_67_, v_zero_69_);
if v_isZero_70_ == 1 {
return v_a_68_;
} else {
let mut v_one_71_: *mut lean_object = core::ptr::null_mut(); let mut v_n_72_: *mut lean_object = core::ptr::null_mut(); let mut v___x_73_: *mut lean_object = core::ptr::null_mut(); let mut v_k_74_: *mut lean_object = core::ptr::null_mut(); let mut v_v_75_: *mut lean_object = core::ptr::null_mut(); let mut v___y_77_: *mut lean_object = core::ptr::null_mut(); let mut v___x_97_: u8 = 0; 
v_one_71_ = lean_unsigned_to_nat(1);
v_n_72_ = lean_nat_sub(v_j_67_, v_one_71_);
v___x_73_ = lean_nat_sub(v_n_66_, v_j_67_);
v_k_74_ = lean_array_fget_borrowed(v_ks_64_, v___x_73_);
v_v_75_ = lean_array_get_borrowed(v_zero_69_, v_vs_65_, v___x_73_);
v___x_97_ = lean_nat_dec_lt(v_zero_69_, v___x_73_);
lean_dec(v___x_73_);
if v___x_97_ == 0 {
v___y_77_ = v_a_68_;
state = 1; continue;
} else {
let mut v___x_98_: *mut lean_object = core::ptr::null_mut(); let mut v___x_99_: *mut lean_object = core::ptr::null_mut(); let mut v___x_100_: *mut lean_object = core::ptr::null_mut(); let mut v___x_101_: *mut lean_object = core::ptr::null_mut(); 
v___x_98_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__11;
v___x_99_ = lean_alloc_ctor(5, 2, (0) as u32);
lean_ctor_set(v___x_99_, 0, v_a_68_);
lean_ctor_set(v___x_99_, 1, v___x_98_);
v___x_100_ = lean_box(1);
v___x_101_ = lean_alloc_ctor(5, 2, (0) as u32);
lean_ctor_set(v___x_101_, 0, v___x_99_);
lean_ctor_set(v___x_101_, 1, v___x_100_);
v___y_77_ = v___x_101_;
state = 1; continue;
}
}
}
1 => {
v___x_78_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__1;
v___x_79_ = lean_alloc_ctor(5, 2, (0) as u32);
lean_ctor_set(v___x_79_, 0, v___y_77_);
lean_ctor_set(v___x_79_, 1, v___x_78_);
lean_inc(v_k_74_);
v___x_80_ = l_Nat_reprFast(v_k_74_);
v___x_81_ = lean_alloc_ctor(3, 1, (0) as u32);
lean_ctor_set(v___x_81_, 0, v___x_80_);
v___x_82_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__3;
v___x_83_ = lean_alloc_ctor(5, 2, (0) as u32);
lean_ctor_set(v___x_83_, 0, v___x_81_);
lean_ctor_set(v___x_83_, 1, v___x_82_);
lean_inc(v_v_75_);
v___x_84_ = l_Nat_reprFast(v_v_75_);
v___x_85_ = lean_alloc_ctor(3, 1, (0) as u32);
lean_ctor_set(v___x_85_, 0, v___x_84_);
v___x_86_ = lean_alloc_ctor(5, 2, (0) as u32);
lean_ctor_set(v___x_86_, 0, v___x_83_);
lean_ctor_set(v___x_86_, 1, v___x_85_);
v___x_87_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__7), core::ptr::addr_of_mut!(l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__7_once), _init_l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__7);
v___x_88_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__8;
v___x_89_ = lean_alloc_ctor(5, 2, (0) as u32);
lean_ctor_set(v___x_89_, 0, v___x_88_);
lean_ctor_set(v___x_89_, 1, v___x_86_);
v___x_90_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__9;
v___x_91_ = lean_alloc_ctor(5, 2, (0) as u32);
lean_ctor_set(v___x_91_, 0, v___x_89_);
lean_ctor_set(v___x_91_, 1, v___x_90_);
v___x_92_ = lean_alloc_ctor(4, 2, (0) as u32);
lean_ctor_set(v___x_92_, 0, v___x_87_);
lean_ctor_set(v___x_92_, 1, v___x_91_);
v___x_93_ = 0;
v___x_94_ = lean_alloc_ctor(6, 1, (1) as u32);
lean_ctor_set(v___x_94_, 0, v___x_92_);
lean_ctor_set_uint8(v___x_94_, (core::mem::size_of::<*mut lean_object>()*1) as u32, v___x_93_);
v___x_95_ = lean_alloc_ctor(5, 2, (0) as u32);
lean_ctor_set(v___x_95_, 0, v___x_79_);
lean_ctor_set(v___x_95_, 1, v___x_94_);
v___x_96_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg(v_ks_64_, v_vs_65_, v_n_66_, v_n_72_, v___x_95_);
return v___x_96_;
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1___redArg___boxed(mut v_ks_102_: *mut lean_object, mut v_vs_103_: *mut lean_object, mut v_n_104_: *mut lean_object, mut v_j_105_: *mut lean_object, mut v_a_106_: *mut lean_object) -> *mut lean_object{
let mut v_res_107_: *mut lean_object = core::ptr::null_mut(); 
v_res_107_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1___redArg(v_ks_102_, v_vs_103_, v_n_104_, v_j_105_, v_a_106_);
lean_dec(v_j_105_);
lean_dec(v_n_104_);
lean_dec_ref(v_vs_103_);
lean_dec_ref(v_ks_102_);
return v_res_107_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_formatMap___closed__2() -> *mut lean_object{
let mut v___x_110_: *mut lean_object = core::ptr::null_mut(); let mut v___x_111_: *mut lean_object = core::ptr::null_mut(); 
v___x_110_ = l_formatMap___closed__0;
v___x_111_ = lean_string_length(v___x_110_);
return v___x_111_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_formatMap___closed__3() -> *mut lean_object{
let mut v___x_112_: *mut lean_object = core::ptr::null_mut(); let mut v___x_113_: *mut lean_object = core::ptr::null_mut(); 
v___x_112_ = lean_obj_once(core::ptr::addr_of_mut!(l_formatMap___closed__2), core::ptr::addr_of_mut!(l_formatMap___closed__2_once), _init_l_formatMap___closed__2);
v___x_113_ = lean_nat_to_int(v___x_112_);
return v___x_113_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__0_spec__0___redArg(mut v_es_121_: *mut lean_object, mut v_n_122_: *mut lean_object, mut v_j_123_: *mut lean_object, mut v_a_124_: *mut lean_object) -> *mut lean_object{
let mut v_zero_125_: *mut lean_object = core::ptr::null_mut(); let mut v_isZero_126_: u8 = 0; let mut v_one_127_: *mut lean_object = core::ptr::null_mut(); let mut v_n_128_: *mut lean_object = core::ptr::null_mut(); let mut v___x_129_: *mut lean_object = core::ptr::null_mut(); let mut v_entry_130_: *mut lean_object = core::ptr::null_mut(); let mut v___y_132_: *mut lean_object = core::ptr::null_mut(); let mut v_key_133_: *mut lean_object = core::ptr::null_mut(); let mut v_val_134_: *mut lean_object = core::ptr::null_mut(); let mut v___x_136_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_137_: u8 = 0; let mut v___x_138_: *mut lean_object = core::ptr::null_mut(); let mut v___x_139_: *mut lean_object = core::ptr::null_mut(); let mut v___x_140_: *mut lean_object = core::ptr::null_mut(); let mut v___x_142_: *mut lean_object = core::ptr::null_mut(); let mut v___x_143_: *mut lean_object = core::ptr::null_mut(); let mut v___x_144_: *mut lean_object = core::ptr::null_mut(); let mut v___x_145_: *mut lean_object = core::ptr::null_mut(); let mut v___x_146_: *mut lean_object = core::ptr::null_mut(); let mut v___x_147_: *mut lean_object = core::ptr::null_mut(); let mut v___x_148_: *mut lean_object = core::ptr::null_mut(); let mut v___x_149_: *mut lean_object = core::ptr::null_mut(); let mut v___x_150_: *mut lean_object = core::ptr::null_mut(); let mut v___x_151_: *mut lean_object = core::ptr::null_mut(); let mut v___x_152_: u8 = 0; let mut v___x_153_: *mut lean_object = core::ptr::null_mut(); let mut v___x_154_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_156_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_157_: u8 = 0; let mut v_node_158_: *mut lean_object = core::ptr::null_mut(); let mut v___x_159_: *mut lean_object = core::ptr::null_mut(); let mut v___x_160_: *mut lean_object = core::ptr::null_mut(); let mut v___x_162_: *mut lean_object = core::ptr::null_mut(); let mut v___x_163_: *mut lean_object = core::ptr::null_mut(); let mut v___x_165_: u8 = 0; let mut v___x_166_: *mut lean_object = core::ptr::null_mut(); let mut v___x_167_: *mut lean_object = core::ptr::null_mut(); let mut v___x_168_: *mut lean_object = core::ptr::null_mut(); let mut v___x_169_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v_zero_125_ = lean_unsigned_to_nat(0);
v_isZero_126_ = lean_nat_dec_eq(v_j_123_, v_zero_125_);
if v_isZero_126_ == 1 {
lean_dec(v_j_123_);
return v_a_124_;
} else {
let mut v_one_127_: *mut lean_object = core::ptr::null_mut(); let mut v_n_128_: *mut lean_object = core::ptr::null_mut(); let mut v___x_129_: *mut lean_object = core::ptr::null_mut(); let mut v_entry_130_: *mut lean_object = core::ptr::null_mut(); let mut v___y_132_: *mut lean_object = core::ptr::null_mut(); let mut v___x_165_: u8 = 0; 
v_one_127_ = lean_unsigned_to_nat(1);
v_n_128_ = lean_nat_sub(v_j_123_, v_one_127_);
v___x_129_ = lean_nat_sub(v_n_122_, v_j_123_);
lean_dec(v_j_123_);
v_entry_130_ = lean_array_fget(v_es_121_, v___x_129_);
v___x_165_ = lean_nat_dec_lt(v_zero_125_, v___x_129_);
lean_dec(v___x_129_);
if v___x_165_ == 0 {
v___y_132_ = v_a_124_;
state = 1; continue;
} else {
let mut v___x_166_: *mut lean_object = core::ptr::null_mut(); let mut v___x_167_: *mut lean_object = core::ptr::null_mut(); let mut v___x_168_: *mut lean_object = core::ptr::null_mut(); let mut v___x_169_: *mut lean_object = core::ptr::null_mut(); 
v___x_166_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__11;
v___x_167_ = lean_alloc_ctor(5, 2, (0) as u32);
lean_ctor_set(v___x_167_, 0, v_a_124_);
lean_ctor_set(v___x_167_, 1, v___x_166_);
v___x_168_ = lean_box(1);
v___x_169_ = lean_alloc_ctor(5, 2, (0) as u32);
lean_ctor_set(v___x_169_, 0, v___x_167_);
lean_ctor_set(v___x_169_, 1, v___x_168_);
v___y_132_ = v___x_169_;
state = 1; continue;
}
}
}
1 => {
match lean_obj_tag(v_entry_130_)
{
0 => {
let mut v_key_133_: *mut lean_object = core::ptr::null_mut(); let mut v_val_134_: *mut lean_object = core::ptr::null_mut(); let mut v___x_136_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_137_: u8 = 0; let mut v_isSharedCheck_157_: u8 = 0; 
v_key_133_ = lean_ctor_get(v_entry_130_, 0);
v_val_134_ = lean_ctor_get(v_entry_130_, 1);
v_isSharedCheck_157_ = (!lean_is_exclusive(v_entry_130_)) as u8;
if v_isSharedCheck_157_ == 0 {
v___x_136_ = v_entry_130_;
v_isShared_137_ = v_isSharedCheck_157_;
state = 2; continue;
} else {
lean_inc(v_val_134_);
lean_inc(v_key_133_);
lean_dec(v_entry_130_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_157_;
state = 2; continue;
}
}
1 => {
let mut v_node_158_: *mut lean_object = core::ptr::null_mut(); let mut v___x_159_: *mut lean_object = core::ptr::null_mut(); let mut v___x_160_: *mut lean_object = core::ptr::null_mut(); 
v_node_158_ = lean_ctor_get(v_entry_130_, 0);
lean_inc(v_node_158_);
lean_dec_ref_known(v_entry_130_, 1);
v___x_159_ = l_formatMap(v_node_158_);
v___x_160_ = lean_alloc_ctor(5, 2, (0) as u32);
lean_ctor_set(v___x_160_, 0, v___y_132_);
lean_ctor_set(v___x_160_, 1, v___x_159_);
v_j_123_ = v_n_128_;
v_a_124_ = v___x_160_;
state = 0; continue;
}
_ => {
let mut v___x_162_: *mut lean_object = core::ptr::null_mut(); let mut v___x_163_: *mut lean_object = core::ptr::null_mut(); 
v___x_162_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__0_spec__0___redArg___closed__1;
v___x_163_ = lean_alloc_ctor(5, 2, (0) as u32);
lean_ctor_set(v___x_163_, 0, v___y_132_);
lean_ctor_set(v___x_163_, 1, v___x_162_);
v_j_123_ = v_n_128_;
v_a_124_ = v___x_163_;
state = 0; continue;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__0___redArg(mut v_es_170_: *mut lean_object, mut v_n_171_: *mut lean_object, mut v_j_172_: *mut lean_object, mut v_a_173_: *mut lean_object) -> *mut lean_object{
let mut v_zero_174_: *mut lean_object = core::ptr::null_mut(); let mut v_isZero_175_: u8 = 0; let mut v_one_176_: *mut lean_object = core::ptr::null_mut(); let mut v_n_177_: *mut lean_object = core::ptr::null_mut(); let mut v___x_178_: *mut lean_object = core::ptr::null_mut(); let mut v_entry_179_: *mut lean_object = core::ptr::null_mut(); let mut v___y_181_: *mut lean_object = core::ptr::null_mut(); let mut v_key_182_: *mut lean_object = core::ptr::null_mut(); let mut v_val_183_: *mut lean_object = core::ptr::null_mut(); let mut v___x_185_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_186_: u8 = 0; let mut v___x_187_: *mut lean_object = core::ptr::null_mut(); let mut v___x_188_: *mut lean_object = core::ptr::null_mut(); let mut v___x_189_: *mut lean_object = core::ptr::null_mut(); let mut v___x_191_: *mut lean_object = core::ptr::null_mut(); let mut v___x_192_: *mut lean_object = core::ptr::null_mut(); let mut v___x_193_: *mut lean_object = core::ptr::null_mut(); let mut v___x_194_: *mut lean_object = core::ptr::null_mut(); let mut v___x_195_: *mut lean_object = core::ptr::null_mut(); let mut v___x_196_: *mut lean_object = core::ptr::null_mut(); let mut v___x_197_: *mut lean_object = core::ptr::null_mut(); let mut v___x_198_: *mut lean_object = core::ptr::null_mut(); let mut v___x_199_: *mut lean_object = core::ptr::null_mut(); let mut v___x_200_: *mut lean_object = core::ptr::null_mut(); let mut v___x_201_: u8 = 0; let mut v___x_202_: *mut lean_object = core::ptr::null_mut(); let mut v___x_203_: *mut lean_object = core::ptr::null_mut(); let mut v___x_204_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_205_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_206_: u8 = 0; let mut v_node_207_: *mut lean_object = core::ptr::null_mut(); let mut v___x_208_: *mut lean_object = core::ptr::null_mut(); let mut v___x_209_: *mut lean_object = core::ptr::null_mut(); let mut v___x_210_: *mut lean_object = core::ptr::null_mut(); let mut v___x_211_: *mut lean_object = core::ptr::null_mut(); let mut v___x_212_: *mut lean_object = core::ptr::null_mut(); let mut v___x_213_: *mut lean_object = core::ptr::null_mut(); let mut v___x_214_: u8 = 0; let mut v___x_215_: *mut lean_object = core::ptr::null_mut(); let mut v___x_216_: *mut lean_object = core::ptr::null_mut(); let mut v___x_217_: *mut lean_object = core::ptr::null_mut(); let mut v___x_218_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v_zero_174_ = lean_unsigned_to_nat(0);
v_isZero_175_ = lean_nat_dec_eq(v_j_172_, v_zero_174_);
if v_isZero_175_ == 1 {
return v_a_173_;
} else {
let mut v_one_176_: *mut lean_object = core::ptr::null_mut(); let mut v_n_177_: *mut lean_object = core::ptr::null_mut(); let mut v___x_178_: *mut lean_object = core::ptr::null_mut(); let mut v_entry_179_: *mut lean_object = core::ptr::null_mut(); let mut v___y_181_: *mut lean_object = core::ptr::null_mut(); let mut v___x_214_: u8 = 0; 
v_one_176_ = lean_unsigned_to_nat(1);
v_n_177_ = lean_nat_sub(v_j_172_, v_one_176_);
v___x_178_ = lean_nat_sub(v_n_171_, v_j_172_);
v_entry_179_ = lean_array_fget(v_es_170_, v___x_178_);
v___x_214_ = lean_nat_dec_lt(v_zero_174_, v___x_178_);
lean_dec(v___x_178_);
if v___x_214_ == 0 {
v___y_181_ = v_a_173_;
state = 1; continue;
} else {
let mut v___x_215_: *mut lean_object = core::ptr::null_mut(); let mut v___x_216_: *mut lean_object = core::ptr::null_mut(); let mut v___x_217_: *mut lean_object = core::ptr::null_mut(); let mut v___x_218_: *mut lean_object = core::ptr::null_mut(); 
v___x_215_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__11;
v___x_216_ = lean_alloc_ctor(5, 2, (0) as u32);
lean_ctor_set(v___x_216_, 0, v_a_173_);
lean_ctor_set(v___x_216_, 1, v___x_215_);
v___x_217_ = lean_box(1);
v___x_218_ = lean_alloc_ctor(5, 2, (0) as u32);
lean_ctor_set(v___x_218_, 0, v___x_216_);
lean_ctor_set(v___x_218_, 1, v___x_217_);
v___y_181_ = v___x_218_;
state = 1; continue;
}
}
}
1 => {
match lean_obj_tag(v_entry_179_)
{
0 => {
let mut v_key_182_: *mut lean_object = core::ptr::null_mut(); let mut v_val_183_: *mut lean_object = core::ptr::null_mut(); let mut v___x_185_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_186_: u8 = 0; let mut v_isSharedCheck_206_: u8 = 0; 
v_key_182_ = lean_ctor_get(v_entry_179_, 0);
v_val_183_ = lean_ctor_get(v_entry_179_, 1);
v_isSharedCheck_206_ = (!lean_is_exclusive(v_entry_179_)) as u8;
if v_isSharedCheck_206_ == 0 {
v___x_185_ = v_entry_179_;
v_isShared_186_ = v_isSharedCheck_206_;
state = 2; continue;
} else {
lean_inc(v_val_183_);
lean_inc(v_key_182_);
lean_dec(v_entry_179_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_206_;
state = 2; continue;
}
}
1 => {
let mut v_node_207_: *mut lean_object = core::ptr::null_mut(); let mut v___x_208_: *mut lean_object = core::ptr::null_mut(); let mut v___x_209_: *mut lean_object = core::ptr::null_mut(); let mut v___x_210_: *mut lean_object = core::ptr::null_mut(); 
v_node_207_ = lean_ctor_get(v_entry_179_, 0);
lean_inc(v_node_207_);
lean_dec_ref_known(v_entry_179_, 1);
v___x_208_ = l_formatMap(v_node_207_);
v___x_209_ = lean_alloc_ctor(5, 2, (0) as u32);
lean_ctor_set(v___x_209_, 0, v___y_181_);
lean_ctor_set(v___x_209_, 1, v___x_208_);
v___x_210_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__0_spec__0___redArg(v_es_170_, v_n_171_, v_n_177_, v___x_209_);
return v___x_210_;
}
_ => {
let mut v___x_211_: *mut lean_object = core::ptr::null_mut(); let mut v___x_212_: *mut lean_object = core::ptr::null_mut(); let mut v___x_213_: *mut lean_object = core::ptr::null_mut(); 
v___x_211_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__0_spec__0___redArg___closed__1;
v___x_212_ = lean_alloc_ctor(5, 2, (0) as u32);
lean_ctor_set(v___x_212_, 0, v___y_181_);
lean_ctor_set(v___x_212_, 1, v___x_211_);
v___x_213_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__0_spec__0___redArg(v_es_170_, v_n_171_, v_n_177_, v___x_212_);
return v___x_213_;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_formatMap(mut v_x_219_: *mut lean_object) -> *mut lean_object{
let mut v_es_220_: *mut lean_object = core::ptr::null_mut(); let mut v___x_221_: *mut lean_object = core::ptr::null_mut(); let mut v___x_222_: *mut lean_object = core::ptr::null_mut(); let mut v___x_223_: *mut lean_object = core::ptr::null_mut(); let mut v___x_224_: *mut lean_object = core::ptr::null_mut(); let mut v___x_225_: *mut lean_object = core::ptr::null_mut(); let mut v___x_226_: *mut lean_object = core::ptr::null_mut(); let mut v___x_227_: *mut lean_object = core::ptr::null_mut(); let mut v___x_228_: *mut lean_object = core::ptr::null_mut(); let mut v___x_229_: *mut lean_object = core::ptr::null_mut(); let mut v___x_230_: u8 = 0; let mut v___x_231_: *mut lean_object = core::ptr::null_mut(); let mut v_ks_232_: *mut lean_object = core::ptr::null_mut(); let mut v_vs_233_: *mut lean_object = core::ptr::null_mut(); let mut v___x_235_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_236_: u8 = 0; let mut v___x_237_: *mut lean_object = core::ptr::null_mut(); let mut v___x_238_: *mut lean_object = core::ptr::null_mut(); let mut v___x_239_: *mut lean_object = core::ptr::null_mut(); let mut v___x_240_: *mut lean_object = core::ptr::null_mut(); let mut v___x_241_: *mut lean_object = core::ptr::null_mut(); let mut v___x_243_: *mut lean_object = core::ptr::null_mut(); let mut v___x_244_: *mut lean_object = core::ptr::null_mut(); let mut v___x_245_: *mut lean_object = core::ptr::null_mut(); let mut v___x_246_: *mut lean_object = core::ptr::null_mut(); let mut v___x_247_: u8 = 0; let mut v___x_248_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_249_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_250_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_x_219_) == 0 {
let mut v_es_220_: *mut lean_object = core::ptr::null_mut(); let mut v___x_221_: *mut lean_object = core::ptr::null_mut(); let mut v___x_222_: *mut lean_object = core::ptr::null_mut(); let mut v___x_223_: *mut lean_object = core::ptr::null_mut(); let mut v___x_224_: *mut lean_object = core::ptr::null_mut(); let mut v___x_225_: *mut lean_object = core::ptr::null_mut(); let mut v___x_226_: *mut lean_object = core::ptr::null_mut(); let mut v___x_227_: *mut lean_object = core::ptr::null_mut(); let mut v___x_228_: *mut lean_object = core::ptr::null_mut(); let mut v___x_229_: *mut lean_object = core::ptr::null_mut(); let mut v___x_230_: u8 = 0; let mut v___x_231_: *mut lean_object = core::ptr::null_mut(); 
v_es_220_ = lean_ctor_get(v_x_219_, 0);
lean_inc_ref(v_es_220_);
lean_dec_ref_known(v_x_219_, 1);
v___x_221_ = lean_array_get_size(v_es_220_);
v___x_222_ = lean_box(0);
v___x_223_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__0___redArg(v_es_220_, v___x_221_, v___x_221_, v___x_222_);
lean_dec_ref(v_es_220_);
v___x_224_ = lean_obj_once(core::ptr::addr_of_mut!(l_formatMap___closed__3), core::ptr::addr_of_mut!(l_formatMap___closed__3_once), _init_l_formatMap___closed__3);
v___x_225_ = l_formatMap___closed__4;
v___x_226_ = lean_alloc_ctor(5, 2, (0) as u32);
lean_ctor_set(v___x_226_, 0, v___x_225_);
lean_ctor_set(v___x_226_, 1, v___x_223_);
v___x_227_ = l_formatMap___closed__5;
v___x_228_ = lean_alloc_ctor(5, 2, (0) as u32);
lean_ctor_set(v___x_228_, 0, v___x_226_);
lean_ctor_set(v___x_228_, 1, v___x_227_);
v___x_229_ = lean_alloc_ctor(4, 2, (0) as u32);
lean_ctor_set(v___x_229_, 0, v___x_224_);
lean_ctor_set(v___x_229_, 1, v___x_228_);
v___x_230_ = 0;
v___x_231_ = lean_alloc_ctor(6, 1, (1) as u32);
lean_ctor_set(v___x_231_, 0, v___x_229_);
lean_ctor_set_uint8(v___x_231_, (core::mem::size_of::<*mut lean_object>()*1) as u32, v___x_230_);
return v___x_231_;
} else {
let mut v_ks_232_: *mut lean_object = core::ptr::null_mut(); let mut v_vs_233_: *mut lean_object = core::ptr::null_mut(); let mut v___x_235_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_236_: u8 = 0; let mut v_isSharedCheck_250_: u8 = 0; 
v_ks_232_ = lean_ctor_get(v_x_219_, 0);
v_vs_233_ = lean_ctor_get(v_x_219_, 1);
v_isSharedCheck_250_ = (!lean_is_exclusive(v_x_219_)) as u8;
if v_isSharedCheck_250_ == 0 {
v___x_235_ = v_x_219_;
v_isShared_236_ = v_isSharedCheck_250_;
state = 1; continue;
} else {
lean_inc(v_vs_233_);
lean_inc(v_ks_232_);
lean_dec(v_x_219_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_250_;
state = 1; continue;
}
}
}
1 => {
v___x_237_ = lean_array_get_size(v_ks_232_);
v___x_238_ = lean_box(0);
v___x_239_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1___redArg(v_ks_232_, v_vs_233_, v___x_237_, v___x_237_, v___x_238_);
lean_dec_ref(v_vs_233_);
lean_dec_ref(v_ks_232_);
v___x_240_ = lean_obj_once(core::ptr::addr_of_mut!(l_formatMap___closed__3), core::ptr::addr_of_mut!(l_formatMap___closed__3_once), _init_l_formatMap___closed__3);
v___x_241_ = l_formatMap___closed__4;
if v_isShared_236_ == 0 {
lean_ctor_set_tag(v___x_235_, 5);
lean_ctor_set(v___x_235_, 1, v___x_239_);
lean_ctor_set(v___x_235_, 0, v___x_241_);
v___x_243_ = v___x_235_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_249_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_249_ = lean_alloc_ctor(5, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v___x_241_);
lean_ctor_set(v_reuseFailAlloc_249_, 1, v___x_239_);
v___x_243_ = v_reuseFailAlloc_249_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__0_spec__0___redArg___boxed(mut v_es_251_: *mut lean_object, mut v_n_252_: *mut lean_object, mut v_j_253_: *mut lean_object, mut v_a_254_: *mut lean_object) -> *mut lean_object{
let mut v_res_255_: *mut lean_object = core::ptr::null_mut(); 
v_res_255_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__0_spec__0___redArg(v_es_251_, v_n_252_, v_j_253_, v_a_254_);
lean_dec(v_n_252_);
lean_dec_ref(v_es_251_);
return v_res_255_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__0___redArg___boxed(mut v_es_256_: *mut lean_object, mut v_n_257_: *mut lean_object, mut v_j_258_: *mut lean_object, mut v_a_259_: *mut lean_object) -> *mut lean_object{
let mut v_res_260_: *mut lean_object = core::ptr::null_mut(); 
v_res_260_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__0___redArg(v_es_256_, v_n_257_, v_j_258_, v_a_259_);
lean_dec(v_j_258_);
lean_dec(v_n_257_);
lean_dec_ref(v_es_256_);
return v_res_260_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__0(mut v_es_261_: *mut lean_object, mut v_n_262_: *mut lean_object, mut v_j_263_: *mut lean_object, mut v_a_264_: *mut lean_object, mut v_a_265_: *mut lean_object) -> *mut lean_object{
let mut v___x_266_: *mut lean_object = core::ptr::null_mut(); 
v___x_266_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__0___redArg(v_es_261_, v_n_262_, v_j_263_, v_a_265_);
return v___x_266_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__0___boxed(mut v_es_267_: *mut lean_object, mut v_n_268_: *mut lean_object, mut v_j_269_: *mut lean_object, mut v_a_270_: *mut lean_object, mut v_a_271_: *mut lean_object) -> *mut lean_object{
let mut v_res_272_: *mut lean_object = core::ptr::null_mut(); 
v_res_272_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__0(v_es_267_, v_n_268_, v_j_269_, v_a_270_, v_a_271_);
lean_dec(v_j_269_);
lean_dec(v_n_268_);
lean_dec_ref(v_es_267_);
return v_res_272_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1(mut v_ks_273_: *mut lean_object, mut v_vs_274_: *mut lean_object, mut v_n_275_: *mut lean_object, mut v_j_276_: *mut lean_object, mut v_a_277_: *mut lean_object, mut v_a_278_: *mut lean_object) -> *mut lean_object{
let mut v___x_279_: *mut lean_object = core::ptr::null_mut(); 
v___x_279_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1___redArg(v_ks_273_, v_vs_274_, v_n_275_, v_j_276_, v_a_278_);
return v___x_279_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1___boxed(mut v_ks_280_: *mut lean_object, mut v_vs_281_: *mut lean_object, mut v_n_282_: *mut lean_object, mut v_j_283_: *mut lean_object, mut v_a_284_: *mut lean_object, mut v_a_285_: *mut lean_object) -> *mut lean_object{
let mut v_res_286_: *mut lean_object = core::ptr::null_mut(); 
v_res_286_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1(v_ks_280_, v_vs_281_, v_n_282_, v_j_283_, v_a_284_, v_a_285_);
lean_dec(v_j_283_);
lean_dec(v_n_282_);
lean_dec_ref(v_vs_281_);
lean_dec_ref(v_ks_280_);
return v_res_286_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__0_spec__0(mut v_es_287_: *mut lean_object, mut v_n_288_: *mut lean_object, mut v_j_289_: *mut lean_object, mut v_a_290_: *mut lean_object, mut v_a_291_: *mut lean_object) -> *mut lean_object{
let mut v___x_292_: *mut lean_object = core::ptr::null_mut(); 
v___x_292_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__0_spec__0___redArg(v_es_287_, v_n_288_, v_j_289_, v_a_291_);
return v___x_292_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__0_spec__0___boxed(mut v_es_293_: *mut lean_object, mut v_n_294_: *mut lean_object, mut v_j_295_: *mut lean_object, mut v_a_296_: *mut lean_object, mut v_a_297_: *mut lean_object) -> *mut lean_object{
let mut v_res_298_: *mut lean_object = core::ptr::null_mut(); 
v_res_298_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__0_spec__0(v_es_293_, v_n_294_, v_j_295_, v_a_296_, v_a_297_);
lean_dec(v_n_294_);
lean_dec_ref(v_es_293_);
return v_res_298_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2(mut v_ks_299_: *mut lean_object, mut v_vs_300_: *mut lean_object, mut v_n_301_: *mut lean_object, mut v_j_302_: *mut lean_object, mut v_a_303_: *mut lean_object, mut v_a_304_: *mut lean_object) -> *mut lean_object{
let mut v___x_305_: *mut lean_object = core::ptr::null_mut(); 
v___x_305_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg(v_ks_299_, v_vs_300_, v_n_301_, v_j_302_, v_a_304_);
return v___x_305_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___boxed(mut v_ks_306_: *mut lean_object, mut v_vs_307_: *mut lean_object, mut v_n_308_: *mut lean_object, mut v_j_309_: *mut lean_object, mut v_a_310_: *mut lean_object, mut v_a_311_: *mut lean_object) -> *mut lean_object{
let mut v_res_312_: *mut lean_object = core::ptr::null_mut(); 
v_res_312_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2(v_ks_306_, v_vs_307_, v_n_308_, v_j_309_, v_a_310_, v_a_311_);
lean_dec(v_n_308_);
lean_dec_ref(v_vs_307_);
lean_dec_ref(v_ks_306_);
return v_res_312_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_stats___at___00checkState_spec__0___redArg(mut v_m_315_: *mut lean_object) -> *mut lean_object{
let mut v___x_316_: *mut lean_object = core::ptr::null_mut(); let mut v___x_317_: *mut lean_object = core::ptr::null_mut(); let mut v___x_318_: *mut lean_object = core::ptr::null_mut(); 
v___x_316_ = l_Lean_PersistentHashMap_stats___at___00checkState_spec__0___redArg___closed__0;
v___x_317_ = lean_unsigned_to_nat(1);
v___x_318_ = l_Lean_PersistentHashMap_collectStats___redArg(v_m_315_, v___x_316_, v___x_317_);
return v___x_318_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_stats___at___00checkState_spec__0___redArg___boxed(mut v_m_319_: *mut lean_object) -> *mut lean_object{
let mut v_res_320_: *mut lean_object = core::ptr::null_mut(); 
v_res_320_ = l_Lean_PersistentHashMap_stats___at___00checkState_spec__0___redArg(v_m_319_);
lean_dec_ref(v_m_319_);
return v_res_320_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_stats___at___00checkState_spec__0(mut v_00_u03b2_321_: *mut lean_object, mut v_m_322_: *mut lean_object) -> *mut lean_object{
let mut v___x_323_: *mut lean_object = core::ptr::null_mut(); 
v___x_323_ = l_Lean_PersistentHashMap_stats___at___00checkState_spec__0___redArg(v_m_322_);
return v___x_323_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_stats___at___00checkState_spec__0___boxed(mut v_00_u03b2_324_: *mut lean_object, mut v_m_325_: *mut lean_object) -> *mut lean_object{
let mut v_res_326_: *mut lean_object = core::ptr::null_mut(); 
v_res_326_ = l_Lean_PersistentHashMap_stats___at___00checkState_spec__0(v_00_u03b2_324_, v_m_325_);
lean_dec_ref(v_m_325_);
return v_res_326_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00checkState_spec__1_spec__1(mut v_s_327_: *mut lean_object) -> *mut lean_object{
let mut v___x_329_: *mut lean_object = core::ptr::null_mut(); let mut v_putStr_330_: *mut lean_object = core::ptr::null_mut(); let mut v___x_331_: *mut lean_object = core::ptr::null_mut(); 
v___x_329_ = lean_get_stdout();
v_putStr_330_ = lean_ctor_get(v___x_329_, 4);
lean_inc_ref(v_putStr_330_);
lean_dec_ref(v___x_329_);
v___x_331_ = lean_apply_2(v_putStr_330_, v_s_327_, lean_box(0));
return v___x_331_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00checkState_spec__1_spec__1___boxed(mut v_s_332_: *mut lean_object, mut v_a_333_: *mut lean_object) -> *mut lean_object{
let mut v_res_334_: *mut lean_object = core::ptr::null_mut(); 
v_res_334_ = l_IO_print___at___00IO_println___at___00checkState_spec__1_spec__1(v_s_332_);
return v_res_334_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00checkState_spec__1(mut v_s_335_: *mut lean_object) -> *mut lean_object{
let mut v___x_337_: u32 = 0; let mut v___x_338_: *mut lean_object = core::ptr::null_mut(); let mut v___x_339_: *mut lean_object = core::ptr::null_mut(); 
v___x_337_ = 10;
v___x_338_ = lean_string_push(v_s_335_, v___x_337_);
v___x_339_ = l_IO_print___at___00IO_println___at___00checkState_spec__1_spec__1(v___x_338_);
return v___x_339_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00checkState_spec__1___boxed(mut v_s_340_: *mut lean_object, mut v_a_341_: *mut lean_object) -> *mut lean_object{
let mut v_res_342_: *mut lean_object = core::ptr::null_mut(); 
v_res_342_ = l_IO_println___at___00checkState_spec__1(v_s_340_);
return v_res_342_;
}
#[no_mangle] pub unsafe extern "C" fn l_checkState(mut v_m_345_: *mut lean_object) -> *mut lean_object{
let mut v___x_348_: *mut lean_object = core::ptr::null_mut(); let mut v_numCollisions_349_: *mut lean_object = core::ptr::null_mut(); let mut v___x_350_: *mut lean_object = core::ptr::null_mut(); let mut v___x_351_: u8 = 0; let mut v___x_352_: *mut lean_object = core::ptr::null_mut(); let mut v___x_353_: *mut lean_object = core::ptr::null_mut(); let mut v___x_354_: *mut lean_object = core::ptr::null_mut(); let mut v___x_355_: *mut lean_object = core::ptr::null_mut(); let mut v___x_356_: *mut lean_object = core::ptr::null_mut(); let mut v_maxDepth_357_: *mut lean_object = core::ptr::null_mut(); let mut v___x_358_: *mut lean_object = core::ptr::null_mut(); let mut v___x_359_: u8 = 0; let mut v___x_360_: *mut lean_object = core::ptr::null_mut(); let mut v___x_361_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_356_ = l_Lean_PersistentHashMap_stats___at___00checkState_spec__0___redArg(v_m_345_);
v_maxDepth_357_ = lean_ctor_get(v___x_356_, 3);
lean_inc(v_maxDepth_357_);
lean_dec_ref(v___x_356_);
v___x_358_ = lean_unsigned_to_nat(1);
v___x_359_ = lean_nat_dec_eq(v_maxDepth_357_, v___x_358_);
lean_dec(v_maxDepth_357_);
if v___x_359_ == 0 {
let mut v___x_360_: *mut lean_object = core::ptr::null_mut(); let mut v___x_361_: *mut lean_object = core::ptr::null_mut(); 
v___x_360_ = l_checkState___closed__1;
v___x_361_ = l_IO_println___at___00checkState_spec__1(v___x_360_);
if lean_obj_tag(v___x_361_) == 0 {
lean_dec_ref_known(v___x_361_, 1);
state = 1; continue;
} else {
return v___x_361_;
}
} else {
state = 1; continue;
}
}
1 => {
v___x_348_ = l_Lean_PersistentHashMap_stats___at___00checkState_spec__0___redArg(v_m_345_);
v_numCollisions_349_ = lean_ctor_get(v___x_348_, 2);
lean_inc(v_numCollisions_349_);
lean_dec_ref(v___x_348_);
v___x_350_ = lean_unsigned_to_nat(0);
v___x_351_ = lean_nat_dec_eq(v_numCollisions_349_, v___x_350_);
lean_dec(v_numCollisions_349_);
if v___x_351_ == 0 {
let mut v___x_352_: *mut lean_object = core::ptr::null_mut(); let mut v___x_353_: *mut lean_object = core::ptr::null_mut(); 
v___x_352_ = l_checkState___closed__0;
v___x_353_ = l_IO_println___at___00checkState_spec__1(v___x_352_);
return v___x_353_;
} else {
let mut v___x_354_: *mut lean_object = core::ptr::null_mut(); let mut v___x_355_: *mut lean_object = core::ptr::null_mut(); 
v___x_354_ = lean_box(0);
v___x_355_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_355_, 0, v___x_354_);
return v___x_355_;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_checkState___boxed(mut v_m_362_: *mut lean_object, mut v_a_363_: *mut lean_object) -> *mut lean_object{
let mut v_res_364_: *mut lean_object = core::ptr::null_mut(); 
v_res_364_ = l_checkState(v_m_362_);
lean_dec_ref(v_m_362_);
return v_res_364_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_PersistentHashMap_empty___at___00main_spec__0___closed__0() -> *mut lean_object{
let mut v___x_365_: *mut lean_object = core::ptr::null_mut(); 
v___x_365_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_365_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_PersistentHashMap_empty___at___00main_spec__0___closed__1() -> *mut lean_object{
let mut v___x_366_: *mut lean_object = core::ptr::null_mut(); let mut v___x_367_: *mut lean_object = core::ptr::null_mut(); 
v___x_366_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00main_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00main_spec__0___closed__0_once), _init_l_Lean_PersistentHashMap_empty___at___00main_spec__0___closed__0);
v___x_367_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_367_, 0, v___x_366_);
return v___x_367_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_empty___at___00main_spec__0(mut v_00_u03b2_368_: *mut lean_object) -> *mut lean_object{
let mut v___x_369_: *mut lean_object = core::ptr::null_mut(); 
v___x_369_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00main_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00main_spec__0___closed__1_once), _init_l_Lean_PersistentHashMap_empty___at___00main_spec__0___closed__1);
return v___x_369_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__1_spec__1_spec__2_spec__5___redArg(mut v_x_370_: *mut lean_object, mut v_x_371_: *mut lean_object, mut v_x_372_: *mut lean_object, mut v_x_373_: *mut lean_object) -> *mut lean_object{
let mut v_ks_374_: *mut lean_object = core::ptr::null_mut(); let mut v_vs_375_: *mut lean_object = core::ptr::null_mut(); let mut v___x_377_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_378_: u8 = 0; let mut v___x_379_: *mut lean_object = core::ptr::null_mut(); let mut v___x_380_: u8 = 0; let mut v___x_381_: *mut lean_object = core::ptr::null_mut(); let mut v___x_382_: *mut lean_object = core::ptr::null_mut(); let mut v___x_384_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_385_: *mut lean_object = core::ptr::null_mut(); let mut v_k_x27_386_: *mut lean_object = core::ptr::null_mut(); let mut v___x_387_: u8 = 0; let mut v___x_389_: *mut lean_object = core::ptr::null_mut(); let mut v___x_390_: *mut lean_object = core::ptr::null_mut(); let mut v___x_391_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_393_: *mut lean_object = core::ptr::null_mut(); let mut v___x_394_: *mut lean_object = core::ptr::null_mut(); let mut v___x_395_: *mut lean_object = core::ptr::null_mut(); let mut v___x_397_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_398_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_399_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v_ks_374_ = lean_ctor_get(v_x_370_, 0);
v_vs_375_ = lean_ctor_get(v_x_370_, 1);
v_isSharedCheck_399_ = (!lean_is_exclusive(v_x_370_)) as u8;
if v_isSharedCheck_399_ == 0 {
v___x_377_ = v_x_370_;
v_isShared_378_ = v_isSharedCheck_399_;
state = 1; continue;
} else {
lean_inc(v_vs_375_);
lean_inc(v_ks_374_);
lean_dec(v_x_370_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_399_;
state = 1; continue;
}
}
1 => {
v___x_379_ = lean_array_get_size(v_ks_374_);
v___x_380_ = lean_nat_dec_lt(v_x_371_, v___x_379_);
if v___x_380_ == 0 {
let mut v___x_381_: *mut lean_object = core::ptr::null_mut(); let mut v___x_382_: *mut lean_object = core::ptr::null_mut(); let mut v___x_384_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_x_371_);
v___x_381_ = lean_array_push(v_ks_374_, v_x_372_);
v___x_382_ = lean_array_push(v_vs_375_, v_x_373_);
if v_isShared_378_ == 0 {
lean_ctor_set(v___x_377_, 1, v___x_382_);
lean_ctor_set(v___x_377_, 0, v___x_381_);
v___x_384_ = v___x_377_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_385_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_385_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v___x_381_);
lean_ctor_set(v_reuseFailAlloc_385_, 1, v___x_382_);
v___x_384_ = v_reuseFailAlloc_385_;
state = 2; continue;
}
} else {
let mut v_k_x27_386_: *mut lean_object = core::ptr::null_mut(); let mut v___x_387_: u8 = 0; 
v_k_x27_386_ = lean_array_fget_borrowed(v_ks_374_, v_x_371_);
v___x_387_ = lean_nat_dec_eq(v_x_372_, v_k_x27_386_);
if v___x_387_ == 0 {
let mut v___x_389_: *mut lean_object = core::ptr::null_mut(); 
if v_isShared_378_ == 0 {
v___x_389_ = v___x_377_;
state = 3; continue;
} else {
let mut v_reuseFailAlloc_393_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_393_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v_ks_374_);
lean_ctor_set(v_reuseFailAlloc_393_, 1, v_vs_375_);
v___x_389_ = v_reuseFailAlloc_393_;
state = 3; continue;
}
} else {
let mut v___x_394_: *mut lean_object = core::ptr::null_mut(); let mut v___x_395_: *mut lean_object = core::ptr::null_mut(); let mut v___x_397_: *mut lean_object = core::ptr::null_mut(); 
v___x_394_ = lean_array_fset(v_ks_374_, v_x_371_, v_x_372_);
v___x_395_ = lean_array_fset(v_vs_375_, v_x_371_, v_x_373_);
lean_dec(v_x_371_);
if v_isShared_378_ == 0 {
lean_ctor_set(v___x_377_, 1, v___x_395_);
lean_ctor_set(v___x_377_, 0, v___x_394_);
v___x_397_ = v___x_377_;
state = 4; continue;
} else {
let mut v_reuseFailAlloc_398_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_398_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v___x_394_);
lean_ctor_set(v_reuseFailAlloc_398_, 1, v___x_395_);
v___x_397_ = v_reuseFailAlloc_398_;
state = 4; continue;
}
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__1_spec__1_spec__2___redArg(mut v_n_400_: *mut lean_object, mut v_k_401_: *mut lean_object, mut v_v_402_: *mut lean_object) -> *mut lean_object{
let mut v___x_403_: *mut lean_object = core::ptr::null_mut(); let mut v___x_404_: *mut lean_object = core::ptr::null_mut(); 
v___x_403_ = lean_unsigned_to_nat(0);
v___x_404_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__1_spec__1_spec__2_spec__5___redArg(v_n_400_, v___x_403_, v_k_401_, v_v_402_);
return v___x_404_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__1_spec__1___redArg___closed__0() -> usize{
let mut v___x_405_: usize = 0; let mut v___x_406_: usize = 0; let mut v___x_407_: usize = 0; 
v___x_405_ = 5usize;
v___x_406_ = 1usize;
v___x_407_ = lean_usize_shift_left(v___x_406_, v___x_405_);
return v___x_407_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__1_spec__1___redArg___closed__1() -> usize{
let mut v___x_408_: usize = 0; let mut v___x_409_: usize = 0; let mut v___x_410_: usize = 0; 
v___x_408_ = 1usize;
v___x_409_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__1_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__1_spec__1___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__1_spec__1___redArg___closed__0);
v___x_410_ = lean_usize_sub(v___x_409_, v___x_408_);
return v___x_410_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__1_spec__1___redArg___closed__2() -> *mut lean_object{
let mut v___x_411_: *mut lean_object = core::ptr::null_mut(); 
v___x_411_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_411_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__1_spec__1___redArg(mut v_x_412_: *mut lean_object, mut v_x_413_: usize, mut v_x_414_: usize, mut v_x_415_: *mut lean_object, mut v_x_416_: *mut lean_object) -> *mut lean_object{
let mut v_es_417_: *mut lean_object = core::ptr::null_mut(); let mut v___x_418_: usize = 0; let mut v___x_419_: usize = 0; let mut v___x_420_: usize = 0; let mut v___x_421_: usize = 0; let mut v_j_422_: *mut lean_object = core::ptr::null_mut(); let mut v___x_423_: *mut lean_object = core::ptr::null_mut(); let mut v___x_424_: u8 = 0; let mut v___x_426_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_427_: u8 = 0; let mut v_v_428_: *mut lean_object = core::ptr::null_mut(); let mut v___x_429_: *mut lean_object = core::ptr::null_mut(); let mut v_xs_x27_430_: *mut lean_object = core::ptr::null_mut(); let mut v___y_432_: *mut lean_object = core::ptr::null_mut(); let mut v___x_433_: *mut lean_object = core::ptr::null_mut(); let mut v___x_435_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_436_: *mut lean_object = core::ptr::null_mut(); let mut v_key_437_: *mut lean_object = core::ptr::null_mut(); let mut v_val_438_: *mut lean_object = core::ptr::null_mut(); let mut v___x_440_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_441_: u8 = 0; let mut v___x_442_: u8 = 0; let mut v___x_443_: *mut lean_object = core::ptr::null_mut(); let mut v___x_444_: *mut lean_object = core::ptr::null_mut(); let mut v___x_446_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_447_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_448_: u8 = 0; let mut v_node_449_: *mut lean_object = core::ptr::null_mut(); let mut v___x_451_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_452_: u8 = 0; let mut v___x_453_: usize = 0; let mut v___x_454_: usize = 0; let mut v___x_455_: *mut lean_object = core::ptr::null_mut(); let mut v___x_457_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_458_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_459_: u8 = 0; let mut v___x_460_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_461_: u8 = 0; let mut v_unused_462_: *mut lean_object = core::ptr::null_mut(); let mut v_ks_463_: *mut lean_object = core::ptr::null_mut(); let mut v_vs_464_: *mut lean_object = core::ptr::null_mut(); let mut v___x_466_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_467_: u8 = 0; let mut v___x_469_: *mut lean_object = core::ptr::null_mut(); let mut v_newNode_470_: *mut lean_object = core::ptr::null_mut(); let mut v___y_472_: u8 = 0; let mut v_ks_473_: *mut lean_object = core::ptr::null_mut(); let mut v_vs_474_: *mut lean_object = core::ptr::null_mut(); let mut v___x_475_: *mut lean_object = core::ptr::null_mut(); let mut v___x_476_: *mut lean_object = core::ptr::null_mut(); let mut v___x_477_: *mut lean_object = core::ptr::null_mut(); let mut v___x_478_: usize = 0; let mut v___x_479_: u8 = 0; let mut v___x_480_: *mut lean_object = core::ptr::null_mut(); let mut v___x_481_: *mut lean_object = core::ptr::null_mut(); let mut v___x_482_: u8 = 0; let mut v_reuseFailAlloc_483_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_484_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_x_412_) == 0 {
let mut v_es_417_: *mut lean_object = core::ptr::null_mut(); let mut v___x_418_: usize = 0; let mut v___x_419_: usize = 0; let mut v___x_420_: usize = 0; let mut v___x_421_: usize = 0; let mut v_j_422_: *mut lean_object = core::ptr::null_mut(); let mut v___x_423_: *mut lean_object = core::ptr::null_mut(); let mut v___x_424_: u8 = 0; 
v_es_417_ = lean_ctor_get(v_x_412_, 0);
v___x_418_ = 5usize;
v___x_419_ = 1usize;
v___x_420_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__1_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__1_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__1_spec__1___redArg___closed__1);
v___x_421_ = lean_usize_land(v_x_413_, v___x_420_);
v_j_422_ = lean_usize_to_nat(v___x_421_);
v___x_423_ = lean_array_get_size(v_es_417_);
v___x_424_ = lean_nat_dec_lt(v_j_422_, v___x_423_);
if v___x_424_ == 0 {
lean_dec(v_j_422_);
lean_dec(v_x_416_);
lean_dec(v_x_415_);
return v_x_412_;
} else {
let mut v___x_426_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_427_: u8 = 0; let mut v_isSharedCheck_461_: u8 = 0; 
lean_inc_ref(v_es_417_);
v_isSharedCheck_461_ = (!lean_is_exclusive(v_x_412_)) as u8;
if v_isSharedCheck_461_ == 0 {
let mut v_unused_462_: *mut lean_object = core::ptr::null_mut(); 
v_unused_462_ = lean_ctor_get(v_x_412_, 0);
lean_dec(v_unused_462_);
v___x_426_ = v_x_412_;
v_isShared_427_ = v_isSharedCheck_461_;
state = 1; continue;
} else {
lean_dec(v_x_412_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_461_;
state = 1; continue;
}
}
} else {
let mut v_ks_463_: *mut lean_object = core::ptr::null_mut(); let mut v_vs_464_: *mut lean_object = core::ptr::null_mut(); let mut v___x_466_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_467_: u8 = 0; let mut v_isSharedCheck_484_: u8 = 0; 
v_ks_463_ = lean_ctor_get(v_x_412_, 0);
v_vs_464_ = lean_ctor_get(v_x_412_, 1);
v_isSharedCheck_484_ = (!lean_is_exclusive(v_x_412_)) as u8;
if v_isSharedCheck_484_ == 0 {
v___x_466_ = v_x_412_;
v_isShared_467_ = v_isSharedCheck_484_;
state = 8; continue;
} else {
lean_inc(v_vs_464_);
lean_inc(v_ks_463_);
lean_dec(v_x_412_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_484_;
state = 8; continue;
}
}
}
1 => {
v_v_428_ = lean_array_fget(v_es_417_, v_j_422_);
v___x_429_ = lean_box(0);
v_xs_x27_430_ = lean_array_fset(v_es_417_, v_j_422_, v___x_429_);
match lean_obj_tag(v_v_428_)
{
0 => {
let mut v_key_437_: *mut lean_object = core::ptr::null_mut(); let mut v_val_438_: *mut lean_object = core::ptr::null_mut(); let mut v___x_440_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_441_: u8 = 0; let mut v_isSharedCheck_448_: u8 = 0; 
v_key_437_ = lean_ctor_get(v_v_428_, 0);
v_val_438_ = lean_ctor_get(v_v_428_, 1);
v_isSharedCheck_448_ = (!lean_is_exclusive(v_v_428_)) as u8;
if v_isSharedCheck_448_ == 0 {
v___x_440_ = v_v_428_;
v_isShared_441_ = v_isSharedCheck_448_;
state = 4; continue;
} else {
lean_inc(v_val_438_);
lean_inc(v_key_437_);
lean_dec(v_v_428_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_448_;
state = 4; continue;
}
}
1 => {
let mut v_node_449_: *mut lean_object = core::ptr::null_mut(); let mut v___x_451_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_452_: u8 = 0; let mut v_isSharedCheck_459_: u8 = 0; 
v_node_449_ = lean_ctor_get(v_v_428_, 0);
v_isSharedCheck_459_ = (!lean_is_exclusive(v_v_428_)) as u8;
if v_isSharedCheck_459_ == 0 {
v___x_451_ = v_v_428_;
v_isShared_452_ = v_isSharedCheck_459_;
state = 6; continue;
} else {
lean_inc(v_node_449_);
lean_dec(v_v_428_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_459_;
state = 6; continue;
}
}
_ => {
let mut v___x_460_: *mut lean_object = core::ptr::null_mut(); 
v___x_460_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_460_, 0, v_x_415_);
lean_ctor_set(v___x_460_, 1, v_x_416_);
v___y_432_ = v___x_460_;
state = 2; continue;
}
}
}
8 => {
if v_isShared_467_ == 0 {
v___x_469_ = v___x_466_;
state = 9; continue;
} else {
let mut v_reuseFailAlloc_483_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_483_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v_ks_463_);
lean_ctor_set(v_reuseFailAlloc_483_, 1, v_vs_464_);
v___x_469_ = v_reuseFailAlloc_483_;
state = 9; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__1_spec__1_spec__3___redArg(mut v_depth_485_: usize, mut v_keys_486_: *mut lean_object, mut v_vals_487_: *mut lean_object, mut v_i_488_: *mut lean_object, mut v_entries_489_: *mut lean_object) -> *mut lean_object{
let mut v___x_490_: *mut lean_object = core::ptr::null_mut(); let mut v___x_491_: u8 = 0; let mut v_k_492_: *mut lean_object = core::ptr::null_mut(); let mut v_v_493_: *mut lean_object = core::ptr::null_mut(); let mut v___x_494_: u64 = 0; let mut v_h_495_: usize = 0; let mut v___x_496_: usize = 0; let mut v___x_497_: *mut lean_object = core::ptr::null_mut(); let mut v___x_498_: usize = 0; let mut v___x_499_: usize = 0; let mut v___x_500_: usize = 0; let mut v_h_501_: usize = 0; let mut v___x_502_: *mut lean_object = core::ptr::null_mut(); let mut v___x_503_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_490_ = lean_array_get_size(v_keys_486_);
v___x_491_ = lean_nat_dec_lt(v_i_488_, v___x_490_);
if v___x_491_ == 0 {
lean_dec(v_i_488_);
return v_entries_489_;
} else {
let mut v_k_492_: *mut lean_object = core::ptr::null_mut(); let mut v_v_493_: *mut lean_object = core::ptr::null_mut(); let mut v___x_494_: u64 = 0; let mut v_h_495_: usize = 0; let mut v___x_496_: usize = 0; let mut v___x_497_: *mut lean_object = core::ptr::null_mut(); let mut v___x_498_: usize = 0; let mut v___x_499_: usize = 0; let mut v___x_500_: usize = 0; let mut v_h_501_: usize = 0; let mut v___x_502_: *mut lean_object = core::ptr::null_mut(); let mut v___x_503_: *mut lean_object = core::ptr::null_mut(); 
v_k_492_ = lean_array_fget_borrowed(v_keys_486_, v_i_488_);
v_v_493_ = lean_array_fget_borrowed(v_vals_487_, v_i_488_);
v___x_494_ = lean_uint64_of_nat(v_k_492_);
v_h_495_ = lean_uint64_to_usize(v___x_494_);
v___x_496_ = 5usize;
v___x_497_ = lean_unsigned_to_nat(1);
v___x_498_ = 1usize;
v___x_499_ = lean_usize_sub(v_depth_485_, v___x_498_);
v___x_500_ = lean_usize_mul(v___x_496_, v___x_499_);
v_h_501_ = lean_usize_shift_right(v_h_495_, v___x_500_);
v___x_502_ = lean_nat_add(v_i_488_, v___x_497_);
lean_dec(v_i_488_);
lean_inc(v_v_493_);
lean_inc(v_k_492_);
v___x_503_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__1_spec__1___redArg(v_entries_489_, v_h_501_, v_depth_485_, v_k_492_, v_v_493_);
v_i_488_ = v___x_502_;
v_entries_489_ = v___x_503_;
state = 0; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__1_spec__1_spec__3___redArg___boxed(mut v_depth_505_: *mut lean_object, mut v_keys_506_: *mut lean_object, mut v_vals_507_: *mut lean_object, mut v_i_508_: *mut lean_object, mut v_entries_509_: *mut lean_object) -> *mut lean_object{
let mut v_depth_boxed_510_: usize = 0; let mut v_res_511_: *mut lean_object = core::ptr::null_mut(); 
v_depth_boxed_510_ = lean_unbox_usize(v_depth_505_);
lean_dec(v_depth_505_);
v_res_511_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__1_spec__1_spec__3___redArg(v_depth_boxed_510_, v_keys_506_, v_vals_507_, v_i_508_, v_entries_509_);
lean_dec_ref(v_vals_507_);
lean_dec_ref(v_keys_506_);
return v_res_511_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__1_spec__1___redArg___boxed(mut v_x_512_: *mut lean_object, mut v_x_513_: *mut lean_object, mut v_x_514_: *mut lean_object, mut v_x_515_: *mut lean_object, mut v_x_516_: *mut lean_object) -> *mut lean_object{
let mut v_x_1082__boxed_517_: usize = 0; let mut v_x_1083__boxed_518_: usize = 0; let mut v_res_519_: *mut lean_object = core::ptr::null_mut(); 
v_x_1082__boxed_517_ = lean_unbox_usize(v_x_513_);
lean_dec(v_x_513_);
v_x_1083__boxed_518_ = lean_unbox_usize(v_x_514_);
lean_dec(v_x_514_);
v_res_519_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__1_spec__1___redArg(v_x_512_, v_x_1082__boxed_517_, v_x_1083__boxed_518_, v_x_515_, v_x_516_);
return v_res_519_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_insert___at___00main_spec__1___redArg(mut v_x_520_: *mut lean_object, mut v_x_521_: *mut lean_object, mut v_x_522_: *mut lean_object) -> *mut lean_object{
let mut v___x_523_: u64 = 0; let mut v___x_524_: usize = 0; let mut v___x_525_: usize = 0; let mut v___x_526_: *mut lean_object = core::ptr::null_mut(); 
v___x_523_ = lean_uint64_of_nat(v_x_521_);
v___x_524_ = lean_uint64_to_usize(v___x_523_);
v___x_525_ = 1usize;
v___x_526_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__1_spec__1___redArg(v_x_520_, v___x_524_, v___x_525_, v_x_521_, v_x_522_);
return v___x_526_;
}
#[no_mangle] pub unsafe extern "C" fn l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00main_spec__3_spec__4_spec__7_spec__9(mut v_xs_527_: *mut lean_object, mut v_v_528_: *mut lean_object, mut v_i_529_: *mut lean_object) -> *mut lean_object{
let mut v___x_530_: *mut lean_object = core::ptr::null_mut(); let mut v___x_531_: u8 = 0; let mut v___x_532_: *mut lean_object = core::ptr::null_mut(); let mut v___x_533_: *mut lean_object = core::ptr::null_mut(); let mut v___x_534_: u8 = 0; let mut v___x_535_: *mut lean_object = core::ptr::null_mut(); let mut v___x_536_: *mut lean_object = core::ptr::null_mut(); let mut v___x_538_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_530_ = lean_array_get_size(v_xs_527_);
v___x_531_ = lean_nat_dec_lt(v_i_529_, v___x_530_);
if v___x_531_ == 0 {
let mut v___x_532_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_i_529_);
v___x_532_ = lean_box(0);
return v___x_532_;
} else {
let mut v___x_533_: *mut lean_object = core::ptr::null_mut(); let mut v___x_534_: u8 = 0; 
v___x_533_ = lean_array_fget_borrowed(v_xs_527_, v_i_529_);
v___x_534_ = lean_nat_dec_eq(v___x_533_, v_v_528_);
if v___x_534_ == 0 {
let mut v___x_535_: *mut lean_object = core::ptr::null_mut(); let mut v___x_536_: *mut lean_object = core::ptr::null_mut(); 
v___x_535_ = lean_unsigned_to_nat(1);
v___x_536_ = lean_nat_add(v_i_529_, v___x_535_);
lean_dec(v_i_529_);
v_i_529_ = v___x_536_;
state = 0; continue;
} else {
let mut v___x_538_: *mut lean_object = core::ptr::null_mut(); 
v___x_538_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v___x_538_, 0, v_i_529_);
return v___x_538_;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00main_spec__3_spec__4_spec__7_spec__9___boxed(mut v_xs_539_: *mut lean_object, mut v_v_540_: *mut lean_object, mut v_i_541_: *mut lean_object) -> *mut lean_object{
let mut v_res_542_: *mut lean_object = core::ptr::null_mut(); 
v_res_542_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00main_spec__3_spec__4_spec__7_spec__9(v_xs_539_, v_v_540_, v_i_541_);
lean_dec(v_v_540_);
lean_dec_ref(v_xs_539_);
return v_res_542_;
}
#[no_mangle] pub unsafe extern "C" fn l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00main_spec__3_spec__4_spec__7(mut v_xs_543_: *mut lean_object, mut v_v_544_: *mut lean_object) -> *mut lean_object{
let mut v___x_545_: *mut lean_object = core::ptr::null_mut(); let mut v___x_546_: *mut lean_object = core::ptr::null_mut(); 
v___x_545_ = lean_unsigned_to_nat(0);
v___x_546_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00main_spec__3_spec__4_spec__7_spec__9(v_xs_543_, v_v_544_, v___x_545_);
return v___x_546_;
}
#[no_mangle] pub unsafe extern "C" fn l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00main_spec__3_spec__4_spec__7___boxed(mut v_xs_547_: *mut lean_object, mut v_v_548_: *mut lean_object) -> *mut lean_object{
let mut v_res_549_: *mut lean_object = core::ptr::null_mut(); 
v_res_549_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00main_spec__3_spec__4_spec__7(v_xs_547_, v_v_548_);
lean_dec(v_v_548_);
lean_dec_ref(v_xs_547_);
return v_res_549_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00main_spec__3_spec__4___redArg(mut v_x_550_: *mut lean_object, mut v_x_551_: usize, mut v_x_552_: *mut lean_object) -> *mut lean_object{
let mut v_es_553_: *mut lean_object = core::ptr::null_mut(); let mut v___x_554_: *mut lean_object = core::ptr::null_mut(); let mut v___x_555_: usize = 0; let mut v___x_556_: usize = 0; let mut v___x_557_: usize = 0; let mut v_j_558_: *mut lean_object = core::ptr::null_mut(); let mut v_entry_559_: *mut lean_object = core::ptr::null_mut(); let mut v_key_560_: *mut lean_object = core::ptr::null_mut(); let mut v___x_561_: u8 = 0; let mut v___x_563_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_564_: u8 = 0; let mut v___x_565_: *mut lean_object = core::ptr::null_mut(); let mut v___x_567_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_568_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_569_: u8 = 0; let mut v_unused_570_: *mut lean_object = core::ptr::null_mut(); let mut v___x_572_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_573_: u8 = 0; let mut v_node_574_: *mut lean_object = core::ptr::null_mut(); let mut v___x_576_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_577_: u8 = 0; let mut v_entries_578_: *mut lean_object = core::ptr::null_mut(); let mut v___x_579_: usize = 0; let mut v_newNode_580_: *mut lean_object = core::ptr::null_mut(); let mut v___x_581_: *mut lean_object = core::ptr::null_mut(); let mut v___x_583_: *mut lean_object = core::ptr::null_mut(); let mut v___x_584_: *mut lean_object = core::ptr::null_mut(); let mut v___x_586_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_587_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_588_: *mut lean_object = core::ptr::null_mut(); let mut v_val_589_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_590_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_591_: *mut lean_object = core::ptr::null_mut(); let mut v___x_593_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_594_: u8 = 0; let mut v___x_596_: *mut lean_object = core::ptr::null_mut(); let mut v___x_597_: *mut lean_object = core::ptr::null_mut(); let mut v___x_599_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_600_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_601_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_602_: u8 = 0; let mut v_isSharedCheck_603_: u8 = 0; let mut v_isSharedCheck_604_: u8 = 0; let mut v_unused_605_: *mut lean_object = core::ptr::null_mut(); let mut v_ks_606_: *mut lean_object = core::ptr::null_mut(); let mut v_vs_607_: *mut lean_object = core::ptr::null_mut(); let mut v___x_609_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_610_: u8 = 0; let mut v___x_611_: *mut lean_object = core::ptr::null_mut(); let mut v___x_613_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_614_: *mut lean_object = core::ptr::null_mut(); let mut v_val_615_: *mut lean_object = core::ptr::null_mut(); let mut v_keys_x27_616_: *mut lean_object = core::ptr::null_mut(); let mut v_vals_x27_617_: *mut lean_object = core::ptr::null_mut(); let mut v___x_619_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_620_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_621_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_x_550_) == 0 {
let mut v_es_553_: *mut lean_object = core::ptr::null_mut(); let mut v___x_554_: *mut lean_object = core::ptr::null_mut(); let mut v___x_555_: usize = 0; let mut v___x_556_: usize = 0; let mut v___x_557_: usize = 0; let mut v_j_558_: *mut lean_object = core::ptr::null_mut(); let mut v_entry_559_: *mut lean_object = core::ptr::null_mut(); 
v_es_553_ = lean_ctor_get(v_x_550_, 0);
v___x_554_ = lean_box(2);
v___x_555_ = 5usize;
v___x_556_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__1_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__1_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__1_spec__1___redArg___closed__1);
v___x_557_ = lean_usize_land(v_x_551_, v___x_556_);
v_j_558_ = lean_usize_to_nat(v___x_557_);
v_entry_559_ = lean_array_get(v___x_554_, v_es_553_, v_j_558_);
match lean_obj_tag(v_entry_559_)
{
0 => {
let mut v_key_560_: *mut lean_object = core::ptr::null_mut(); let mut v___x_561_: u8 = 0; 
v_key_560_ = lean_ctor_get(v_entry_559_, 0);
lean_inc(v_key_560_);
lean_dec_ref_known(v_entry_559_, 2);
v___x_561_ = lean_nat_dec_eq(v_x_552_, v_key_560_);
lean_dec(v_key_560_);
if v___x_561_ == 0 {
lean_dec(v_j_558_);
return v_x_550_;
} else {
let mut v___x_563_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_564_: u8 = 0; let mut v_isSharedCheck_569_: u8 = 0; 
lean_inc_ref(v_es_553_);
v_isSharedCheck_569_ = (!lean_is_exclusive(v_x_550_)) as u8;
if v_isSharedCheck_569_ == 0 {
let mut v_unused_570_: *mut lean_object = core::ptr::null_mut(); 
v_unused_570_ = lean_ctor_get(v_x_550_, 0);
lean_dec(v_unused_570_);
v___x_563_ = v_x_550_;
v_isShared_564_ = v_isSharedCheck_569_;
state = 1; continue;
} else {
lean_dec(v_x_550_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_569_;
state = 1; continue;
}
}
}
1 => {
let mut v___x_572_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_573_: u8 = 0; let mut v_isSharedCheck_604_: u8 = 0; 
lean_inc_ref(v_es_553_);
v_isSharedCheck_604_ = (!lean_is_exclusive(v_x_550_)) as u8;
if v_isSharedCheck_604_ == 0 {
let mut v_unused_605_: *mut lean_object = core::ptr::null_mut(); 
v_unused_605_ = lean_ctor_get(v_x_550_, 0);
lean_dec(v_unused_605_);
v___x_572_ = v_x_550_;
v_isShared_573_ = v_isSharedCheck_604_;
state = 3; continue;
} else {
lean_dec(v_x_550_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_604_;
state = 3; continue;
}
}
_ => {
lean_dec(v_j_558_);
return v_x_550_;
}
}
} else {
let mut v_ks_606_: *mut lean_object = core::ptr::null_mut(); let mut v_vs_607_: *mut lean_object = core::ptr::null_mut(); let mut v___x_609_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_610_: u8 = 0; let mut v_isSharedCheck_621_: u8 = 0; 
v_ks_606_ = lean_ctor_get(v_x_550_, 0);
v_vs_607_ = lean_ctor_get(v_x_550_, 1);
v_isSharedCheck_621_ = (!lean_is_exclusive(v_x_550_)) as u8;
if v_isSharedCheck_621_ == 0 {
v___x_609_ = v_x_550_;
v_isShared_610_ = v_isSharedCheck_621_;
state = 10; continue;
} else {
lean_inc(v_vs_607_);
lean_inc(v_ks_606_);
lean_dec(v_x_550_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_621_;
state = 10; continue;
}
}
}
1 => {
v___x_565_ = lean_array_set(v_es_553_, v_j_558_, v___x_554_);
lean_dec(v_j_558_);
if v_isShared_564_ == 0 {
lean_ctor_set(v___x_563_, 0, v___x_565_);
v___x_567_ = v___x_563_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_568_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_568_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v___x_565_);
v___x_567_ = v_reuseFailAlloc_568_;
state = 2; continue;
}
}
3 => {
v_node_574_ = lean_ctor_get(v_entry_559_, 0);
v_isSharedCheck_603_ = (!lean_is_exclusive(v_entry_559_)) as u8;
if v_isSharedCheck_603_ == 0 {
v___x_576_ = v_entry_559_;
v_isShared_577_ = v_isSharedCheck_603_;
state = 4; continue;
} else {
lean_inc(v_node_574_);
lean_dec(v_entry_559_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_603_;
state = 4; continue;
}
}
10 => {
v___x_611_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00main_spec__3_spec__4_spec__7(v_ks_606_, v_x_552_);
if lean_obj_tag(v___x_611_) == 0 {
let mut v___x_613_: *mut lean_object = core::ptr::null_mut(); 
if v_isShared_610_ == 0 {
v___x_613_ = v___x_609_;
state = 11; continue;
} else {
let mut v_reuseFailAlloc_614_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_614_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_ks_606_);
lean_ctor_set(v_reuseFailAlloc_614_, 1, v_vs_607_);
v___x_613_ = v_reuseFailAlloc_614_;
state = 11; continue;
}
} else {
let mut v_val_615_: *mut lean_object = core::ptr::null_mut(); let mut v_keys_x27_616_: *mut lean_object = core::ptr::null_mut(); let mut v_vals_x27_617_: *mut lean_object = core::ptr::null_mut(); let mut v___x_619_: *mut lean_object = core::ptr::null_mut(); 
v_val_615_ = lean_ctor_get(v___x_611_, 0);
lean_inc_n(v_val_615_, 2);
lean_dec_ref_known(v___x_611_, 1);
v_keys_x27_616_ = l_Array_eraseIdx___redArg(v_ks_606_, v_val_615_);
v_vals_x27_617_ = l_Array_eraseIdx___redArg(v_vs_607_, v_val_615_);
if v_isShared_610_ == 0 {
lean_ctor_set(v___x_609_, 1, v_vals_x27_617_);
lean_ctor_set(v___x_609_, 0, v_keys_x27_616_);
v___x_619_ = v___x_609_;
state = 12; continue;
} else {
let mut v_reuseFailAlloc_620_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_620_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v_keys_x27_616_);
lean_ctor_set(v_reuseFailAlloc_620_, 1, v_vals_x27_617_);
v___x_619_ = v_reuseFailAlloc_620_;
state = 12; continue;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00main_spec__3_spec__4___redArg___boxed(mut v_x_622_: *mut lean_object, mut v_x_623_: *mut lean_object, mut v_x_624_: *mut lean_object) -> *mut lean_object{
let mut v_x_1286__boxed_625_: usize = 0; let mut v_res_626_: *mut lean_object = core::ptr::null_mut(); 
v_x_1286__boxed_625_ = lean_unbox_usize(v_x_623_);
lean_dec(v_x_623_);
v_res_626_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00main_spec__3_spec__4___redArg(v_x_622_, v_x_1286__boxed_625_, v_x_624_);
lean_dec(v_x_624_);
return v_res_626_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_erase___at___00main_spec__3___redArg(mut v_x_627_: *mut lean_object, mut v_x_628_: *mut lean_object) -> *mut lean_object{
let mut v___x_629_: u64 = 0; let mut v_h_630_: usize = 0; let mut v___x_631_: *mut lean_object = core::ptr::null_mut(); 
v___x_629_ = lean_uint64_of_nat(v_x_628_);
v_h_630_ = lean_uint64_to_usize(v___x_629_);
v___x_631_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00main_spec__3_spec__4___redArg(v_x_627_, v_h_630_, v_x_628_);
return v___x_631_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_erase___at___00main_spec__3___redArg___boxed(mut v_x_632_: *mut lean_object, mut v_x_633_: *mut lean_object) -> *mut lean_object{
let mut v_res_634_: *mut lean_object = core::ptr::null_mut(); 
v_res_634_ = l_Lean_PersistentHashMap_erase___at___00main_spec__3___redArg(v_x_632_, v_x_633_);
lean_dec(v_x_633_);
return v_res_634_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__2(mut v_s_635_: *mut lean_object) -> *mut lean_object{
let mut v___x_637_: *mut lean_object = core::ptr::null_mut(); let mut v___x_638_: u32 = 0; let mut v___x_639_: *mut lean_object = core::ptr::null_mut(); let mut v___x_640_: *mut lean_object = core::ptr::null_mut(); 
v___x_637_ = l_Lean_PersistentHashMap_Stats_toString(v_s_635_);
v___x_638_ = 10;
v___x_639_ = lean_string_push(v___x_637_, v___x_638_);
v___x_640_ = l_IO_print___at___00IO_println___at___00checkState_spec__1_spec__1(v___x_639_);
return v___x_640_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__2___boxed(mut v_s_641_: *mut lean_object, mut v_a_642_: *mut lean_object) -> *mut lean_object{
let mut v_res_643_: *mut lean_object = core::ptr::null_mut(); 
v_res_643_ = l_IO_println___at___00main_spec__2(v_s_641_);
return v_res_643_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__0() -> *mut lean_object{
let mut v_m_644_: *mut lean_object = core::ptr::null_mut(); 
v_m_644_ = l_Lean_PersistentHashMap_empty___at___00main_spec__0(lean_box(0));
return v_m_644_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__1() -> *mut lean_object{
let mut v___x_645_: *mut lean_object = core::ptr::null_mut(); let mut v_m_646_: *mut lean_object = core::ptr::null_mut(); let mut v_m_647_: *mut lean_object = core::ptr::null_mut(); 
v___x_645_ = lean_unsigned_to_nat(1);
v_m_646_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__0), core::ptr::addr_of_mut!(l_main___closed__0_once), _init_l_main___closed__0);
v_m_647_ = l_Lean_PersistentHashMap_insert___at___00main_spec__1___redArg(v_m_646_, v___x_645_, v___x_645_);
return v_m_647_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__2() -> *mut lean_object{
let mut v___x_648_: *mut lean_object = core::ptr::null_mut(); let mut v___x_649_: *mut lean_object = core::ptr::null_mut(); let mut v_m_650_: *mut lean_object = core::ptr::null_mut(); let mut v_m_651_: *mut lean_object = core::ptr::null_mut(); 
v___x_648_ = lean_unsigned_to_nat(2);
v___x_649_ = lean_unsigned_to_nat(33554433);
v_m_650_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__1), core::ptr::addr_of_mut!(l_main___closed__1_once), _init_l_main___closed__1);
v_m_651_ = l_Lean_PersistentHashMap_insert___at___00main_spec__1___redArg(v_m_650_, v___x_649_, v___x_648_);
return v_m_651_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__3() -> *mut lean_object{
let mut v___x_652_: *mut lean_object = core::ptr::null_mut(); let mut v___x_653_: *mut lean_object = core::ptr::null_mut(); let mut v_m_654_: *mut lean_object = core::ptr::null_mut(); let mut v_m_655_: *mut lean_object = core::ptr::null_mut(); 
v___x_652_ = lean_unsigned_to_nat(3);
v___x_653_ = lean_cstr_to_nat(b"34359738369\0".as_ptr().cast());
v_m_654_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__2), core::ptr::addr_of_mut!(l_main___closed__2_once), _init_l_main___closed__2);
v_m_655_ = l_Lean_PersistentHashMap_insert___at___00main_spec__1___redArg(v_m_654_, v___x_653_, v___x_652_);
return v_m_655_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__4() -> *mut lean_object{
let mut v___x_656_: *mut lean_object = core::ptr::null_mut(); let mut v___x_657_: *mut lean_object = core::ptr::null_mut(); let mut v_m_658_: *mut lean_object = core::ptr::null_mut(); let mut v_m_659_: *mut lean_object = core::ptr::null_mut(); 
v___x_656_ = lean_unsigned_to_nat(4);
v___x_657_ = lean_cstr_to_nat(b"1099511627777\0".as_ptr().cast());
v_m_658_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__3), core::ptr::addr_of_mut!(l_main___closed__3_once), _init_l_main___closed__3);
v_m_659_ = l_Lean_PersistentHashMap_insert___at___00main_spec__1___redArg(v_m_658_, v___x_657_, v___x_656_);
return v_m_659_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__5() -> *mut lean_object{
let mut v___x_660_: *mut lean_object = core::ptr::null_mut(); let mut v___x_661_: *mut lean_object = core::ptr::null_mut(); let mut v_m_662_: *mut lean_object = core::ptr::null_mut(); let mut v_m_663_: *mut lean_object = core::ptr::null_mut(); 
v___x_660_ = lean_unsigned_to_nat(5);
v___x_661_ = lean_cstr_to_nat(b"35184372088833\0".as_ptr().cast());
v_m_662_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__4), core::ptr::addr_of_mut!(l_main___closed__4_once), _init_l_main___closed__4);
v_m_663_ = l_Lean_PersistentHashMap_insert___at___00main_spec__1___redArg(v_m_662_, v___x_661_, v___x_660_);
return v_m_663_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__6() -> *mut lean_object{
let mut v_m_664_: *mut lean_object = core::ptr::null_mut(); let mut v___x_665_: *mut lean_object = core::ptr::null_mut(); 
v_m_664_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__5), core::ptr::addr_of_mut!(l_main___closed__5_once), _init_l_main___closed__5);
v___x_665_ = l_Lean_PersistentHashMap_stats___at___00checkState_spec__0___redArg(v_m_664_);
return v___x_665_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__7() -> *mut lean_object{
let mut v___x_666_: *mut lean_object = core::ptr::null_mut(); let mut v_m_667_: *mut lean_object = core::ptr::null_mut(); let mut v___x_668_: *mut lean_object = core::ptr::null_mut(); 
v___x_666_ = lean_cstr_to_nat(b"1099511627777\0".as_ptr().cast());
v_m_667_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__5), core::ptr::addr_of_mut!(l_main___closed__5_once), _init_l_main___closed__5);
v___x_668_ = l_Lean_PersistentHashMap_erase___at___00main_spec__3___redArg(v_m_667_, v___x_666_);
return v___x_668_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__8() -> *mut lean_object{
let mut v___x_669_: *mut lean_object = core::ptr::null_mut(); let mut v___x_670_: *mut lean_object = core::ptr::null_mut(); let mut v___x_671_: *mut lean_object = core::ptr::null_mut(); 
v___x_669_ = lean_cstr_to_nat(b"35184372088833\0".as_ptr().cast());
v___x_670_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__7), core::ptr::addr_of_mut!(l_main___closed__7_once), _init_l_main___closed__7);
v___x_671_ = l_Lean_PersistentHashMap_erase___at___00main_spec__3___redArg(v___x_670_, v___x_669_);
return v___x_671_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__9() -> *mut lean_object{
let mut v___x_672_: *mut lean_object = core::ptr::null_mut(); let mut v___x_673_: *mut lean_object = core::ptr::null_mut(); let mut v___x_674_: *mut lean_object = core::ptr::null_mut(); 
v___x_672_ = lean_cstr_to_nat(b"34359738369\0".as_ptr().cast());
v___x_673_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__8), core::ptr::addr_of_mut!(l_main___closed__8_once), _init_l_main___closed__8);
v___x_674_ = l_Lean_PersistentHashMap_erase___at___00main_spec__3___redArg(v___x_673_, v___x_672_);
return v___x_674_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__10() -> *mut lean_object{
let mut v___x_675_: *mut lean_object = core::ptr::null_mut(); let mut v___x_676_: *mut lean_object = core::ptr::null_mut(); 
v___x_675_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__9), core::ptr::addr_of_mut!(l_main___closed__9_once), _init_l_main___closed__9);
v___x_676_ = l_Lean_PersistentHashMap_stats___at___00checkState_spec__0___redArg(v___x_675_);
return v___x_676_;
}
#[no_mangle] pub unsafe extern "C" fn _lean_main() -> *mut lean_object{
let mut v___x_678_: *mut lean_object = core::ptr::null_mut(); let mut v___y_680_: *mut lean_object = core::ptr::null_mut(); let mut v___x_681_: *mut lean_object = core::ptr::null_mut(); let mut v___x_682_: *mut lean_object = core::ptr::null_mut(); let mut v___x_683_: *mut lean_object = core::ptr::null_mut(); let mut v___x_684_: *mut lean_object = core::ptr::null_mut(); let mut v___x_685_: *mut lean_object = core::ptr::null_mut(); let mut v___x_687_: *mut lean_object = core::ptr::null_mut(); let mut v___x_688_: *mut lean_object = core::ptr::null_mut(); let mut v___x_689_: *mut lean_object = core::ptr::null_mut(); let mut v___x_690_: *mut lean_object = core::ptr::null_mut(); let mut v_maxDepth_691_: *mut lean_object = core::ptr::null_mut(); let mut v___x_692_: *mut lean_object = core::ptr::null_mut(); let mut v___x_693_: u8 = 0; let mut v___x_694_: *mut lean_object = core::ptr::null_mut(); let mut v___x_695_: *mut lean_object = core::ptr::null_mut(); let mut v___x_697_: *mut lean_object = core::ptr::null_mut(); let mut v_numCollisions_698_: *mut lean_object = core::ptr::null_mut(); let mut v___x_699_: u8 = 0; let mut v___x_700_: *mut lean_object = core::ptr::null_mut(); let mut v___x_701_: *mut lean_object = core::ptr::null_mut(); let mut v___x_702_: *mut lean_object = core::ptr::null_mut(); let mut v_maxDepth_703_: *mut lean_object = core::ptr::null_mut(); let mut v_max_704_: *mut lean_object = core::ptr::null_mut(); let mut v___x_705_: u8 = 0; let mut v___x_706_: *mut lean_object = core::ptr::null_mut(); let mut v___x_707_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_678_ = lean_unsigned_to_nat(33554433);
v___x_685_ = lean_unsigned_to_nat(3);
v___x_702_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__6), core::ptr::addr_of_mut!(l_main___closed__6_once), _init_l_main___closed__6);
v_maxDepth_703_ = lean_ctor_get(v___x_702_, 3);
v_max_704_ = lean_unsigned_to_nat(7);
v___x_705_ = lean_nat_dec_eq(v_maxDepth_703_, v_max_704_);
if v___x_705_ == 0 {
let mut v___x_706_: *mut lean_object = core::ptr::null_mut(); let mut v___x_707_: *mut lean_object = core::ptr::null_mut(); 
v___x_706_ = l_checkState___closed__1;
v___x_707_ = l_IO_println___at___00checkState_spec__1(v___x_706_);
if lean_obj_tag(v___x_707_) == 0 {
lean_dec_ref_known(v___x_707_, 1);
state = 3; continue;
} else {
return v___x_707_;
}
} else {
state = 3; continue;
}
}
1 => {
lean_inc_ref(v___y_680_);
v___x_681_ = l_Lean_PersistentHashMap_erase___at___00main_spec__3___redArg(v___y_680_, v___x_678_);
v___x_682_ = l_checkState(v___x_681_);
if lean_obj_tag(v___x_682_) == 0 {
let mut v___x_683_: *mut lean_object = core::ptr::null_mut(); let mut v___x_684_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_682_, 1);
v___x_683_ = l_Lean_PersistentHashMap_stats___at___00checkState_spec__0___redArg(v___x_681_);
lean_dec_ref(v___x_681_);
v___x_684_ = l_IO_println___at___00main_spec__2(v___x_683_);
return v___x_684_;
} else {
lean_dec_ref(v___x_681_);
return v___x_682_;
}
}
2 => {
v___x_687_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__6), core::ptr::addr_of_mut!(l_main___closed__6_once), _init_l_main___closed__6);
v___x_688_ = l_IO_println___at___00main_spec__2(v___x_687_);
if lean_obj_tag(v___x_688_) == 0 {
let mut v___x_689_: *mut lean_object = core::ptr::null_mut(); let mut v___x_690_: *mut lean_object = core::ptr::null_mut(); let mut v_maxDepth_691_: *mut lean_object = core::ptr::null_mut(); let mut v___x_692_: *mut lean_object = core::ptr::null_mut(); let mut v___x_693_: u8 = 0; 
lean_dec_ref_known(v___x_688_, 1);
v___x_689_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__9), core::ptr::addr_of_mut!(l_main___closed__9_once), _init_l_main___closed__9);
v___x_690_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__10), core::ptr::addr_of_mut!(l_main___closed__10_once), _init_l_main___closed__10);
v_maxDepth_691_ = lean_ctor_get(v___x_690_, 3);
v___x_692_ = lean_unsigned_to_nat(6);
v___x_693_ = lean_nat_dec_eq(v_maxDepth_691_, v___x_692_);
if v___x_693_ == 0 {
let mut v___x_694_: *mut lean_object = core::ptr::null_mut(); let mut v___x_695_: *mut lean_object = core::ptr::null_mut(); 
v___x_694_ = l_checkState___closed__1;
v___x_695_ = l_IO_println___at___00checkState_spec__1(v___x_694_);
if lean_obj_tag(v___x_695_) == 0 {
lean_dec_ref_known(v___x_695_, 1);
v___y_680_ = v___x_689_;
state = 1; continue;
} else {
return v___x_695_;
}
} else {
v___y_680_ = v___x_689_;
state = 1; continue;
}
} else {
return v___x_688_;
}
}
3 => {
v___x_697_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__6), core::ptr::addr_of_mut!(l_main___closed__6_once), _init_l_main___closed__6);
v_numCollisions_698_ = lean_ctor_get(v___x_697_, 2);
v___x_699_ = lean_nat_dec_eq(v_numCollisions_698_, v___x_685_);
if v___x_699_ == 0 {
let mut v___x_700_: *mut lean_object = core::ptr::null_mut(); let mut v___x_701_: *mut lean_object = core::ptr::null_mut(); 
v___x_700_ = l_checkState___closed__0;
v___x_701_ = l_IO_println___at___00checkState_spec__1(v___x_700_);
if lean_obj_tag(v___x_701_) == 0 {
lean_dec_ref_known(v___x_701_, 1);
state = 2; continue;
} else {
return v___x_701_;
}
} else {
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_main___boxed(mut v_a_708_: *mut lean_object) -> *mut lean_object{
let mut v_res_709_: *mut lean_object = core::ptr::null_mut(); 
v_res_709_ = _lean_main();
return v_res_709_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_insert___at___00main_spec__1(mut v_00_u03b2_710_: *mut lean_object, mut v_x_711_: *mut lean_object, mut v_x_712_: *mut lean_object, mut v_x_713_: *mut lean_object) -> *mut lean_object{
let mut v___x_714_: *mut lean_object = core::ptr::null_mut(); 
v___x_714_ = l_Lean_PersistentHashMap_insert___at___00main_spec__1___redArg(v_x_711_, v_x_712_, v_x_713_);
return v___x_714_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_erase___at___00main_spec__3(mut v_00_u03b2_715_: *mut lean_object, mut v_x_716_: *mut lean_object, mut v_x_717_: *mut lean_object) -> *mut lean_object{
let mut v___x_718_: *mut lean_object = core::ptr::null_mut(); 
v___x_718_ = l_Lean_PersistentHashMap_erase___at___00main_spec__3___redArg(v_x_716_, v_x_717_);
return v___x_718_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_erase___at___00main_spec__3___boxed(mut v_00_u03b2_719_: *mut lean_object, mut v_x_720_: *mut lean_object, mut v_x_721_: *mut lean_object) -> *mut lean_object{
let mut v_res_722_: *mut lean_object = core::ptr::null_mut(); 
v_res_722_ = l_Lean_PersistentHashMap_erase___at___00main_spec__3(v_00_u03b2_719_, v_x_720_, v_x_721_);
lean_dec(v_x_721_);
return v_res_722_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__1_spec__1(mut v_00_u03b2_723_: *mut lean_object, mut v_x_724_: *mut lean_object, mut v_x_725_: usize, mut v_x_726_: usize, mut v_x_727_: *mut lean_object, mut v_x_728_: *mut lean_object) -> *mut lean_object{
let mut v___x_729_: *mut lean_object = core::ptr::null_mut(); 
v___x_729_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__1_spec__1___redArg(v_x_724_, v_x_725_, v_x_726_, v_x_727_, v_x_728_);
return v___x_729_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__1_spec__1___boxed(mut v_00_u03b2_730_: *mut lean_object, mut v_x_731_: *mut lean_object, mut v_x_732_: *mut lean_object, mut v_x_733_: *mut lean_object, mut v_x_734_: *mut lean_object, mut v_x_735_: *mut lean_object) -> *mut lean_object{
let mut v_x_1593__boxed_736_: usize = 0; let mut v_x_1594__boxed_737_: usize = 0; let mut v_res_738_: *mut lean_object = core::ptr::null_mut(); 
v_x_1593__boxed_736_ = lean_unbox_usize(v_x_732_);
lean_dec(v_x_732_);
v_x_1594__boxed_737_ = lean_unbox_usize(v_x_733_);
lean_dec(v_x_733_);
v_res_738_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__1_spec__1(v_00_u03b2_730_, v_x_731_, v_x_1593__boxed_736_, v_x_1594__boxed_737_, v_x_734_, v_x_735_);
return v_res_738_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00main_spec__3_spec__4(mut v_00_u03b2_739_: *mut lean_object, mut v_x_740_: *mut lean_object, mut v_x_741_: usize, mut v_x_742_: *mut lean_object) -> *mut lean_object{
let mut v___x_743_: *mut lean_object = core::ptr::null_mut(); 
v___x_743_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00main_spec__3_spec__4___redArg(v_x_740_, v_x_741_, v_x_742_);
return v___x_743_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00main_spec__3_spec__4___boxed(mut v_00_u03b2_744_: *mut lean_object, mut v_x_745_: *mut lean_object, mut v_x_746_: *mut lean_object, mut v_x_747_: *mut lean_object) -> *mut lean_object{
let mut v_x_1610__boxed_748_: usize = 0; let mut v_res_749_: *mut lean_object = core::ptr::null_mut(); 
v_x_1610__boxed_748_ = lean_unbox_usize(v_x_746_);
lean_dec(v_x_746_);
v_res_749_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00main_spec__3_spec__4(v_00_u03b2_744_, v_x_745_, v_x_1610__boxed_748_, v_x_747_);
lean_dec(v_x_747_);
return v_res_749_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__1_spec__1_spec__2(mut v_00_u03b2_750_: *mut lean_object, mut v_n_751_: *mut lean_object, mut v_k_752_: *mut lean_object, mut v_v_753_: *mut lean_object) -> *mut lean_object{
let mut v___x_754_: *mut lean_object = core::ptr::null_mut(); 
v___x_754_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__1_spec__1_spec__2___redArg(v_n_751_, v_k_752_, v_v_753_);
return v___x_754_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__1_spec__1_spec__3(mut v_00_u03b2_755_: *mut lean_object, mut v_depth_756_: usize, mut v_keys_757_: *mut lean_object, mut v_vals_758_: *mut lean_object, mut v_heq_759_: *mut lean_object, mut v_i_760_: *mut lean_object, mut v_entries_761_: *mut lean_object) -> *mut lean_object{
let mut v___x_762_: *mut lean_object = core::ptr::null_mut(); 
v___x_762_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__1_spec__1_spec__3___redArg(v_depth_756_, v_keys_757_, v_vals_758_, v_i_760_, v_entries_761_);
return v___x_762_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__1_spec__1_spec__3___boxed(mut v_00_u03b2_763_: *mut lean_object, mut v_depth_764_: *mut lean_object, mut v_keys_765_: *mut lean_object, mut v_vals_766_: *mut lean_object, mut v_heq_767_: *mut lean_object, mut v_i_768_: *mut lean_object, mut v_entries_769_: *mut lean_object) -> *mut lean_object{
let mut v_depth_boxed_770_: usize = 0; let mut v_res_771_: *mut lean_object = core::ptr::null_mut(); 
v_depth_boxed_770_ = lean_unbox_usize(v_depth_764_);
lean_dec(v_depth_764_);
v_res_771_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__1_spec__1_spec__3(v_00_u03b2_763_, v_depth_boxed_770_, v_keys_765_, v_vals_766_, v_heq_767_, v_i_768_, v_entries_769_);
lean_dec_ref(v_vals_766_);
lean_dec_ref(v_keys_765_);
return v_res_771_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__1_spec__1_spec__2_spec__5(mut v_00_u03b2_772_: *mut lean_object, mut v_x_773_: *mut lean_object, mut v_x_774_: *mut lean_object, mut v_x_775_: *mut lean_object, mut v_x_776_: *mut lean_object) -> *mut lean_object{
let mut v___x_777_: *mut lean_object = core::ptr::null_mut(); 
v___x_777_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__1_spec__1_spec__2_spec__5___redArg(v_x_773_, v_x_774_, v_x_775_, v_x_776_);
return v___x_777_;
}
extern "C" { fn initialize_Init(builtin: u8) -> *mut lean_object; }
extern "C" { fn initialize_Lean_Data_PersistentHashMap(builtin: u8) -> *mut lean_object; }
extern "C" { fn initialize_Lean_Data_Format(builtin: u8) -> *mut lean_object; }
static mut _G_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn initialize_phashmap3(builtin: u8) -> *mut lean_object {
let mut res: *mut lean_object = core::ptr::null_mut();
if _G_initialized { return lean_io_result_mk_ok(lean_box(0)); }
_G_initialized = true;
res = initialize_Init(builtin);
if lean_io_result_is_error(res) { return res; }
lean_dec_ref(res);
res = initialize_Lean_Data_PersistentHashMap(builtin);
if lean_io_result_is_error(res) { return res; }
lean_dec_ref(res);
res = initialize_Lean_Data_Format(builtin);
if lean_io_result_is_error(res) { return res; }
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
unsafe extern "C" fn run_main(argc: core::ffi::c_int, argv: *mut *mut core::ffi::c_char) -> *mut lean_object {
    return _lean_main();
}
#[no_mangle]
pub unsafe extern "C" fn main(argc: core::ffi::c_int, mut argv: *mut *mut core::ffi::c_char) -> core::ffi::c_int {
  argv = lean_setup_args(argc, argv);
  lean_initialize();
  let res = initialize_phashmap3(1 /* builtin */);
  lean_io_mark_end_initialization();
  let mut ret_val = 1;
  if lean_io_result_is_ok(res) {
    lean_dec(res);
    lean_init_task_manager();
    let main_res = lean_run_main(run_main, argc, argv);
    lean_finalize_task_manager();
    if lean_io_result_is_ok(main_res) {
      ret_val = 0;
      lean_dec(main_res);
    } else {
      lean_io_result_show_error(main_res);
      lean_dec(main_res);
    }
  } else {
    lean_io_result_show_error(res);
    lean_dec(res);
  }
  return ret_val;
}
