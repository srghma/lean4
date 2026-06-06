// Lean compiler output
// Module: trie
// Imports: public import Init public meta import Init public import Lean.Data.Trie
use lean_runtime::generated_abi::*;
extern "C" {
    fn lean_usize_add(_: usize, _: usize) -> usize;
    fn lean_usize_dec_eq(_: usize, _: usize) -> u8;
    fn lean_array_uget_borrowed(_: *mut lean_object, _: usize) -> *mut lean_object;
    fn lean_string_append(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_instDecidableEqString___boxed(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_string_utf8_byte_size(_: *mut lean_object) -> *mut lean_object;
    fn l_Lean_Data_Trie_matchPrefix___redArg(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_string_length(_: *mut lean_object) -> *mut lean_object;
    fn lean_nat_add(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_List_range(_: *mut lean_object) -> *mut lean_object;
    fn l_List_reverse___redArg(_: *mut lean_object) -> *mut lean_object;
    fn l_String_Slice_Pos_nextn(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_string_utf8_extract(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_array_size(_: *mut lean_object) -> usize;
    fn lean_usize_dec_lt(_: usize, _: usize) -> u8;
    fn lean_string_dec_eq(_: *mut lean_object, _: *mut lean_object) -> u8;
    fn l_Option_instDecidableEq___redArg(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> u8;
    fn lean_string_push(_: *mut lean_object, _: u32) -> *mut lean_object;
    fn lean_get_stdout() -> *mut lean_object;
    fn l_addParenHeuristic(_: *mut lean_object) -> *mut lean_object;
    fn lean_mk_empty_array_with_capacity(_: *mut lean_object) -> *mut lean_object;
    fn l_Lean_Data_Trie_empty(_: *mut lean_object) -> *mut lean_object;
    fn lean_array_push(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_array_get_size(_: *mut lean_object) -> *mut lean_object;
    fn lean_nat_dec_lt(_: *mut lean_object, _: *mut lean_object) -> u8;
    fn lean_nat_dec_le(_: *mut lean_object, _: *mut lean_object) -> u8;
    fn lean_usize_of_nat(_: *mut lean_object) -> usize;
    fn l_Lean_Data_Trie_findPrefix___redArg(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_nat_dec_eq(_: *mut lean_object, _: *mut lean_object) -> u8;
    fn lean_nat_sub(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_array_fget(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_array_fswap(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_array_fget_borrowed(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_string_dec_lt(_: *mut lean_object, _: *mut lean_object) -> u8;
    fn lean_nat_shiftr(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_string_memcmp(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> u8;
    fn l_Lean_Data_Trie_find_x3f___redArg(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_Lean_Data_Trie_insert___redArg(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
}
#[no_mangle] pub static l_keys___closed__0_value: lean_string_object<1> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_keys___closed__0: *mut lean_object = core::ptr::addr_of!(l_keys___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_keys___closed__1_value: lean_string_object<2> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [104, 0]};
static mut l_keys___closed__1: *mut lean_object = core::ptr::addr_of!(l_keys___closed__1_value) as *mut lean_object;
#[no_mangle] pub static l_keys___closed__2_value: lean_string_object<6> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [104, 101, 108, 108, 111, 0]};
static mut l_keys___closed__2: *mut lean_object = core::ptr::addr_of!(l_keys___closed__2_value) as *mut lean_object;
#[no_mangle] pub static l_keys___closed__3_value: lean_string_object<7> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [104, 101, 108, 108, 111, 111, 0]};
static mut l_keys___closed__3: *mut lean_object = core::ptr::addr_of!(l_keys___closed__3_value) as *mut lean_object;
#[no_mangle] pub static l_keys___closed__4_value: lean_string_object<8> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [104, 101, 108, 108, 111, 111, 111, 0]};
static mut l_keys___closed__4: *mut lean_object = core::ptr::addr_of!(l_keys___closed__4_value) as *mut lean_object;
#[no_mangle] pub static l_keys___closed__5_value: lean_string_object<11> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [104, 101, 108, 108, 111, 111, 111, 111, 111, 111, 0]};
static mut l_keys___closed__5: *mut lean_object = core::ptr::addr_of!(l_keys___closed__5_value) as *mut lean_object;
#[no_mangle] pub static l_keys___closed__6_value: lean_string_object<6> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [104, 101, 108, 108, 97, 0]};
static mut l_keys___closed__6: *mut lean_object = core::ptr::addr_of!(l_keys___closed__6_value) as *mut lean_object;
#[no_mangle] pub static l_keys___closed__7_value: lean_string_object<6> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [104, 101, 108, 108, 120, 0]};
static mut l_keys___closed__7: *mut lean_object = core::ptr::addr_of!(l_keys___closed__7_value) as *mut lean_object;
#[no_mangle] pub static l_keys___closed__8_value: lean_string_object<4> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 4, m_capacity: 4, m_length: 2, m_data: [104, 195, 182, 0]};
static mut l_keys___closed__8: *mut lean_object = core::ptr::addr_of!(l_keys___closed__8_value) as *mut lean_object;
#[no_mangle] pub static l_keys___closed__9_value: lean_string_object<4> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 4, m_capacity: 4, m_length: 2, m_data: [104, 195, 188, 0]};
static mut l_keys___closed__9: *mut lean_object = core::ptr::addr_of!(l_keys___closed__9_value) as *mut lean_object;
#[no_mangle] pub static l_keys___closed__10_value: lean_string_object<4> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 4, m_capacity: 4, m_length: 2, m_data: [104, 195, 164, 0]};
static mut l_keys___closed__10: *mut lean_object = core::ptr::addr_of!(l_keys___closed__10_value) as *mut lean_object;
#[no_mangle] pub static l_keys___closed__11_value: lean_string_object<5> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 5, m_capacity: 5, m_length: 1, m_data: [240, 159, 146, 169, 0]};
static mut l_keys___closed__11: *mut lean_object = core::ptr::addr_of!(l_keys___closed__11_value) as *mut lean_object;
#[no_mangle] pub static l_keys___closed__12_value: lean_array_object<12> = lean_array_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut lean_object>()*12) as u16, m_other: 0, m_tag: 246 }, m_size: 12, m_capacity: 12, m_data: [core::ptr::addr_of!(l_keys___closed__0_value) as *mut lean_object,core::ptr::addr_of!(l_keys___closed__1_value) as *mut lean_object,core::ptr::addr_of!(l_keys___closed__2_value) as *mut lean_object,core::ptr::addr_of!(l_keys___closed__3_value) as *mut lean_object,core::ptr::addr_of!(l_keys___closed__4_value) as *mut lean_object,core::ptr::addr_of!(l_keys___closed__5_value) as *mut lean_object,core::ptr::addr_of!(l_keys___closed__6_value) as *mut lean_object,core::ptr::addr_of!(l_keys___closed__7_value) as *mut lean_object,core::ptr::addr_of!(l_keys___closed__8_value) as *mut lean_object,core::ptr::addr_of!(l_keys___closed__9_value) as *mut lean_object,core::ptr::addr_of!(l_keys___closed__10_value) as *mut lean_object,core::ptr::addr_of!(l_keys___closed__11_value) as *mut lean_object] };
static mut l_keys___closed__12: *mut lean_object = core::ptr::addr_of!(l_keys___closed__12_value) as *mut lean_object;
#[no_mangle] pub static mut l_keys: *mut lean_object = core::ptr::addr_of!(l_keys___closed__12_value) as *mut lean_object;
static mut l_T_empty___closed__0_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_T_empty___closed__0: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static l_T_empty___closed__1_value: lean_array_object<0> = lean_array_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_T_empty___closed__1: *mut lean_object = core::ptr::addr_of!(l_T_empty___closed__1_value) as *mut lean_object;
static mut l_T_empty___closed__2_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_T_empty___closed__2: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static mut l_T_empty: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static l_Array_findPrefix___closed__0_value: lean_array_object<0> = lean_array_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Array_findPrefix___closed__0: *mut lean_object = core::ptr::addr_of!(l_Array_findPrefix___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_matchPrefix_spec__0___closed__0_value: lean_ctor_object<2> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 0) as u16, m_other: 2, m_tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut lean_object,((( 0 as usize) << 1) | 1) as *mut lean_object] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_matchPrefix_spec__0___closed__0: *mut lean_object = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_matchPrefix_spec__0___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00T_check_spec__2___closed__0_value: lean_string_object<11> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [115, 111, 109, 101, 80, 114, 101, 102, 105, 120, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00T_check_spec__2___closed__0: *mut lean_object = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00T_check_spec__2___closed__0_value) as *mut lean_object;
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00T_check_spec__2___closed__1_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00T_check_spec__2___closed__1: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00T_check_spec__2___closed__2_value: lean_string_object<42> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 42, m_capacity: 42, m_length: 41, m_data: [109, 97, 116, 99, 104, 80, 114, 101, 102, 105, 120, 32, 100, 105, 102, 102, 101, 114, 115, 32, 40, 119, 105, 116, 104, 32, 112, 114, 101, 102, 105, 120, 41, 58, 32, 107, 101, 121, 32, 61, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00T_check_spec__2___closed__2: *mut lean_object = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00T_check_spec__2___closed__2_value) as *mut lean_object;
#[no_mangle] pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00T_check_spec__2___closed__3_value: lean_string_object<2> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00T_check_spec__2___closed__3: *mut lean_object = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00T_check_spec__2___closed__3_value) as *mut lean_object;
#[no_mangle] pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00T_check_spec__2___closed__4_value: lean_string_object<28> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 28, m_capacity: 28, m_length: 27, m_data: [109, 97, 116, 99, 104, 80, 114, 101, 102, 105, 120, 32, 100, 105, 102, 102, 101, 114, 115, 58, 32, 107, 101, 121, 32, 61, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00T_check_spec__2___closed__4: *mut lean_object = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00T_check_spec__2___closed__4_value) as *mut lean_object;
#[no_mangle] pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00T_check_spec__2___closed__5_value: lean_string_object<8> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [44, 32, 103, 111, 116, 58, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00T_check_spec__2___closed__5: *mut lean_object = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00T_check_spec__2___closed__5_value) as *mut lean_object;
#[no_mangle] pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00T_check_spec__2___closed__6_value: lean_string_object<7> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [32, 101, 120, 112, 58, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00T_check_spec__2___closed__6: *mut lean_object = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00T_check_spec__2___closed__6_value) as *mut lean_object;
#[no_mangle] pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00T_check_spec__2___closed__7_value: lean_string_object<5> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 111, 110, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00T_check_spec__2___closed__7: *mut lean_object = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00T_check_spec__2___closed__7_value) as *mut lean_object;
#[no_mangle] pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00T_check_spec__2___closed__8_value: lean_string_object<7> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [40, 115, 111, 109, 101, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00T_check_spec__2___closed__8: *mut lean_object = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00T_check_spec__2___closed__8_value) as *mut lean_object;
#[no_mangle] pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00T_check_spec__2___closed__9_value: lean_string_object<2> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00T_check_spec__2___closed__9: *mut lean_object = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00T_check_spec__2___closed__9_value) as *mut lean_object;
#[no_mangle] pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00T_check_spec__3___closed__0_value: lean_string_object<27> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [102, 105, 110, 100, 80, 114, 101, 102, 105, 120, 32, 100, 105, 102, 102, 101, 114, 115, 58, 32, 107, 101, 121, 32, 61, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00T_check_spec__3___closed__0: *mut lean_object = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00T_check_spec__3___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00T_check_spec__4___closed__0_value: lean_string_object<22> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [102, 105, 110, 100, 63, 32, 100, 105, 102, 102, 101, 114, 115, 58, 32, 107, 101, 121, 32, 61, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00T_check_spec__4___closed__0: *mut lean_object = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00T_check_spec__4___closed__0_value) as *mut lean_object;
static mut l_T_check___closed__0_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_T_check___closed__0: *mut lean_object = core::ptr::null_mut();
static mut l_T_check___closed__1_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_T_check___closed__1: u8 = 0;
static mut l_T_check___closed__2_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_T_check___closed__2: u8 = 0;
static mut l_T_check___closed__3_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_T_check___closed__3: usize = 0;
#[no_mangle] pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__0___closed__0_value: lean_string_object<11> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [73, 110, 115, 101, 114, 116, 105, 110, 103, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__0___closed__0: *mut lean_object = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__0___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__0_value: lean_string_object<15> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [82, 101, 115, 101, 116, 116, 105, 110, 103, 32, 116, 114, 105, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__0: *mut lean_object = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__0_value: lean_array_object<9> = lean_array_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut lean_object>()*9) as u16, m_other: 0, m_tag: 246 }, m_size: 9, m_capacity: 9, m_data: [core::ptr::addr_of!(l_keys___closed__2_value) as *mut lean_object,core::ptr::addr_of!(l_keys___closed__6_value) as *mut lean_object,core::ptr::addr_of!(l_keys___closed__4_value) as *mut lean_object,core::ptr::addr_of!(l_keys___closed__1_value) as *mut lean_object,core::ptr::addr_of!(l_keys___closed__8_value) as *mut lean_object,core::ptr::addr_of!(l_keys___closed__9_value) as *mut lean_object,core::ptr::addr_of!(l_keys___closed__11_value) as *mut lean_object,core::ptr::addr_of!(l_keys___closed__0_value) as *mut lean_object,core::ptr::addr_of!(l_keys___closed__9_value) as *mut lean_object] };
static mut l_main___closed__0: *mut lean_object = core::ptr::addr_of!(l_main___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__1_value: lean_string_object<9> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [104, 101, 108, 111, 111, 111, 111, 111, 0]};
static mut l_main___closed__1: *mut lean_object = core::ptr::addr_of!(l_main___closed__1_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__2_value: lean_array_object<2> = lean_array_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut lean_object>()*2) as u16, m_other: 0, m_tag: 246 }, m_size: 2, m_capacity: 2, m_data: [core::ptr::addr_of!(l_keys___closed__0_value) as *mut lean_object,core::ptr::addr_of!(l_main___closed__1_value) as *mut lean_object] };
static mut l_main___closed__2: *mut lean_object = core::ptr::addr_of!(l_main___closed__2_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__3_value: lean_array_object<2> = lean_array_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut lean_object>()*2) as u16, m_other: 0, m_tag: 246 }, m_size: 2, m_capacity: 2, m_data: [core::ptr::addr_of!(l_main___closed__0_value) as *mut lean_object,core::ptr::addr_of!(l_main___closed__2_value) as *mut lean_object] };
static mut l_main___closed__3: *mut lean_object = core::ptr::addr_of!(l_main___closed__3_value) as *mut lean_object;
static mut l_main___closed__4_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__4: usize = 0;
#[no_mangle] pub unsafe extern "C" fn _init_l_T_empty___closed__0() -> *mut lean_object{
let mut v___x_40_: *mut lean_object = core::ptr::null_mut(); 
v___x_40_ = l_Lean_Data_Trie_empty(lean_box(0));
return v___x_40_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_T_empty___closed__2() -> *mut lean_object{
let mut v___x_43_: *mut lean_object = core::ptr::null_mut(); let mut v___x_44_: *mut lean_object = core::ptr::null_mut(); let mut v___x_45_: *mut lean_object = core::ptr::null_mut(); 
v___x_43_ = l_T_empty___closed__1;
v___x_44_ = lean_obj_once(core::ptr::addr_of_mut!(l_T_empty___closed__0), core::ptr::addr_of_mut!(l_T_empty___closed__0_once), _init_l_T_empty___closed__0);
v___x_45_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_45_, 0, v___x_44_);
lean_ctor_set(v___x_45_, 1, v___x_43_);
return v___x_45_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_T_empty() -> *mut lean_object{
let mut v___x_46_: *mut lean_object = core::ptr::null_mut(); 
v___x_46_ = lean_obj_once(core::ptr::addr_of_mut!(l_T_empty___closed__2), core::ptr::addr_of_mut!(l_T_empty___closed__2_once), _init_l_T_empty___closed__2);
return v___x_46_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00T_insert_spec__0_spec__0(mut v_a_47_: *mut lean_object, mut v_as_48_: *mut lean_object, mut v_i_49_: usize, mut v_stop_50_: usize) -> u8{
let mut v___x_51_: u8 = 0; let mut v___x_52_: *mut lean_object = core::ptr::null_mut(); let mut v___x_53_: u8 = 0; let mut v___x_54_: usize = 0; let mut v___x_55_: usize = 0; let mut v___x_57_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_51_ = lean_usize_dec_eq(v_i_49_, v_stop_50_);
if v___x_51_ == 0 {
let mut v___x_52_: *mut lean_object = core::ptr::null_mut(); let mut v___x_53_: u8 = 0; 
v___x_52_ = lean_array_uget_borrowed(v_as_48_, v_i_49_);
v___x_53_ = lean_string_dec_eq(v_a_47_, v___x_52_);
if v___x_53_ == 0 {
let mut v___x_54_: usize = 0; let mut v___x_55_: usize = 0; 
v___x_54_ = 1usize;
v___x_55_ = lean_usize_add(v_i_49_, v___x_54_);
v_i_49_ = v___x_55_;
state = 0; continue;
} else {
return v___x_53_;
}
} else {
let mut v___x_57_: u8 = 0; 
v___x_57_ = 0;
return v___x_57_;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00T_insert_spec__0_spec__0___boxed(mut v_a_58_: *mut lean_object, mut v_as_59_: *mut lean_object, mut v_i_60_: *mut lean_object, mut v_stop_61_: *mut lean_object) -> *mut lean_object{
let mut v_i_boxed_62_: usize = 0; let mut v_stop_boxed_63_: usize = 0; let mut v_res_64_: u8 = 0; let mut v_r_65_: *mut lean_object = core::ptr::null_mut(); 
v_i_boxed_62_ = lean_unbox_usize(v_i_60_);
lean_dec(v_i_60_);
v_stop_boxed_63_ = lean_unbox_usize(v_stop_61_);
lean_dec(v_stop_61_);
v_res_64_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00T_insert_spec__0_spec__0(v_a_58_, v_as_59_, v_i_boxed_62_, v_stop_boxed_63_);
lean_dec_ref(v_as_59_);
lean_dec_ref(v_a_58_);
v_r_65_ = lean_box((v_res_64_) as usize);
return v_r_65_;
}
#[no_mangle] pub unsafe extern "C" fn l_Array_contains___at___00T_insert_spec__0(mut v_as_66_: *mut lean_object, mut v_a_67_: *mut lean_object) -> u8{
let mut v___x_68_: *mut lean_object = core::ptr::null_mut(); let mut v___x_69_: *mut lean_object = core::ptr::null_mut(); let mut v___x_70_: u8 = 0; 
v___x_68_ = lean_unsigned_to_nat(0);
v___x_69_ = lean_array_get_size(v_as_66_);
v___x_70_ = lean_nat_dec_lt(v___x_68_, v___x_69_);
if v___x_70_ == 0 {
return v___x_70_;
} else {
if v___x_70_ == 0 {
return v___x_70_;
} else {
let mut v___x_71_: usize = 0; let mut v___x_72_: usize = 0; let mut v___x_73_: u8 = 0; 
v___x_71_ = 0usize;
v___x_72_ = lean_usize_of_nat(v___x_69_);
v___x_73_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00T_insert_spec__0_spec__0(v_a_67_, v_as_66_, v___x_71_, v___x_72_);
return v___x_73_;
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Array_contains___at___00T_insert_spec__0___boxed(mut v_as_74_: *mut lean_object, mut v_a_75_: *mut lean_object) -> *mut lean_object{
let mut v_res_76_: u8 = 0; let mut v_r_77_: *mut lean_object = core::ptr::null_mut(); 
v_res_76_ = l_Array_contains___at___00T_insert_spec__0(v_as_74_, v_a_75_);
lean_dec_ref(v_a_75_);
lean_dec_ref(v_as_74_);
v_r_77_ = lean_box((v_res_76_) as usize);
return v_r_77_;
}
#[no_mangle] pub unsafe extern "C" fn l_T_insert(mut v_x_78_: *mut lean_object, mut v_s_79_: *mut lean_object) -> *mut lean_object{
let mut v_fst_80_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_81_: *mut lean_object = core::ptr::null_mut(); let mut v___x_83_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_84_: u8 = 0; let mut v___x_85_: *mut lean_object = core::ptr::null_mut(); let mut v___x_86_: u8 = 0; let mut v___x_87_: *mut lean_object = core::ptr::null_mut(); let mut v___x_89_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_90_: *mut lean_object = core::ptr::null_mut(); let mut v___x_92_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_93_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_94_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v_fst_80_ = lean_ctor_get(v_x_78_, 0);
v_snd_81_ = lean_ctor_get(v_x_78_, 1);
v_isSharedCheck_94_ = (!lean_is_exclusive(v_x_78_)) as u8;
if v_isSharedCheck_94_ == 0 {
v___x_83_ = v_x_78_;
v_isShared_84_ = v_isSharedCheck_94_;
state = 1; continue;
} else {
lean_inc(v_snd_81_);
lean_inc(v_fst_80_);
lean_dec(v_x_78_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_94_;
state = 1; continue;
}
}
1 => {
lean_inc_ref(v_s_79_);
v___x_85_ = l_Lean_Data_Trie_insert___redArg(v_fst_80_, v_s_79_, v_s_79_);
v___x_86_ = l_Array_contains___at___00T_insert_spec__0(v_snd_81_, v_s_79_);
if v___x_86_ == 0 {
let mut v___x_87_: *mut lean_object = core::ptr::null_mut(); let mut v___x_89_: *mut lean_object = core::ptr::null_mut(); 
v___x_87_ = lean_array_push(v_snd_81_, v_s_79_);
if v_isShared_84_ == 0 {
lean_ctor_set(v___x_83_, 1, v___x_87_);
lean_ctor_set(v___x_83_, 0, v___x_85_);
v___x_89_ = v___x_83_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_90_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_90_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_90_, 0, v___x_85_);
lean_ctor_set(v_reuseFailAlloc_90_, 1, v___x_87_);
v___x_89_ = v_reuseFailAlloc_90_;
state = 2; continue;
}
} else {
let mut v___x_92_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref(v_s_79_);
if v_isShared_84_ == 0 {
lean_ctor_set(v___x_83_, 0, v___x_85_);
v___x_92_ = v___x_83_;
state = 3; continue;
} else {
let mut v_reuseFailAlloc_93_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_93_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_93_, 0, v___x_85_);
lean_ctor_set(v_reuseFailAlloc_93_, 1, v_snd_81_);
v___x_92_ = v_reuseFailAlloc_93_;
state = 3; continue;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Array_sorted_spec__0_spec__0___redArg(mut v_hi_95_: *mut lean_object, mut v_pivot_96_: *mut lean_object, mut v_as_97_: *mut lean_object, mut v_i_98_: *mut lean_object, mut v_k_99_: *mut lean_object) -> *mut lean_object{
let mut v___x_100_: u8 = 0; let mut v___x_101_: *mut lean_object = core::ptr::null_mut(); let mut v___x_102_: *mut lean_object = core::ptr::null_mut(); let mut v___x_103_: *mut lean_object = core::ptr::null_mut(); let mut v___x_104_: u8 = 0; let mut v___x_105_: *mut lean_object = core::ptr::null_mut(); let mut v___x_106_: *mut lean_object = core::ptr::null_mut(); let mut v___x_108_: *mut lean_object = core::ptr::null_mut(); let mut v___x_109_: *mut lean_object = core::ptr::null_mut(); let mut v___x_110_: *mut lean_object = core::ptr::null_mut(); let mut v___x_111_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_100_ = lean_nat_dec_lt(v_k_99_, v_hi_95_);
if v___x_100_ == 0 {
let mut v___x_101_: *mut lean_object = core::ptr::null_mut(); let mut v___x_102_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_k_99_);
v___x_101_ = lean_array_fswap(v_as_97_, v_i_98_, v_hi_95_);
v___x_102_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_102_, 0, v_i_98_);
lean_ctor_set(v___x_102_, 1, v___x_101_);
return v___x_102_;
} else {
let mut v___x_103_: *mut lean_object = core::ptr::null_mut(); let mut v___x_104_: u8 = 0; 
v___x_103_ = lean_array_fget_borrowed(v_as_97_, v_k_99_);
v___x_104_ = lean_string_dec_lt(v___x_103_, v_pivot_96_);
if v___x_104_ == 0 {
let mut v___x_105_: *mut lean_object = core::ptr::null_mut(); let mut v___x_106_: *mut lean_object = core::ptr::null_mut(); 
v___x_105_ = lean_unsigned_to_nat(1);
v___x_106_ = lean_nat_add(v_k_99_, v___x_105_);
lean_dec(v_k_99_);
v_k_99_ = v___x_106_;
state = 0; continue;
} else {
let mut v___x_108_: *mut lean_object = core::ptr::null_mut(); let mut v___x_109_: *mut lean_object = core::ptr::null_mut(); let mut v___x_110_: *mut lean_object = core::ptr::null_mut(); let mut v___x_111_: *mut lean_object = core::ptr::null_mut(); 
v___x_108_ = lean_array_fswap(v_as_97_, v_i_98_, v_k_99_);
v___x_109_ = lean_unsigned_to_nat(1);
v___x_110_ = lean_nat_add(v_i_98_, v___x_109_);
lean_dec(v_i_98_);
v___x_111_ = lean_nat_add(v_k_99_, v___x_109_);
lean_dec(v_k_99_);
v_as_97_ = v___x_108_;
v_i_98_ = v___x_110_;
v_k_99_ = v___x_111_;
state = 0; continue;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Array_sorted_spec__0_spec__0___redArg___boxed(mut v_hi_113_: *mut lean_object, mut v_pivot_114_: *mut lean_object, mut v_as_115_: *mut lean_object, mut v_i_116_: *mut lean_object, mut v_k_117_: *mut lean_object) -> *mut lean_object{
let mut v_res_118_: *mut lean_object = core::ptr::null_mut(); 
v_res_118_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Array_sorted_spec__0_spec__0___redArg(v_hi_113_, v_pivot_114_, v_as_115_, v_i_116_, v_k_117_);
lean_dec_ref(v_pivot_114_);
lean_dec(v_hi_113_);
return v_res_118_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Array_sorted_spec__0___redArg(mut v_n_119_: *mut lean_object, mut v_as_120_: *mut lean_object, mut v_lo_121_: *mut lean_object, mut v_hi_122_: *mut lean_object) -> *mut lean_object{
let mut v___y_124_: *mut lean_object = core::ptr::null_mut(); let mut v_pivot_125_: *mut lean_object = core::ptr::null_mut(); let mut v___x_126_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_127_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_128_: *mut lean_object = core::ptr::null_mut(); let mut v___x_129_: u8 = 0; let mut v___x_130_: *mut lean_object = core::ptr::null_mut(); let mut v___x_131_: *mut lean_object = core::ptr::null_mut(); let mut v___x_132_: *mut lean_object = core::ptr::null_mut(); let mut v___x_134_: u8 = 0; let mut v___x_135_: *mut lean_object = core::ptr::null_mut(); let mut v___x_136_: *mut lean_object = core::ptr::null_mut(); let mut v_mid_137_: *mut lean_object = core::ptr::null_mut(); let mut v___y_139_: *mut lean_object = core::ptr::null_mut(); let mut v___x_140_: *mut lean_object = core::ptr::null_mut(); let mut v___x_141_: *mut lean_object = core::ptr::null_mut(); let mut v___x_142_: u8 = 0; let mut v___x_143_: *mut lean_object = core::ptr::null_mut(); let mut v___y_145_: *mut lean_object = core::ptr::null_mut(); let mut v___x_146_: *mut lean_object = core::ptr::null_mut(); let mut v___x_147_: *mut lean_object = core::ptr::null_mut(); let mut v___x_148_: u8 = 0; let mut v___x_149_: *mut lean_object = core::ptr::null_mut(); let mut v___x_150_: *mut lean_object = core::ptr::null_mut(); let mut v___x_151_: *mut lean_object = core::ptr::null_mut(); let mut v___x_152_: u8 = 0; let mut v___x_153_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_134_ = lean_nat_dec_lt(v_lo_121_, v_hi_122_);
if v___x_134_ == 0 {
lean_dec(v_lo_121_);
return v_as_120_;
} else {
let mut v___x_135_: *mut lean_object = core::ptr::null_mut(); let mut v___x_136_: *mut lean_object = core::ptr::null_mut(); let mut v_mid_137_: *mut lean_object = core::ptr::null_mut(); let mut v___y_139_: *mut lean_object = core::ptr::null_mut(); let mut v___y_145_: *mut lean_object = core::ptr::null_mut(); let mut v___x_150_: *mut lean_object = core::ptr::null_mut(); let mut v___x_151_: *mut lean_object = core::ptr::null_mut(); let mut v___x_152_: u8 = 0; 
v___x_135_ = lean_nat_add(v_lo_121_, v_hi_122_);
v___x_136_ = lean_unsigned_to_nat(1);
v_mid_137_ = lean_nat_shiftr(v___x_135_, v___x_136_);
lean_dec(v___x_135_);
v___x_150_ = lean_array_fget_borrowed(v_as_120_, v_mid_137_);
v___x_151_ = lean_array_fget_borrowed(v_as_120_, v_lo_121_);
v___x_152_ = lean_string_dec_lt(v___x_150_, v___x_151_);
if v___x_152_ == 0 {
v___y_145_ = v_as_120_;
state = 3; continue;
} else {
let mut v___x_153_: *mut lean_object = core::ptr::null_mut(); 
v___x_153_ = lean_array_fswap(v_as_120_, v_lo_121_, v_mid_137_);
v___y_145_ = v___x_153_;
state = 3; continue;
}
}
}
1 => {
v_pivot_125_ = lean_array_fget(v___y_124_, v_hi_122_);
lean_inc_n(v_lo_121_, 2);
v___x_126_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Array_sorted_spec__0_spec__0___redArg(v_hi_122_, v_pivot_125_, v___y_124_, v_lo_121_, v_lo_121_);
lean_dec(v_pivot_125_);
v_fst_127_ = lean_ctor_get(v___x_126_, 0);
lean_inc(v_fst_127_);
v_snd_128_ = lean_ctor_get(v___x_126_, 1);
lean_inc(v_snd_128_);
lean_dec_ref(v___x_126_);
v___x_129_ = lean_nat_dec_le(v_hi_122_, v_fst_127_);
if v___x_129_ == 0 {
let mut v___x_130_: *mut lean_object = core::ptr::null_mut(); let mut v___x_131_: *mut lean_object = core::ptr::null_mut(); let mut v___x_132_: *mut lean_object = core::ptr::null_mut(); 
v___x_130_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Array_sorted_spec__0___redArg(v_n_119_, v_snd_128_, v_lo_121_, v_fst_127_);
v___x_131_ = lean_unsigned_to_nat(1);
v___x_132_ = lean_nat_add(v_fst_127_, v___x_131_);
lean_dec(v_fst_127_);
v_as_120_ = v___x_130_;
v_lo_121_ = v___x_132_;
state = 0; continue;
} else {
lean_dec(v_fst_127_);
lean_dec(v_lo_121_);
return v_snd_128_;
}
}
2 => {
v___x_140_ = lean_array_fget_borrowed(v___y_139_, v_mid_137_);
v___x_141_ = lean_array_fget_borrowed(v___y_139_, v_hi_122_);
v___x_142_ = lean_string_dec_lt(v___x_140_, v___x_141_);
if v___x_142_ == 0 {
lean_dec(v_mid_137_);
v___y_124_ = v___y_139_;
state = 1; continue;
} else {
let mut v___x_143_: *mut lean_object = core::ptr::null_mut(); 
v___x_143_ = lean_array_fswap(v___y_139_, v_mid_137_, v_hi_122_);
lean_dec(v_mid_137_);
v___y_124_ = v___x_143_;
state = 1; continue;
}
}
3 => {
v___x_146_ = lean_array_fget_borrowed(v___y_145_, v_hi_122_);
v___x_147_ = lean_array_fget_borrowed(v___y_145_, v_lo_121_);
v___x_148_ = lean_string_dec_lt(v___x_146_, v___x_147_);
if v___x_148_ == 0 {
v___y_139_ = v___y_145_;
state = 2; continue;
} else {
let mut v___x_149_: *mut lean_object = core::ptr::null_mut(); 
v___x_149_ = lean_array_fswap(v___y_145_, v_lo_121_, v_hi_122_);
v___y_139_ = v___x_149_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Array_sorted_spec__0___redArg___boxed(mut v_n_154_: *mut lean_object, mut v_as_155_: *mut lean_object, mut v_lo_156_: *mut lean_object, mut v_hi_157_: *mut lean_object) -> *mut lean_object{
let mut v_res_158_: *mut lean_object = core::ptr::null_mut(); 
v_res_158_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Array_sorted_spec__0___redArg(v_n_154_, v_as_155_, v_lo_156_, v_hi_157_);
lean_dec(v_hi_157_);
lean_dec(v_n_154_);
return v_res_158_;
}
#[no_mangle] pub unsafe extern "C" fn l_Array_sorted(mut v_a_159_: *mut lean_object) -> *mut lean_object{
let mut v___x_160_: *mut lean_object = core::ptr::null_mut(); let mut v___x_161_: *mut lean_object = core::ptr::null_mut(); let mut v___x_162_: u8 = 0; let mut v___x_163_: *mut lean_object = core::ptr::null_mut(); let mut v___x_164_: *mut lean_object = core::ptr::null_mut(); let mut v___y_166_: *mut lean_object = core::ptr::null_mut(); let mut v___x_167_: u8 = 0; let mut v___x_168_: *mut lean_object = core::ptr::null_mut(); let mut v___x_169_: *mut lean_object = core::ptr::null_mut(); let mut v___x_170_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_160_ = lean_array_get_size(v_a_159_);
v___x_161_ = lean_unsigned_to_nat(0);
v___x_162_ = lean_nat_dec_eq(v___x_160_, v___x_161_);
if v___x_162_ == 0 {
let mut v___x_163_: *mut lean_object = core::ptr::null_mut(); let mut v___x_164_: *mut lean_object = core::ptr::null_mut(); let mut v___y_166_: *mut lean_object = core::ptr::null_mut(); let mut v___x_170_: u8 = 0; 
v___x_163_ = lean_unsigned_to_nat(1);
v___x_164_ = lean_nat_sub(v___x_160_, v___x_163_);
v___x_170_ = lean_nat_dec_le(v___x_161_, v___x_164_);
if v___x_170_ == 0 {
lean_inc(v___x_164_);
v___y_166_ = v___x_164_;
state = 1; continue;
} else {
v___y_166_ = v___x_161_;
state = 1; continue;
}
} else {
return v_a_159_;
}
}
1 => {
v___x_167_ = lean_nat_dec_le(v___y_166_, v___x_164_);
if v___x_167_ == 0 {
let mut v___x_168_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v___x_164_);
lean_inc(v___y_166_);
v___x_168_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Array_sorted_spec__0___redArg(v___x_160_, v_a_159_, v___y_166_, v___y_166_);
lean_dec(v___y_166_);
return v___x_168_;
} else {
let mut v___x_169_: *mut lean_object = core::ptr::null_mut(); 
v___x_169_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Array_sorted_spec__0___redArg(v___x_160_, v_a_159_, v___y_166_, v___x_164_);
lean_dec(v___x_164_);
return v___x_169_;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Array_sorted_spec__0(mut v_n_171_: *mut lean_object, mut v_as_172_: *mut lean_object, mut v_lo_173_: *mut lean_object, mut v_hi_174_: *mut lean_object, mut v_w_175_: *mut lean_object, mut v_hlo_176_: *mut lean_object, mut v_hhi_177_: *mut lean_object) -> *mut lean_object{
let mut v___x_178_: *mut lean_object = core::ptr::null_mut(); 
v___x_178_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Array_sorted_spec__0___redArg(v_n_171_, v_as_172_, v_lo_173_, v_hi_174_);
return v___x_178_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Array_sorted_spec__0___boxed(mut v_n_179_: *mut lean_object, mut v_as_180_: *mut lean_object, mut v_lo_181_: *mut lean_object, mut v_hi_182_: *mut lean_object, mut v_w_183_: *mut lean_object, mut v_hlo_184_: *mut lean_object, mut v_hhi_185_: *mut lean_object) -> *mut lean_object{
let mut v_res_186_: *mut lean_object = core::ptr::null_mut(); 
v_res_186_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Array_sorted_spec__0(v_n_179_, v_as_180_, v_lo_181_, v_hi_182_, v_w_183_, v_hlo_184_, v_hhi_185_);
lean_dec(v_hi_182_);
lean_dec(v_n_179_);
return v_res_186_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Array_sorted_spec__0_spec__0(mut v_n_187_: *mut lean_object, mut v_lo_188_: *mut lean_object, mut v_hi_189_: *mut lean_object, mut v_hhi_190_: *mut lean_object, mut v_pivot_191_: *mut lean_object, mut v_as_192_: *mut lean_object, mut v_i_193_: *mut lean_object, mut v_k_194_: *mut lean_object, mut v_ilo_195_: *mut lean_object, mut v_ik_196_: *mut lean_object, mut v_w_197_: *mut lean_object) -> *mut lean_object{
let mut v___x_198_: *mut lean_object = core::ptr::null_mut(); 
v___x_198_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Array_sorted_spec__0_spec__0___redArg(v_hi_189_, v_pivot_191_, v_as_192_, v_i_193_, v_k_194_);
return v___x_198_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Array_sorted_spec__0_spec__0___boxed(mut v_n_199_: *mut lean_object, mut v_lo_200_: *mut lean_object, mut v_hi_201_: *mut lean_object, mut v_hhi_202_: *mut lean_object, mut v_pivot_203_: *mut lean_object, mut v_as_204_: *mut lean_object, mut v_i_205_: *mut lean_object, mut v_k_206_: *mut lean_object, mut v_ilo_207_: *mut lean_object, mut v_ik_208_: *mut lean_object, mut v_w_209_: *mut lean_object) -> *mut lean_object{
let mut v_res_210_: *mut lean_object = core::ptr::null_mut(); 
v_res_210_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Array_sorted_spec__0_spec__0(v_n_199_, v_lo_200_, v_hi_201_, v_hhi_202_, v_pivot_203_, v_as_204_, v_i_205_, v_k_206_, v_ilo_207_, v_ik_208_, v_w_209_);
lean_dec_ref(v_pivot_203_);
lean_dec(v_hi_201_);
lean_dec(v_lo_200_);
lean_dec(v_n_199_);
return v_res_210_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_findPrefix_spec__0(mut v_s_211_: *mut lean_object, mut v_as_212_: *mut lean_object, mut v_i_213_: usize, mut v_stop_214_: usize, mut v_b_215_: *mut lean_object) -> *mut lean_object{
let mut v___y_217_: *mut lean_object = core::ptr::null_mut(); let mut v___x_218_: usize = 0; let mut v___x_219_: usize = 0; let mut v___x_221_: u8 = 0; let mut v___x_222_: *mut lean_object = core::ptr::null_mut(); let mut v___x_223_: *mut lean_object = core::ptr::null_mut(); let mut v___x_224_: *mut lean_object = core::ptr::null_mut(); let mut v___x_225_: u8 = 0; let mut v___x_226_: *mut lean_object = core::ptr::null_mut(); let mut v___x_227_: u8 = 0; let mut v___x_228_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_221_ = lean_usize_dec_eq(v_i_213_, v_stop_214_);
if v___x_221_ == 0 {
let mut v___x_222_: *mut lean_object = core::ptr::null_mut(); let mut v___x_223_: *mut lean_object = core::ptr::null_mut(); let mut v___x_224_: *mut lean_object = core::ptr::null_mut(); let mut v___x_225_: u8 = 0; 
v___x_222_ = lean_array_uget_borrowed(v_as_212_, v_i_213_);
v___x_223_ = lean_string_utf8_byte_size(v___x_222_);
v___x_224_ = lean_string_utf8_byte_size(v_s_211_);
v___x_225_ = lean_nat_dec_le(v___x_224_, v___x_223_);
if v___x_225_ == 0 {
v___y_217_ = v_b_215_;
state = 1; continue;
} else {
let mut v___x_226_: *mut lean_object = core::ptr::null_mut(); let mut v___x_227_: u8 = 0; 
v___x_226_ = lean_unsigned_to_nat(0);
v___x_227_ = lean_string_memcmp(v___x_222_, v_s_211_, v___x_226_, v___x_226_, v___x_224_);
if v___x_227_ == 0 {
v___y_217_ = v_b_215_;
state = 1; continue;
} else {
let mut v___x_228_: *mut lean_object = core::ptr::null_mut(); 
lean_inc(v___x_222_);
v___x_228_ = lean_array_push(v_b_215_, v___x_222_);
v___y_217_ = v___x_228_;
state = 1; continue;
}
}
} else {
return v_b_215_;
}
}
1 => {
v___x_218_ = 1usize;
v___x_219_ = lean_usize_add(v_i_213_, v___x_218_);
v_i_213_ = v___x_219_;
v_b_215_ = v___y_217_;
state = 0; continue;
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_findPrefix_spec__0___boxed(mut v_s_229_: *mut lean_object, mut v_as_230_: *mut lean_object, mut v_i_231_: *mut lean_object, mut v_stop_232_: *mut lean_object, mut v_b_233_: *mut lean_object) -> *mut lean_object{
let mut v_i_boxed_234_: usize = 0; let mut v_stop_boxed_235_: usize = 0; let mut v_res_236_: *mut lean_object = core::ptr::null_mut(); 
v_i_boxed_234_ = lean_unbox_usize(v_i_231_);
lean_dec(v_i_231_);
v_stop_boxed_235_ = lean_unbox_usize(v_stop_232_);
lean_dec(v_stop_232_);
v_res_236_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_findPrefix_spec__0(v_s_229_, v_as_230_, v_i_boxed_234_, v_stop_boxed_235_, v_b_233_);
lean_dec_ref(v_as_230_);
lean_dec_ref(v_s_229_);
return v_res_236_;
}
#[no_mangle] pub unsafe extern "C" fn l_Array_findPrefix(mut v_a_239_: *mut lean_object, mut v_s_240_: *mut lean_object) -> *mut lean_object{
let mut v___x_241_: *mut lean_object = core::ptr::null_mut(); let mut v___x_242_: *mut lean_object = core::ptr::null_mut(); let mut v___x_243_: *mut lean_object = core::ptr::null_mut(); let mut v___x_244_: u8 = 0; 
v___x_241_ = lean_unsigned_to_nat(0);
v___x_242_ = lean_array_get_size(v_a_239_);
v___x_243_ = l_Array_findPrefix___closed__0;
v___x_244_ = lean_nat_dec_lt(v___x_241_, v___x_242_);
if v___x_244_ == 0 {
return v___x_243_;
} else {
let mut v___x_245_: u8 = 0; 
v___x_245_ = lean_nat_dec_le(v___x_242_, v___x_242_);
if v___x_245_ == 0 {
if v___x_244_ == 0 {
return v___x_243_;
} else {
let mut v___x_246_: usize = 0; let mut v___x_247_: usize = 0; let mut v___x_248_: *mut lean_object = core::ptr::null_mut(); 
v___x_246_ = 0usize;
v___x_247_ = lean_usize_of_nat(v___x_242_);
v___x_248_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_findPrefix_spec__0(v_s_240_, v_a_239_, v___x_246_, v___x_247_, v___x_243_);
return v___x_248_;
}
} else {
let mut v___x_249_: usize = 0; let mut v___x_250_: usize = 0; let mut v___x_251_: *mut lean_object = core::ptr::null_mut(); 
v___x_249_ = 0usize;
v___x_250_ = lean_usize_of_nat(v___x_242_);
v___x_251_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_findPrefix_spec__0(v_s_240_, v_a_239_, v___x_249_, v___x_250_, v___x_243_);
return v___x_251_;
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Array_findPrefix___boxed(mut v_a_252_: *mut lean_object, mut v_s_253_: *mut lean_object) -> *mut lean_object{
let mut v_res_254_: *mut lean_object = core::ptr::null_mut(); 
v_res_254_ = l_Array_findPrefix(v_a_252_, v_s_253_);
lean_dec_ref(v_s_253_);
lean_dec_ref(v_a_252_);
return v_res_254_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_matchPrefix_spec__0(mut v___x_258_: *mut lean_object, mut v_as_259_: *mut lean_object, mut v_sz_260_: usize, mut v_i_261_: usize, mut v_b_262_: *mut lean_object) -> *mut lean_object{
let mut v___x_263_: u8 = 0; let mut v___x_264_: *mut lean_object = core::ptr::null_mut(); let mut v_a_265_: *mut lean_object = core::ptr::null_mut(); let mut v___x_266_: u8 = 0; let mut v___x_267_: *mut lean_object = core::ptr::null_mut(); let mut v___x_268_: usize = 0; let mut v___x_269_: usize = 0; let mut v___x_271_: *mut lean_object = core::ptr::null_mut(); let mut v___x_272_: *mut lean_object = core::ptr::null_mut(); let mut v___x_273_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_263_ = lean_usize_dec_lt(v_i_261_, v_sz_260_);
if v___x_263_ == 0 {
lean_inc_ref(v_b_262_);
return v_b_262_;
} else {
let mut v___x_264_: *mut lean_object = core::ptr::null_mut(); let mut v_a_265_: *mut lean_object = core::ptr::null_mut(); let mut v___x_266_: u8 = 0; 
v___x_264_ = lean_box(0);
v_a_265_ = lean_array_uget_borrowed(v_as_259_, v_i_261_);
v___x_266_ = lean_string_dec_eq(v_a_265_, v___x_258_);
if v___x_266_ == 0 {
let mut v___x_267_: *mut lean_object = core::ptr::null_mut(); let mut v___x_268_: usize = 0; let mut v___x_269_: usize = 0; 
v___x_267_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_matchPrefix_spec__0___closed__0;
v___x_268_ = 1usize;
v___x_269_ = lean_usize_add(v_i_261_, v___x_268_);
v_i_261_ = v___x_269_;
v_b_262_ = v___x_267_;
state = 0; continue;
} else {
let mut v___x_271_: *mut lean_object = core::ptr::null_mut(); let mut v___x_272_: *mut lean_object = core::ptr::null_mut(); let mut v___x_273_: *mut lean_object = core::ptr::null_mut(); 
lean_inc(v_a_265_);
v___x_271_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v___x_271_, 0, v_a_265_);
v___x_272_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v___x_272_, 0, v___x_271_);
v___x_273_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_273_, 0, v___x_272_);
lean_ctor_set(v___x_273_, 1, v___x_264_);
return v___x_273_;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_matchPrefix_spec__0___boxed(mut v___x_274_: *mut lean_object, mut v_as_275_: *mut lean_object, mut v_sz_276_: *mut lean_object, mut v_i_277_: *mut lean_object, mut v_b_278_: *mut lean_object) -> *mut lean_object{
let mut v_sz_boxed_279_: usize = 0; let mut v_i_boxed_280_: usize = 0; let mut v_res_281_: *mut lean_object = core::ptr::null_mut(); 
v_sz_boxed_279_ = lean_unbox_usize(v_sz_276_);
lean_dec(v_sz_276_);
v_i_boxed_280_ = lean_unbox_usize(v_i_277_);
lean_dec(v_i_277_);
v_res_281_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_matchPrefix_spec__0(v___x_274_, v_as_275_, v_sz_boxed_279_, v_i_boxed_280_, v_b_278_);
lean_dec_ref(v_b_278_);
lean_dec_ref(v_as_275_);
lean_dec_ref(v___x_274_);
return v_res_281_;
}
#[no_mangle] pub unsafe extern "C" fn l_List_forIn_x27_loop___at___00Array_matchPrefix_spec__1___redArg(mut v_s_282_: *mut lean_object, mut v_a_283_: *mut lean_object, mut v_as_x27_284_: *mut lean_object, mut v_b_285_: *mut lean_object) -> *mut lean_object{
let mut v_head_286_: *mut lean_object = core::ptr::null_mut(); let mut v_tail_287_: *mut lean_object = core::ptr::null_mut(); let mut v___x_288_: *mut lean_object = core::ptr::null_mut(); let mut v___x_289_: *mut lean_object = core::ptr::null_mut(); let mut v___x_290_: *mut lean_object = core::ptr::null_mut(); let mut v___x_291_: *mut lean_object = core::ptr::null_mut(); let mut v___x_292_: *mut lean_object = core::ptr::null_mut(); let mut v___x_293_: *mut lean_object = core::ptr::null_mut(); let mut v___x_294_: *mut lean_object = core::ptr::null_mut(); let mut v_sz_295_: usize = 0; let mut v___x_296_: usize = 0; let mut v___x_297_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_298_: *mut lean_object = core::ptr::null_mut(); let mut v___x_300_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_301_: u8 = 0; let mut v_val_303_: *mut lean_object = core::ptr::null_mut(); let mut v___x_305_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_306_: u8 = 0; let mut v___x_308_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_309_: u8 = 0; let mut v___x_311_: *mut lean_object = core::ptr::null_mut(); let mut v___x_313_: *mut lean_object = core::ptr::null_mut(); let mut v___x_315_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_316_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_317_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_318_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_319_: u8 = 0; let mut v_unused_320_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_322_: u8 = 0; let mut v_isSharedCheck_323_: u8 = 0; let mut v_unused_324_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_as_x27_284_) == 0 {
lean_dec_ref(v_s_282_);
lean_inc_ref(v_b_285_);
return v_b_285_;
} else {
let mut v_head_286_: *mut lean_object = core::ptr::null_mut(); let mut v_tail_287_: *mut lean_object = core::ptr::null_mut(); let mut v___x_288_: *mut lean_object = core::ptr::null_mut(); let mut v___x_289_: *mut lean_object = core::ptr::null_mut(); let mut v___x_290_: *mut lean_object = core::ptr::null_mut(); let mut v___x_291_: *mut lean_object = core::ptr::null_mut(); let mut v___x_292_: *mut lean_object = core::ptr::null_mut(); let mut v___x_293_: *mut lean_object = core::ptr::null_mut(); let mut v___x_294_: *mut lean_object = core::ptr::null_mut(); let mut v_sz_295_: usize = 0; let mut v___x_296_: usize = 0; let mut v___x_297_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_298_: *mut lean_object = core::ptr::null_mut(); let mut v___x_300_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_301_: u8 = 0; let mut v_isSharedCheck_323_: u8 = 0; 
v_head_286_ = lean_ctor_get(v_as_x27_284_, 0);
v_tail_287_ = lean_ctor_get(v_as_x27_284_, 1);
v___x_288_ = lean_box(0);
v___x_289_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_matchPrefix_spec__0___closed__0;
v___x_290_ = lean_unsigned_to_nat(0);
v___x_291_ = lean_string_utf8_byte_size(v_s_282_);
lean_inc_ref(v_s_282_);
v___x_292_ = lean_alloc_ctor(0, 3, (0) as u32);
lean_ctor_set(v___x_292_, 0, v_s_282_);
lean_ctor_set(v___x_292_, 1, v___x_290_);
lean_ctor_set(v___x_292_, 2, v___x_291_);
lean_inc(v_head_286_);
v___x_293_ = l_String_Slice_Pos_nextn(v___x_292_, v___x_290_, v_head_286_);
lean_dec_ref_known(v___x_292_, 3);
v___x_294_ = lean_string_utf8_extract(v_s_282_, v___x_290_, v___x_293_);
lean_dec(v___x_293_);
v_sz_295_ = lean_array_size(v_a_283_);
v___x_296_ = 0usize;
v___x_297_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_matchPrefix_spec__0(v___x_294_, v_a_283_, v_sz_295_, v___x_296_, v___x_289_);
v_fst_298_ = lean_ctor_get(v___x_297_, 0);
v_isSharedCheck_323_ = (!lean_is_exclusive(v___x_297_)) as u8;
if v_isSharedCheck_323_ == 0 {
let mut v_unused_324_: *mut lean_object = core::ptr::null_mut(); 
v_unused_324_ = lean_ctor_get(v___x_297_, 1);
lean_dec(v_unused_324_);
v___x_300_ = v___x_297_;
v_isShared_301_ = v_isSharedCheck_323_;
state = 1; continue;
} else {
lean_inc(v_fst_298_);
lean_dec(v___x_297_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_323_;
state = 1; continue;
}
}
}
1 => {
if lean_obj_tag(v_fst_298_) == 0 {
lean_del_object(v___x_300_);
lean_dec_ref(v___x_294_);
v_as_x27_284_ = v_tail_287_;
v_b_285_ = v___x_289_;
state = 0; continue;
} else {
let mut v_val_303_: *mut lean_object = core::ptr::null_mut(); let mut v___x_305_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_306_: u8 = 0; let mut v_isSharedCheck_322_: u8 = 0; 
v_val_303_ = lean_ctor_get(v_fst_298_, 0);
v_isSharedCheck_322_ = (!lean_is_exclusive(v_fst_298_)) as u8;
if v_isSharedCheck_322_ == 0 {
v___x_305_ = v_fst_298_;
v_isShared_306_ = v_isSharedCheck_322_;
state = 2; continue;
} else {
lean_inc(v_val_303_);
lean_dec(v_fst_298_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_322_;
state = 2; continue;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_List_forIn_x27_loop___at___00Array_matchPrefix_spec__1___redArg___boxed(mut v_s_325_: *mut lean_object, mut v_a_326_: *mut lean_object, mut v_as_x27_327_: *mut lean_object, mut v_b_328_: *mut lean_object) -> *mut lean_object{
let mut v_res_329_: *mut lean_object = core::ptr::null_mut(); 
v_res_329_ = l_List_forIn_x27_loop___at___00Array_matchPrefix_spec__1___redArg(v_s_325_, v_a_326_, v_as_x27_327_, v_b_328_);
lean_dec_ref(v_b_328_);
lean_dec(v_as_x27_327_);
lean_dec_ref(v_a_326_);
return v_res_329_;
}
#[no_mangle] pub unsafe extern "C" fn l_Array_matchPrefix(mut v_a_330_: *mut lean_object, mut v_s_331_: *mut lean_object) -> *mut lean_object{
let mut v___x_332_: *mut lean_object = core::ptr::null_mut(); let mut v___x_333_: *mut lean_object = core::ptr::null_mut(); let mut v___x_334_: *mut lean_object = core::ptr::null_mut(); let mut v___x_335_: *mut lean_object = core::ptr::null_mut(); let mut v___x_336_: *mut lean_object = core::ptr::null_mut(); let mut v___x_337_: *mut lean_object = core::ptr::null_mut(); let mut v___x_338_: *mut lean_object = core::ptr::null_mut(); let mut v___x_339_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_340_: *mut lean_object = core::ptr::null_mut(); 
v___x_332_ = lean_string_length(v_s_331_);
v___x_333_ = lean_unsigned_to_nat(1);
v___x_334_ = lean_nat_add(v___x_332_, v___x_333_);
v___x_335_ = l_List_range(v___x_334_);
v___x_336_ = l_List_reverse___redArg(v___x_335_);
v___x_337_ = lean_box(0);
v___x_338_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_matchPrefix_spec__0___closed__0;
v___x_339_ = l_List_forIn_x27_loop___at___00Array_matchPrefix_spec__1___redArg(v_s_331_, v_a_330_, v___x_336_, v___x_338_);
lean_dec(v___x_336_);
v_fst_340_ = lean_ctor_get(v___x_339_, 0);
lean_inc(v_fst_340_);
lean_dec_ref(v___x_339_);
if lean_obj_tag(v_fst_340_) == 0 {
return v___x_337_;
} else {
let mut v_val_341_: *mut lean_object = core::ptr::null_mut(); 
v_val_341_ = lean_ctor_get(v_fst_340_, 0);
lean_inc(v_val_341_);
lean_dec_ref_known(v_fst_340_, 1);
return v_val_341_;
}
}
#[no_mangle] pub unsafe extern "C" fn l_Array_matchPrefix___boxed(mut v_a_342_: *mut lean_object, mut v_s_343_: *mut lean_object) -> *mut lean_object{
let mut v_res_344_: *mut lean_object = core::ptr::null_mut(); 
v_res_344_ = l_Array_matchPrefix(v_a_342_, v_s_343_);
lean_dec_ref(v_a_342_);
return v_res_344_;
}
#[no_mangle] pub unsafe extern "C" fn l_List_forIn_x27_loop___at___00Array_matchPrefix_spec__1(mut v_s_345_: *mut lean_object, mut v_a_346_: *mut lean_object, mut v_as_347_: *mut lean_object, mut v_as_x27_348_: *mut lean_object, mut v_b_349_: *mut lean_object, mut v_a_350_: *mut lean_object) -> *mut lean_object{
let mut v___x_351_: *mut lean_object = core::ptr::null_mut(); 
v___x_351_ = l_List_forIn_x27_loop___at___00Array_matchPrefix_spec__1___redArg(v_s_345_, v_a_346_, v_as_x27_348_, v_b_349_);
return v___x_351_;
}
#[no_mangle] pub unsafe extern "C" fn l_List_forIn_x27_loop___at___00Array_matchPrefix_spec__1___boxed(mut v_s_352_: *mut lean_object, mut v_a_353_: *mut lean_object, mut v_as_354_: *mut lean_object, mut v_as_x27_355_: *mut lean_object, mut v_b_356_: *mut lean_object, mut v_a_357_: *mut lean_object) -> *mut lean_object{
let mut v_res_358_: *mut lean_object = core::ptr::null_mut(); 
v_res_358_ = l_List_forIn_x27_loop___at___00Array_matchPrefix_spec__1(v_s_352_, v_a_353_, v_as_354_, v_as_x27_355_, v_b_356_, v_a_357_);
lean_dec_ref(v_b_356_);
lean_dec(v_as_x27_355_);
lean_dec(v_as_354_);
lean_dec_ref(v_a_353_);
return v_res_358_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00T_check_spec__0_spec__0(mut v_s_359_: *mut lean_object) -> *mut lean_object{
let mut v___x_361_: *mut lean_object = core::ptr::null_mut(); let mut v_putStr_362_: *mut lean_object = core::ptr::null_mut(); let mut v___x_363_: *mut lean_object = core::ptr::null_mut(); 
v___x_361_ = lean_get_stdout();
v_putStr_362_ = lean_ctor_get(v___x_361_, 4);
lean_inc_ref(v_putStr_362_);
lean_dec_ref(v___x_361_);
v___x_363_ = lean_apply_2(v_putStr_362_, v_s_359_, lean_box(0));
return v___x_363_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00T_check_spec__0_spec__0___boxed(mut v_s_364_: *mut lean_object, mut v_a_365_: *mut lean_object) -> *mut lean_object{
let mut v_res_366_: *mut lean_object = core::ptr::null_mut(); 
v_res_366_ = l_IO_print___at___00IO_println___at___00T_check_spec__0_spec__0(v_s_364_);
return v_res_366_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00T_check_spec__0(mut v_s_367_: *mut lean_object) -> *mut lean_object{
let mut v___x_369_: u32 = 0; let mut v___x_370_: *mut lean_object = core::ptr::null_mut(); let mut v___x_371_: *mut lean_object = core::ptr::null_mut(); 
v___x_369_ = 10;
v___x_370_ = lean_string_push(v_s_367_, v___x_369_);
v___x_371_ = l_IO_print___at___00IO_println___at___00T_check_spec__0_spec__0(v___x_370_);
return v___x_371_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00T_check_spec__0___boxed(mut v_s_372_: *mut lean_object, mut v_a_373_: *mut lean_object) -> *mut lean_object{
let mut v_res_374_: *mut lean_object = core::ptr::null_mut(); 
v_res_374_ = l_IO_println___at___00T_check_spec__0(v_s_372_);
return v_res_374_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00T_check_spec__2___closed__1() -> *mut lean_object{
let mut v___x_376_: *mut lean_object = core::ptr::null_mut(); let mut v___x_377_: *mut lean_object = core::ptr::null_mut(); 
v___x_376_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00T_check_spec__2___closed__0;
v___x_377_ = lean_string_utf8_byte_size(v___x_376_);
return v___x_377_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00T_check_spec__2(mut v_fst_386_: *mut lean_object, mut v_snd_387_: *mut lean_object, mut v_as_388_: *mut lean_object, mut v_i_389_: usize, mut v_stop_390_: usize, mut v_b_391_: *mut lean_object) -> *mut lean_object{
let mut v_a_394_: *mut lean_object = core::ptr::null_mut(); let mut v___x_395_: usize = 0; let mut v___x_396_: usize = 0; let mut v___y_399_: *mut lean_object = core::ptr::null_mut(); let mut v_a_400_: *mut lean_object = core::ptr::null_mut(); let mut v___x_401_: u8 = 0; let mut v___x_402_: *mut lean_object = core::ptr::null_mut(); let mut v___x_404_: *mut lean_object = core::ptr::null_mut(); let mut v___x_405_: *mut lean_object = core::ptr::null_mut(); let mut v___x_406_: *mut lean_object = core::ptr::null_mut(); let mut v___x_407_: *mut lean_object = core::ptr::null_mut(); let mut v___x_408_: *mut lean_object = core::ptr::null_mut(); let mut v___x_409_: *mut lean_object = core::ptr::null_mut(); let mut v___x_410_: *mut lean_object = core::ptr::null_mut(); let mut v___x_411_: u8 = 0; let mut v___x_412_: *mut lean_object = core::ptr::null_mut(); let mut v___x_413_: *mut lean_object = core::ptr::null_mut(); let mut v___x_414_: *mut lean_object = core::ptr::null_mut(); let mut v___x_415_: *mut lean_object = core::ptr::null_mut(); let mut v___y_417_: *mut lean_object = core::ptr::null_mut(); let mut v___y_418_: *mut lean_object = core::ptr::null_mut(); let mut v___x_419_: *mut lean_object = core::ptr::null_mut(); let mut v___x_420_: *mut lean_object = core::ptr::null_mut(); let mut v___x_421_: *mut lean_object = core::ptr::null_mut(); let mut v___x_422_: *mut lean_object = core::ptr::null_mut(); let mut v___x_423_: *mut lean_object = core::ptr::null_mut(); let mut v___x_424_: *mut lean_object = core::ptr::null_mut(); let mut v___x_425_: *mut lean_object = core::ptr::null_mut(); let mut v___x_426_: *mut lean_object = core::ptr::null_mut(); let mut v___x_427_: *mut lean_object = core::ptr::null_mut(); let mut v___x_428_: u8 = 0; let mut v___x_429_: *mut lean_object = core::ptr::null_mut(); let mut v___x_430_: *mut lean_object = core::ptr::null_mut(); let mut v___x_431_: *mut lean_object = core::ptr::null_mut(); let mut v___x_432_: *mut lean_object = core::ptr::null_mut(); let mut v___y_434_: *mut lean_object = core::ptr::null_mut(); let mut v___x_435_: *mut lean_object = core::ptr::null_mut(); let mut v___x_436_: *mut lean_object = core::ptr::null_mut(); let mut v___x_437_: *mut lean_object = core::ptr::null_mut(); let mut v___x_438_: *mut lean_object = core::ptr::null_mut(); let mut v_val_439_: *mut lean_object = core::ptr::null_mut(); let mut v___x_440_: *mut lean_object = core::ptr::null_mut(); let mut v___x_441_: *mut lean_object = core::ptr::null_mut(); let mut v___x_442_: *mut lean_object = core::ptr::null_mut(); let mut v___x_443_: *mut lean_object = core::ptr::null_mut(); let mut v___x_444_: *mut lean_object = core::ptr::null_mut(); let mut v___x_445_: *mut lean_object = core::ptr::null_mut(); let mut v_val_446_: *mut lean_object = core::ptr::null_mut(); let mut v___x_447_: *mut lean_object = core::ptr::null_mut(); let mut v___x_448_: *mut lean_object = core::ptr::null_mut(); let mut v___x_449_: *mut lean_object = core::ptr::null_mut(); let mut v___x_450_: *mut lean_object = core::ptr::null_mut(); let mut v___x_451_: *mut lean_object = core::ptr::null_mut(); let mut v___x_452_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_401_ = lean_usize_dec_eq(v_i_389_, v_stop_390_);
if v___x_401_ == 0 {
let mut v___x_402_: *mut lean_object = core::ptr::null_mut(); let mut v___y_417_: *mut lean_object = core::ptr::null_mut(); let mut v___y_418_: *mut lean_object = core::ptr::null_mut(); let mut v___x_423_: *mut lean_object = core::ptr::null_mut(); let mut v___x_424_: *mut lean_object = core::ptr::null_mut(); let mut v___x_425_: *mut lean_object = core::ptr::null_mut(); let mut v___x_426_: *mut lean_object = core::ptr::null_mut(); let mut v___x_427_: *mut lean_object = core::ptr::null_mut(); let mut v___x_428_: u8 = 0; 
v___x_402_ = lean_array_uget_borrowed(v_as_388_, v_i_389_);
v___x_423_ = lean_alloc_closure(l_instDecidableEqString___boxed as *mut core::ffi::c_void, 2, 0);
v___x_424_ = lean_unsigned_to_nat(0);
v___x_425_ = lean_string_utf8_byte_size(v___x_402_);
v___x_426_ = l_Lean_Data_Trie_matchPrefix___redArg(v___x_402_, v_fst_386_, v___x_424_, v___x_425_);
lean_inc(v___x_402_);
v___x_427_ = l_Array_matchPrefix(v_snd_387_, v___x_402_);
lean_inc(v___x_427_);
lean_inc(v___x_426_);
v___x_428_ = l_Option_instDecidableEq___redArg(v___x_423_, v___x_426_, v___x_427_);
if v___x_428_ == 0 {
let mut v___x_429_: *mut lean_object = core::ptr::null_mut(); let mut v___x_430_: *mut lean_object = core::ptr::null_mut(); let mut v___x_431_: *mut lean_object = core::ptr::null_mut(); let mut v___x_432_: *mut lean_object = core::ptr::null_mut(); let mut v___y_434_: *mut lean_object = core::ptr::null_mut(); 
v___x_429_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00T_check_spec__2___closed__4;
v___x_430_ = lean_string_append(v___x_429_, v___x_402_);
v___x_431_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00T_check_spec__2___closed__5;
v___x_432_ = lean_string_append(v___x_430_, v___x_431_);
if lean_obj_tag(v___x_426_) == 0 {
let mut v___x_445_: *mut lean_object = core::ptr::null_mut(); 
v___x_445_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00T_check_spec__2___closed__7;
v___y_434_ = v___x_445_;
state = 5; continue;
} else {
let mut v_val_446_: *mut lean_object = core::ptr::null_mut(); let mut v___x_447_: *mut lean_object = core::ptr::null_mut(); let mut v___x_448_: *mut lean_object = core::ptr::null_mut(); let mut v___x_449_: *mut lean_object = core::ptr::null_mut(); let mut v___x_450_: *mut lean_object = core::ptr::null_mut(); let mut v___x_451_: *mut lean_object = core::ptr::null_mut(); 
v_val_446_ = lean_ctor_get(v___x_426_, 0);
lean_inc(v_val_446_);
lean_dec_ref_known(v___x_426_, 1);
v___x_447_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00T_check_spec__2___closed__8;
v___x_448_ = l_addParenHeuristic(v_val_446_);
v___x_449_ = lean_string_append(v___x_447_, v___x_448_);
lean_dec_ref(v___x_448_);
v___x_450_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00T_check_spec__2___closed__9;
v___x_451_ = lean_string_append(v___x_449_, v___x_450_);
v___y_434_ = v___x_451_;
state = 5; continue;
}
} else {
lean_dec(v___x_427_);
lean_dec(v___x_426_);
state = 3; continue;
}
} else {
let mut v___x_452_: *mut lean_object = core::ptr::null_mut(); 
v___x_452_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_452_, 0, v_b_391_);
return v___x_452_;
}
}
1 => {
v___x_395_ = 1usize;
v___x_396_ = lean_usize_add(v_i_389_, v___x_395_);
v_i_389_ = v___x_396_;
v_b_391_ = v_a_394_;
state = 0; continue;
}
2 => {
if lean_obj_tag(v___y_399_) == 0 {
let mut v_a_400_: *mut lean_object = core::ptr::null_mut(); 
v_a_400_ = lean_ctor_get(v___y_399_, 0);
lean_inc(v_a_400_);
lean_dec_ref_known(v___y_399_, 1);
v_a_394_ = v_a_400_;
state = 1; continue;
} else {
return v___y_399_;
}
}
3 => {
v___x_404_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00T_check_spec__2___closed__0;
v___x_405_ = lean_string_append(v___x_404_, v___x_402_);
v___x_406_ = lean_alloc_closure(l_instDecidableEqString___boxed as *mut core::ffi::c_void, 2, 0);
v___x_407_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00T_check_spec__2___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00T_check_spec__2___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00T_check_spec__2___closed__1);
v___x_408_ = lean_string_utf8_byte_size(v___x_405_);
v___x_409_ = l_Lean_Data_Trie_matchPrefix___redArg(v___x_405_, v_fst_386_, v___x_407_, v___x_408_);
lean_dec_ref(v___x_405_);
lean_inc(v___x_402_);
v___x_410_ = l_Array_matchPrefix(v_snd_387_, v___x_402_);
v___x_411_ = l_Option_instDecidableEq___redArg(v___x_406_, v___x_409_, v___x_410_);
if v___x_411_ == 0 {
let mut v___x_412_: *mut lean_object = core::ptr::null_mut(); let mut v___x_413_: *mut lean_object = core::ptr::null_mut(); let mut v___x_414_: *mut lean_object = core::ptr::null_mut(); 
v___x_412_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00T_check_spec__2___closed__2;
v___x_413_ = lean_string_append(v___x_412_, v___x_402_);
v___x_414_ = l_IO_println___at___00T_check_spec__0(v___x_413_);
v___y_399_ = v___x_414_;
state = 2; continue;
} else {
let mut v___x_415_: *mut lean_object = core::ptr::null_mut(); 
v___x_415_ = lean_box(0);
v_a_394_ = v___x_415_;
state = 1; continue;
}
}
4 => {
v___x_419_ = lean_string_append(v___y_417_, v___y_418_);
lean_dec_ref(v___y_418_);
v___x_420_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00T_check_spec__2___closed__3;
v___x_421_ = lean_string_append(v___x_419_, v___x_420_);
v___x_422_ = l_IO_println___at___00T_check_spec__0(v___x_421_);
if lean_obj_tag(v___x_422_) == 0 {
lean_dec_ref_known(v___x_422_, 1);
state = 3; continue;
} else {
v___y_399_ = v___x_422_;
state = 2; continue;
}
}
5 => {
v___x_435_ = lean_string_append(v___x_432_, v___y_434_);
lean_dec_ref(v___y_434_);
v___x_436_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00T_check_spec__2___closed__6;
v___x_437_ = lean_string_append(v___x_435_, v___x_436_);
if lean_obj_tag(v___x_427_) == 0 {
let mut v___x_438_: *mut lean_object = core::ptr::null_mut(); 
v___x_438_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00T_check_spec__2___closed__7;
v___y_417_ = v___x_437_;
v___y_418_ = v___x_438_;
state = 4; continue;
} else {
let mut v_val_439_: *mut lean_object = core::ptr::null_mut(); let mut v___x_440_: *mut lean_object = core::ptr::null_mut(); let mut v___x_441_: *mut lean_object = core::ptr::null_mut(); let mut v___x_442_: *mut lean_object = core::ptr::null_mut(); let mut v___x_443_: *mut lean_object = core::ptr::null_mut(); let mut v___x_444_: *mut lean_object = core::ptr::null_mut(); 
v_val_439_ = lean_ctor_get(v___x_427_, 0);
lean_inc(v_val_439_);
lean_dec_ref_known(v___x_427_, 1);
v___x_440_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00T_check_spec__2___closed__8;
v___x_441_ = l_addParenHeuristic(v_val_439_);
v___x_442_ = lean_string_append(v___x_440_, v___x_441_);
lean_dec_ref(v___x_441_);
v___x_443_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00T_check_spec__2___closed__9;
v___x_444_ = lean_string_append(v___x_442_, v___x_443_);
v___y_417_ = v___x_437_;
v___y_418_ = v___x_444_;
state = 4; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00T_check_spec__2___boxed(mut v_fst_453_: *mut lean_object, mut v_snd_454_: *mut lean_object, mut v_as_455_: *mut lean_object, mut v_i_456_: *mut lean_object, mut v_stop_457_: *mut lean_object, mut v_b_458_: *mut lean_object, mut v___y_459_: *mut lean_object) -> *mut lean_object{
let mut v_i_boxed_460_: usize = 0; let mut v_stop_boxed_461_: usize = 0; let mut v_res_462_: *mut lean_object = core::ptr::null_mut(); 
v_i_boxed_460_ = lean_unbox_usize(v_i_456_);
lean_dec(v_i_456_);
v_stop_boxed_461_ = lean_unbox_usize(v_stop_457_);
lean_dec(v_stop_457_);
v_res_462_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00T_check_spec__2(v_fst_453_, v_snd_454_, v_as_455_, v_i_boxed_460_, v_stop_boxed_461_, v_b_458_);
lean_dec_ref(v_as_455_);
lean_dec_ref(v_snd_454_);
lean_dec_ref(v_fst_453_);
return v_res_462_;
}
#[no_mangle] pub unsafe extern "C" fn l_Array_isEqvAux___at___00Array_instDecidableEqImpl___at___00T_check_spec__1_spec__2___redArg(mut v_xs_463_: *mut lean_object, mut v_ys_464_: *mut lean_object, mut v_x_465_: *mut lean_object) -> u8{
let mut v_zero_466_: *mut lean_object = core::ptr::null_mut(); let mut v_isZero_467_: u8 = 0; let mut v_one_468_: *mut lean_object = core::ptr::null_mut(); let mut v_n_469_: *mut lean_object = core::ptr::null_mut(); let mut v___x_470_: *mut lean_object = core::ptr::null_mut(); let mut v___x_471_: *mut lean_object = core::ptr::null_mut(); let mut v___x_472_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v_zero_466_ = lean_unsigned_to_nat(0);
v_isZero_467_ = lean_nat_dec_eq(v_x_465_, v_zero_466_);
if v_isZero_467_ == 1 {
lean_dec(v_x_465_);
return v_isZero_467_;
} else {
let mut v_one_468_: *mut lean_object = core::ptr::null_mut(); let mut v_n_469_: *mut lean_object = core::ptr::null_mut(); let mut v___x_470_: *mut lean_object = core::ptr::null_mut(); let mut v___x_471_: *mut lean_object = core::ptr::null_mut(); let mut v___x_472_: u8 = 0; 
v_one_468_ = lean_unsigned_to_nat(1);
v_n_469_ = lean_nat_sub(v_x_465_, v_one_468_);
lean_dec(v_x_465_);
v___x_470_ = lean_array_fget_borrowed(v_xs_463_, v_n_469_);
v___x_471_ = lean_array_fget_borrowed(v_ys_464_, v_n_469_);
v___x_472_ = lean_string_dec_eq(v___x_470_, v___x_471_);
if v___x_472_ == 0 {
lean_dec(v_n_469_);
return v___x_472_;
} else {
v_x_465_ = v_n_469_;
state = 0; continue;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Array_isEqvAux___at___00Array_instDecidableEqImpl___at___00T_check_spec__1_spec__2___redArg___boxed(mut v_xs_474_: *mut lean_object, mut v_ys_475_: *mut lean_object, mut v_x_476_: *mut lean_object) -> *mut lean_object{
let mut v_res_477_: u8 = 0; let mut v_r_478_: *mut lean_object = core::ptr::null_mut(); 
v_res_477_ = l_Array_isEqvAux___at___00Array_instDecidableEqImpl___at___00T_check_spec__1_spec__2___redArg(v_xs_474_, v_ys_475_, v_x_476_);
lean_dec_ref(v_ys_475_);
lean_dec_ref(v_xs_474_);
v_r_478_ = lean_box((v_res_477_) as usize);
return v_r_478_;
}
#[no_mangle] pub unsafe extern "C" fn l_Array_instDecidableEqImpl___at___00T_check_spec__1(mut v_xs_479_: *mut lean_object, mut v_ys_480_: *mut lean_object) -> u8{
let mut v___x_481_: *mut lean_object = core::ptr::null_mut(); let mut v___x_482_: *mut lean_object = core::ptr::null_mut(); let mut v___x_483_: u8 = 0; 
v___x_481_ = lean_array_get_size(v_xs_479_);
v___x_482_ = lean_array_get_size(v_ys_480_);
v___x_483_ = lean_nat_dec_eq(v___x_481_, v___x_482_);
if v___x_483_ == 0 {
return v___x_483_;
} else {
let mut v___x_484_: u8 = 0; 
v___x_484_ = l_Array_isEqvAux___at___00Array_instDecidableEqImpl___at___00T_check_spec__1_spec__2___redArg(v_xs_479_, v_ys_480_, v___x_481_);
return v___x_484_;
}
}
#[no_mangle] pub unsafe extern "C" fn l_Array_instDecidableEqImpl___at___00T_check_spec__1___boxed(mut v_xs_485_: *mut lean_object, mut v_ys_486_: *mut lean_object) -> *mut lean_object{
let mut v_res_487_: u8 = 0; let mut v_r_488_: *mut lean_object = core::ptr::null_mut(); 
v_res_487_ = l_Array_instDecidableEqImpl___at___00T_check_spec__1(v_xs_485_, v_ys_486_);
lean_dec_ref(v_ys_486_);
lean_dec_ref(v_xs_485_);
v_r_488_ = lean_box((v_res_487_) as usize);
return v_r_488_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00T_check_spec__3(mut v_fst_490_: *mut lean_object, mut v_snd_491_: *mut lean_object, mut v_as_492_: *mut lean_object, mut v_i_493_: usize, mut v_stop_494_: usize, mut v_b_495_: *mut lean_object) -> *mut lean_object{
let mut v_a_498_: *mut lean_object = core::ptr::null_mut(); let mut v___x_499_: usize = 0; let mut v___x_500_: usize = 0; let mut v___x_502_: u8 = 0; let mut v___x_503_: *mut lean_object = core::ptr::null_mut(); let mut v___x_504_: *mut lean_object = core::ptr::null_mut(); let mut v___x_505_: *mut lean_object = core::ptr::null_mut(); let mut v___x_506_: *mut lean_object = core::ptr::null_mut(); let mut v___x_507_: *mut lean_object = core::ptr::null_mut(); let mut v___x_508_: u8 = 0; let mut v___x_509_: *mut lean_object = core::ptr::null_mut(); let mut v___x_510_: *mut lean_object = core::ptr::null_mut(); let mut v___x_511_: *mut lean_object = core::ptr::null_mut(); let mut v_a_512_: *mut lean_object = core::ptr::null_mut(); let mut v___x_513_: *mut lean_object = core::ptr::null_mut(); let mut v___x_514_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_502_ = lean_usize_dec_eq(v_i_493_, v_stop_494_);
if v___x_502_ == 0 {
let mut v___x_503_: *mut lean_object = core::ptr::null_mut(); let mut v___x_504_: *mut lean_object = core::ptr::null_mut(); let mut v___x_505_: *mut lean_object = core::ptr::null_mut(); let mut v___x_506_: *mut lean_object = core::ptr::null_mut(); let mut v___x_507_: *mut lean_object = core::ptr::null_mut(); let mut v___x_508_: u8 = 0; 
v___x_503_ = lean_array_uget_borrowed(v_as_492_, v_i_493_);
v___x_504_ = l_Lean_Data_Trie_findPrefix___redArg(v_fst_490_, v___x_503_);
v___x_505_ = l_Array_sorted(v___x_504_);
v___x_506_ = l_Array_findPrefix(v_snd_491_, v___x_503_);
v___x_507_ = l_Array_sorted(v___x_506_);
v___x_508_ = l_Array_instDecidableEqImpl___at___00T_check_spec__1(v___x_505_, v___x_507_);
lean_dec_ref(v___x_507_);
lean_dec_ref(v___x_505_);
if v___x_508_ == 0 {
let mut v___x_509_: *mut lean_object = core::ptr::null_mut(); let mut v___x_510_: *mut lean_object = core::ptr::null_mut(); let mut v___x_511_: *mut lean_object = core::ptr::null_mut(); 
v___x_509_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00T_check_spec__3___closed__0;
v___x_510_ = lean_string_append(v___x_509_, v___x_503_);
v___x_511_ = l_IO_println___at___00T_check_spec__0(v___x_510_);
if lean_obj_tag(v___x_511_) == 0 {
let mut v_a_512_: *mut lean_object = core::ptr::null_mut(); 
v_a_512_ = lean_ctor_get(v___x_511_, 0);
lean_inc(v_a_512_);
lean_dec_ref_known(v___x_511_, 1);
v_a_498_ = v_a_512_;
state = 1; continue;
} else {
return v___x_511_;
}
} else {
let mut v___x_513_: *mut lean_object = core::ptr::null_mut(); 
v___x_513_ = lean_box(0);
v_a_498_ = v___x_513_;
state = 1; continue;
}
} else {
let mut v___x_514_: *mut lean_object = core::ptr::null_mut(); 
v___x_514_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_514_, 0, v_b_495_);
return v___x_514_;
}
}
1 => {
v___x_499_ = 1usize;
v___x_500_ = lean_usize_add(v_i_493_, v___x_499_);
v_i_493_ = v___x_500_;
v_b_495_ = v_a_498_;
state = 0; continue;
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00T_check_spec__3___boxed(mut v_fst_515_: *mut lean_object, mut v_snd_516_: *mut lean_object, mut v_as_517_: *mut lean_object, mut v_i_518_: *mut lean_object, mut v_stop_519_: *mut lean_object, mut v_b_520_: *mut lean_object, mut v___y_521_: *mut lean_object) -> *mut lean_object{
let mut v_i_boxed_522_: usize = 0; let mut v_stop_boxed_523_: usize = 0; let mut v_res_524_: *mut lean_object = core::ptr::null_mut(); 
v_i_boxed_522_ = lean_unbox_usize(v_i_518_);
lean_dec(v_i_518_);
v_stop_boxed_523_ = lean_unbox_usize(v_stop_519_);
lean_dec(v_stop_519_);
v_res_524_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00T_check_spec__3(v_fst_515_, v_snd_516_, v_as_517_, v_i_boxed_522_, v_stop_boxed_523_, v_b_520_);
lean_dec_ref(v_as_517_);
lean_dec_ref(v_snd_516_);
lean_dec_ref(v_fst_515_);
return v_res_524_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00T_check_spec__4(mut v_fst_526_: *mut lean_object, mut v_snd_527_: *mut lean_object, mut v_as_528_: *mut lean_object, mut v_i_529_: usize, mut v_stop_530_: usize, mut v_b_531_: *mut lean_object) -> *mut lean_object{
let mut v_a_534_: *mut lean_object = core::ptr::null_mut(); let mut v___x_535_: usize = 0; let mut v___x_536_: usize = 0; let mut v___x_538_: u8 = 0; let mut v___x_539_: *mut lean_object = core::ptr::null_mut(); let mut v___x_540_: *mut lean_object = core::ptr::null_mut(); let mut v___x_541_: *mut lean_object = core::ptr::null_mut(); let mut v___x_542_: *mut lean_object = core::ptr::null_mut(); let mut v_sz_543_: usize = 0; let mut v___x_544_: usize = 0; let mut v___x_545_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_546_: *mut lean_object = core::ptr::null_mut(); let mut v___x_547_: *mut lean_object = core::ptr::null_mut(); let mut v___x_548_: *mut lean_object = core::ptr::null_mut(); let mut v___y_550_: *mut lean_object = core::ptr::null_mut(); let mut v___x_551_: u8 = 0; let mut v___x_552_: *mut lean_object = core::ptr::null_mut(); let mut v___x_553_: *mut lean_object = core::ptr::null_mut(); let mut v___x_554_: *mut lean_object = core::ptr::null_mut(); let mut v_a_555_: *mut lean_object = core::ptr::null_mut(); let mut v_val_556_: *mut lean_object = core::ptr::null_mut(); let mut v___x_557_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_538_ = lean_usize_dec_eq(v_i_529_, v_stop_530_);
if v___x_538_ == 0 {
let mut v___x_539_: *mut lean_object = core::ptr::null_mut(); let mut v___x_540_: *mut lean_object = core::ptr::null_mut(); let mut v___x_541_: *mut lean_object = core::ptr::null_mut(); let mut v___x_542_: *mut lean_object = core::ptr::null_mut(); let mut v_sz_543_: usize = 0; let mut v___x_544_: usize = 0; let mut v___x_545_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_546_: *mut lean_object = core::ptr::null_mut(); let mut v___x_547_: *mut lean_object = core::ptr::null_mut(); let mut v___x_548_: *mut lean_object = core::ptr::null_mut(); let mut v___y_550_: *mut lean_object = core::ptr::null_mut(); 
v___x_539_ = lean_array_uget_borrowed(v_as_528_, v_i_529_);
v___x_540_ = lean_box(0);
v___x_541_ = lean_box(0);
v___x_542_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_matchPrefix_spec__0___closed__0;
v_sz_543_ = lean_array_size(v_snd_527_);
v___x_544_ = 0usize;
v___x_545_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_matchPrefix_spec__0(v___x_539_, v_snd_527_, v_sz_543_, v___x_544_, v___x_542_);
v_fst_546_ = lean_ctor_get(v___x_545_, 0);
lean_inc(v_fst_546_);
lean_dec_ref(v___x_545_);
v___x_547_ = lean_alloc_closure(l_instDecidableEqString___boxed as *mut core::ffi::c_void, 2, 0);
v___x_548_ = l_Lean_Data_Trie_find_x3f___redArg(v_fst_526_, v___x_539_);
if lean_obj_tag(v_fst_546_) == 0 {
v___y_550_ = v___x_540_;
state = 2; continue;
} else {
let mut v_val_556_: *mut lean_object = core::ptr::null_mut(); 
v_val_556_ = lean_ctor_get(v_fst_546_, 0);
lean_inc(v_val_556_);
lean_dec_ref_known(v_fst_546_, 1);
v___y_550_ = v_val_556_;
state = 2; continue;
}
} else {
let mut v___x_557_: *mut lean_object = core::ptr::null_mut(); 
v___x_557_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_557_, 0, v_b_531_);
return v___x_557_;
}
}
1 => {
v___x_535_ = 1usize;
v___x_536_ = lean_usize_add(v_i_529_, v___x_535_);
v_i_529_ = v___x_536_;
v_b_531_ = v_a_534_;
state = 0; continue;
}
2 => {
v___x_551_ = l_Option_instDecidableEq___redArg(v___x_547_, v___x_548_, v___y_550_);
if v___x_551_ == 0 {
let mut v___x_552_: *mut lean_object = core::ptr::null_mut(); let mut v___x_553_: *mut lean_object = core::ptr::null_mut(); let mut v___x_554_: *mut lean_object = core::ptr::null_mut(); 
v___x_552_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00T_check_spec__4___closed__0;
v___x_553_ = lean_string_append(v___x_552_, v___x_539_);
v___x_554_ = l_IO_println___at___00T_check_spec__0(v___x_553_);
if lean_obj_tag(v___x_554_) == 0 {
let mut v_a_555_: *mut lean_object = core::ptr::null_mut(); 
v_a_555_ = lean_ctor_get(v___x_554_, 0);
lean_inc(v_a_555_);
lean_dec_ref_known(v___x_554_, 1);
v_a_534_ = v_a_555_;
state = 1; continue;
} else {
return v___x_554_;
}
} else {
v_a_534_ = v___x_541_;
state = 1; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00T_check_spec__4___boxed(mut v_fst_558_: *mut lean_object, mut v_snd_559_: *mut lean_object, mut v_as_560_: *mut lean_object, mut v_i_561_: *mut lean_object, mut v_stop_562_: *mut lean_object, mut v_b_563_: *mut lean_object, mut v___y_564_: *mut lean_object) -> *mut lean_object{
let mut v_i_boxed_565_: usize = 0; let mut v_stop_boxed_566_: usize = 0; let mut v_res_567_: *mut lean_object = core::ptr::null_mut(); 
v_i_boxed_565_ = lean_unbox_usize(v_i_561_);
lean_dec(v_i_561_);
v_stop_boxed_566_ = lean_unbox_usize(v_stop_562_);
lean_dec(v_stop_562_);
v_res_567_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00T_check_spec__4(v_fst_558_, v_snd_559_, v_as_560_, v_i_boxed_565_, v_stop_boxed_566_, v_b_563_);
lean_dec_ref(v_as_560_);
lean_dec_ref(v_snd_559_);
lean_dec_ref(v_fst_558_);
return v_res_567_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_T_check___closed__0() -> *mut lean_object{
let mut v___x_568_: *mut lean_object = core::ptr::null_mut(); let mut v___x_569_: *mut lean_object = core::ptr::null_mut(); 
v___x_568_ = l_keys;
v___x_569_ = lean_array_get_size(v___x_568_);
return v___x_569_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_T_check___closed__1() -> u8{
let mut v___x_570_: *mut lean_object = core::ptr::null_mut(); let mut v___x_571_: *mut lean_object = core::ptr::null_mut(); let mut v___x_572_: u8 = 0; 
v___x_570_ = lean_obj_once(core::ptr::addr_of_mut!(l_T_check___closed__0), core::ptr::addr_of_mut!(l_T_check___closed__0_once), _init_l_T_check___closed__0);
v___x_571_ = lean_unsigned_to_nat(0);
v___x_572_ = lean_nat_dec_lt(v___x_571_, v___x_570_);
return v___x_572_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_T_check___closed__2() -> u8{
let mut v___x_573_: *mut lean_object = core::ptr::null_mut(); let mut v___x_574_: u8 = 0; 
v___x_573_ = lean_obj_once(core::ptr::addr_of_mut!(l_T_check___closed__0), core::ptr::addr_of_mut!(l_T_check___closed__0_once), _init_l_T_check___closed__0);
v___x_574_ = lean_nat_dec_le(v___x_573_, v___x_573_);
return v___x_574_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_T_check___closed__3() -> usize{
let mut v___x_575_: *mut lean_object = core::ptr::null_mut(); let mut v___x_576_: usize = 0; 
v___x_575_ = lean_obj_once(core::ptr::addr_of_mut!(l_T_check___closed__0), core::ptr::addr_of_mut!(l_T_check___closed__0_once), _init_l_T_check___closed__0);
v___x_576_ = lean_usize_of_nat(v___x_575_);
return v___x_576_;
}
#[no_mangle] pub unsafe extern "C" fn l_T_check(mut v_x_577_: *mut lean_object) -> *mut lean_object{
let mut v_fst_579_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_580_: *mut lean_object = core::ptr::null_mut(); let mut v___x_581_: *mut lean_object = core::ptr::null_mut(); let mut v___x_583_: *mut lean_object = core::ptr::null_mut(); let mut v___x_584_: u8 = 0; let mut v___x_585_: *mut lean_object = core::ptr::null_mut(); let mut v___x_586_: u8 = 0; let mut v___x_587_: *mut lean_object = core::ptr::null_mut(); let mut v___x_588_: usize = 0; let mut v___x_589_: usize = 0; let mut v___x_590_: *mut lean_object = core::ptr::null_mut(); let mut v___x_591_: usize = 0; let mut v___x_592_: usize = 0; let mut v___x_593_: *mut lean_object = core::ptr::null_mut(); let mut v___y_595_: *mut lean_object = core::ptr::null_mut(); let mut v___x_597_: u8 = 0; let mut v___x_598_: *mut lean_object = core::ptr::null_mut(); let mut v___x_599_: u8 = 0; let mut v___x_600_: usize = 0; let mut v___x_601_: usize = 0; let mut v___x_602_: *mut lean_object = core::ptr::null_mut(); let mut v___x_603_: usize = 0; let mut v___x_604_: usize = 0; let mut v___x_605_: *mut lean_object = core::ptr::null_mut(); let mut v___y_607_: *mut lean_object = core::ptr::null_mut(); let mut v___x_608_: u8 = 0; let mut v___x_609_: *mut lean_object = core::ptr::null_mut(); let mut v___x_610_: u8 = 0; let mut v___x_611_: usize = 0; let mut v___x_612_: usize = 0; let mut v___x_613_: *mut lean_object = core::ptr::null_mut(); let mut v___x_614_: usize = 0; let mut v___x_615_: usize = 0; let mut v___x_616_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v_fst_579_ = lean_ctor_get(v_x_577_, 0);
v_snd_580_ = lean_ctor_get(v_x_577_, 1);
v___x_581_ = l_keys;
v___x_608_ = lean_uint8_once(core::ptr::addr_of_mut!(l_T_check___closed__1), core::ptr::addr_of_mut!(l_T_check___closed__1_once), _init_l_T_check___closed__1);
if v___x_608_ == 0 {
state = 3; continue;
} else {
let mut v___x_609_: *mut lean_object = core::ptr::null_mut(); let mut v___x_610_: u8 = 0; 
v___x_609_ = lean_box(0);
v___x_610_ = lean_uint8_once(core::ptr::addr_of_mut!(l_T_check___closed__2), core::ptr::addr_of_mut!(l_T_check___closed__2_once), _init_l_T_check___closed__2);
if v___x_610_ == 0 {
if v___x_608_ == 0 {
state = 3; continue;
} else {
let mut v___x_611_: usize = 0; let mut v___x_612_: usize = 0; let mut v___x_613_: *mut lean_object = core::ptr::null_mut(); 
v___x_611_ = 0usize;
v___x_612_ = lean_usize_once(core::ptr::addr_of_mut!(l_T_check___closed__3), core::ptr::addr_of_mut!(l_T_check___closed__3_once), _init_l_T_check___closed__3);
v___x_613_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00T_check_spec__4(v_fst_579_, v_snd_580_, v___x_581_, v___x_611_, v___x_612_, v___x_609_);
v___y_607_ = v___x_613_;
state = 4; continue;
}
} else {
let mut v___x_614_: usize = 0; let mut v___x_615_: usize = 0; let mut v___x_616_: *mut lean_object = core::ptr::null_mut(); 
v___x_614_ = 0usize;
v___x_615_ = lean_usize_once(core::ptr::addr_of_mut!(l_T_check___closed__3), core::ptr::addr_of_mut!(l_T_check___closed__3_once), _init_l_T_check___closed__3);
v___x_616_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00T_check_spec__4(v_fst_579_, v_snd_580_, v___x_581_, v___x_614_, v___x_615_, v___x_609_);
v___y_607_ = v___x_616_;
state = 4; continue;
}
}
}
1 => {
v___x_583_ = lean_box(0);
v___x_584_ = lean_uint8_once(core::ptr::addr_of_mut!(l_T_check___closed__1), core::ptr::addr_of_mut!(l_T_check___closed__1_once), _init_l_T_check___closed__1);
if v___x_584_ == 0 {
let mut v___x_585_: *mut lean_object = core::ptr::null_mut(); 
v___x_585_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_585_, 0, v___x_583_);
return v___x_585_;
} else {
let mut v___x_586_: u8 = 0; 
v___x_586_ = lean_uint8_once(core::ptr::addr_of_mut!(l_T_check___closed__2), core::ptr::addr_of_mut!(l_T_check___closed__2_once), _init_l_T_check___closed__2);
if v___x_586_ == 0 {
if v___x_584_ == 0 {
let mut v___x_587_: *mut lean_object = core::ptr::null_mut(); 
v___x_587_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_587_, 0, v___x_583_);
return v___x_587_;
} else {
let mut v___x_588_: usize = 0; let mut v___x_589_: usize = 0; let mut v___x_590_: *mut lean_object = core::ptr::null_mut(); 
v___x_588_ = 0usize;
v___x_589_ = lean_usize_once(core::ptr::addr_of_mut!(l_T_check___closed__3), core::ptr::addr_of_mut!(l_T_check___closed__3_once), _init_l_T_check___closed__3);
v___x_590_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00T_check_spec__2(v_fst_579_, v_snd_580_, v___x_581_, v___x_588_, v___x_589_, v___x_583_);
return v___x_590_;
}
} else {
let mut v___x_591_: usize = 0; let mut v___x_592_: usize = 0; let mut v___x_593_: *mut lean_object = core::ptr::null_mut(); 
v___x_591_ = 0usize;
v___x_592_ = lean_usize_once(core::ptr::addr_of_mut!(l_T_check___closed__3), core::ptr::addr_of_mut!(l_T_check___closed__3_once), _init_l_T_check___closed__3);
v___x_593_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00T_check_spec__2(v_fst_579_, v_snd_580_, v___x_581_, v___x_591_, v___x_592_, v___x_583_);
return v___x_593_;
}
}
}
2 => {
if lean_obj_tag(v___y_595_) == 0 {
lean_dec_ref_known(v___y_595_, 1);
state = 1; continue;
} else {
return v___y_595_;
}
}
3 => {
v___x_597_ = lean_uint8_once(core::ptr::addr_of_mut!(l_T_check___closed__1), core::ptr::addr_of_mut!(l_T_check___closed__1_once), _init_l_T_check___closed__1);
if v___x_597_ == 0 {
state = 1; continue;
} else {
let mut v___x_598_: *mut lean_object = core::ptr::null_mut(); let mut v___x_599_: u8 = 0; 
v___x_598_ = lean_box(0);
v___x_599_ = lean_uint8_once(core::ptr::addr_of_mut!(l_T_check___closed__2), core::ptr::addr_of_mut!(l_T_check___closed__2_once), _init_l_T_check___closed__2);
if v___x_599_ == 0 {
if v___x_597_ == 0 {
state = 1; continue;
} else {
let mut v___x_600_: usize = 0; let mut v___x_601_: usize = 0; let mut v___x_602_: *mut lean_object = core::ptr::null_mut(); 
v___x_600_ = 0usize;
v___x_601_ = lean_usize_once(core::ptr::addr_of_mut!(l_T_check___closed__3), core::ptr::addr_of_mut!(l_T_check___closed__3_once), _init_l_T_check___closed__3);
v___x_602_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00T_check_spec__3(v_fst_579_, v_snd_580_, v___x_581_, v___x_600_, v___x_601_, v___x_598_);
v___y_595_ = v___x_602_;
state = 2; continue;
}
} else {
let mut v___x_603_: usize = 0; let mut v___x_604_: usize = 0; let mut v___x_605_: *mut lean_object = core::ptr::null_mut(); 
v___x_603_ = 0usize;
v___x_604_ = lean_usize_once(core::ptr::addr_of_mut!(l_T_check___closed__3), core::ptr::addr_of_mut!(l_T_check___closed__3_once), _init_l_T_check___closed__3);
v___x_605_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00T_check_spec__3(v_fst_579_, v_snd_580_, v___x_581_, v___x_603_, v___x_604_, v___x_598_);
v___y_595_ = v___x_605_;
state = 2; continue;
}
}
}
4 => {
if lean_obj_tag(v___y_607_) == 0 {
lean_dec_ref_known(v___y_607_, 1);
state = 3; continue;
} else {
return v___y_607_;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_T_check___boxed(mut v_x_617_: *mut lean_object, mut v_a_618_: *mut lean_object) -> *mut lean_object{
let mut v_res_619_: *mut lean_object = core::ptr::null_mut(); 
v_res_619_ = l_T_check(v_x_617_);
lean_dec_ref(v_x_617_);
return v_res_619_;
}
#[no_mangle] pub unsafe extern "C" fn l_Array_isEqvAux___at___00Array_instDecidableEqImpl___at___00T_check_spec__1_spec__2(mut v_xs_620_: *mut lean_object, mut v_ys_621_: *mut lean_object, mut v_hsz_622_: *mut lean_object, mut v_x_623_: *mut lean_object, mut v_x_624_: *mut lean_object) -> u8{
let mut v___x_625_: u8 = 0; 
v___x_625_ = l_Array_isEqvAux___at___00Array_instDecidableEqImpl___at___00T_check_spec__1_spec__2___redArg(v_xs_620_, v_ys_621_, v_x_623_);
return v___x_625_;
}
#[no_mangle] pub unsafe extern "C" fn l_Array_isEqvAux___at___00Array_instDecidableEqImpl___at___00T_check_spec__1_spec__2___boxed(mut v_xs_626_: *mut lean_object, mut v_ys_627_: *mut lean_object, mut v_hsz_628_: *mut lean_object, mut v_x_629_: *mut lean_object, mut v_x_630_: *mut lean_object) -> *mut lean_object{
let mut v_res_631_: u8 = 0; let mut v_r_632_: *mut lean_object = core::ptr::null_mut(); 
v_res_631_ = l_Array_isEqvAux___at___00Array_instDecidableEqImpl___at___00T_check_spec__1_spec__2(v_xs_626_, v_ys_627_, v_hsz_628_, v_x_629_, v_x_630_);
lean_dec_ref(v_ys_627_);
lean_dec_ref(v_xs_626_);
v_r_632_ = lean_box((v_res_631_) as usize);
return v_r_632_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__0(mut v_as_634_: *mut lean_object, mut v_sz_635_: usize, mut v_i_636_: usize, mut v_b_637_: *mut lean_object) -> *mut lean_object{
let mut v___x_639_: u8 = 0; let mut v___x_640_: *mut lean_object = core::ptr::null_mut(); let mut v_a_641_: *mut lean_object = core::ptr::null_mut(); let mut v___x_642_: *mut lean_object = core::ptr::null_mut(); let mut v___x_643_: *mut lean_object = core::ptr::null_mut(); let mut v___x_644_: *mut lean_object = core::ptr::null_mut(); let mut v___x_645_: *mut lean_object = core::ptr::null_mut(); let mut v___x_646_: *mut lean_object = core::ptr::null_mut(); let mut v___x_647_: usize = 0; let mut v___x_648_: usize = 0; let mut v_a_650_: *mut lean_object = core::ptr::null_mut(); let mut v___x_652_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_653_: u8 = 0; let mut v___x_655_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_656_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_657_: u8 = 0; let mut v_a_658_: *mut lean_object = core::ptr::null_mut(); let mut v___x_660_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_661_: u8 = 0; let mut v___x_663_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_664_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_665_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_639_ = lean_usize_dec_lt(v_i_636_, v_sz_635_);
if v___x_639_ == 0 {
let mut v___x_640_: *mut lean_object = core::ptr::null_mut(); 
v___x_640_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_640_, 0, v_b_637_);
return v___x_640_;
} else {
let mut v_a_641_: *mut lean_object = core::ptr::null_mut(); let mut v___x_642_: *mut lean_object = core::ptr::null_mut(); let mut v___x_643_: *mut lean_object = core::ptr::null_mut(); let mut v___x_644_: *mut lean_object = core::ptr::null_mut(); 
v_a_641_ = lean_array_uget_borrowed(v_as_634_, v_i_636_);
v___x_642_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__0___closed__0;
v___x_643_ = lean_string_append(v___x_642_, v_a_641_);
v___x_644_ = l_IO_println___at___00T_check_spec__0(v___x_643_);
if lean_obj_tag(v___x_644_) == 0 {
let mut v___x_645_: *mut lean_object = core::ptr::null_mut(); let mut v___x_646_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_644_, 1);
lean_inc(v_a_641_);
v___x_645_ = l_T_insert(v_b_637_, v_a_641_);
v___x_646_ = l_T_check(v___x_645_);
if lean_obj_tag(v___x_646_) == 0 {
let mut v___x_647_: usize = 0; let mut v___x_648_: usize = 0; 
lean_dec_ref_known(v___x_646_, 1);
v___x_647_ = 1usize;
v___x_648_ = lean_usize_add(v_i_636_, v___x_647_);
v_i_636_ = v___x_648_;
v_b_637_ = v___x_645_;
state = 0; continue;
} else {
let mut v_a_650_: *mut lean_object = core::ptr::null_mut(); let mut v___x_652_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_653_: u8 = 0; let mut v_isSharedCheck_657_: u8 = 0; 
lean_dec_ref(v___x_645_);
v_a_650_ = lean_ctor_get(v___x_646_, 0);
v_isSharedCheck_657_ = (!lean_is_exclusive(v___x_646_)) as u8;
if v_isSharedCheck_657_ == 0 {
v___x_652_ = v___x_646_;
v_isShared_653_ = v_isSharedCheck_657_;
state = 1; continue;
} else {
lean_inc(v_a_650_);
lean_dec(v___x_646_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_657_;
state = 1; continue;
}
}
} else {
let mut v_a_658_: *mut lean_object = core::ptr::null_mut(); let mut v___x_660_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_661_: u8 = 0; let mut v_isSharedCheck_665_: u8 = 0; 
lean_dec_ref(v_b_637_);
v_a_658_ = lean_ctor_get(v___x_644_, 0);
v_isSharedCheck_665_ = (!lean_is_exclusive(v___x_644_)) as u8;
if v_isSharedCheck_665_ == 0 {
v___x_660_ = v___x_644_;
v_isShared_661_ = v_isSharedCheck_665_;
state = 3; continue;
} else {
lean_inc(v_a_658_);
lean_dec(v___x_644_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_665_;
state = 3; continue;
}
}
}
}
1 => {
if v_isShared_653_ == 0 {
v___x_655_ = v___x_652_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_656_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_656_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v_a_650_);
v___x_655_ = v_reuseFailAlloc_656_;
state = 2; continue;
}
}
3 => {
if v_isShared_661_ == 0 {
v___x_663_ = v___x_660_;
state = 4; continue;
} else {
let mut v_reuseFailAlloc_664_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_664_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v_a_658_);
v___x_663_ = v_reuseFailAlloc_664_;
state = 4; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__0___boxed(mut v_as_666_: *mut lean_object, mut v_sz_667_: *mut lean_object, mut v_i_668_: *mut lean_object, mut v_b_669_: *mut lean_object, mut v___y_670_: *mut lean_object) -> *mut lean_object{
let mut v_sz_boxed_671_: usize = 0; let mut v_i_boxed_672_: usize = 0; let mut v_res_673_: *mut lean_object = core::ptr::null_mut(); 
v_sz_boxed_671_ = lean_unbox_usize(v_sz_667_);
lean_dec(v_sz_667_);
v_i_boxed_672_ = lean_unbox_usize(v_i_668_);
lean_dec(v_i_668_);
v_res_673_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__0(v_as_666_, v_sz_boxed_671_, v_i_boxed_672_, v_b_669_);
lean_dec_ref(v_as_666_);
return v_res_673_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1(mut v_as_675_: *mut lean_object, mut v_sz_676_: usize, mut v_i_677_: usize, mut v_b_678_: *mut lean_object) -> *mut lean_object{
let mut v___x_680_: u8 = 0; let mut v___x_681_: *mut lean_object = core::ptr::null_mut(); let mut v___x_682_: *mut lean_object = core::ptr::null_mut(); let mut v___x_683_: *mut lean_object = core::ptr::null_mut(); let mut v___x_684_: *mut lean_object = core::ptr::null_mut(); let mut v___x_685_: *mut lean_object = core::ptr::null_mut(); let mut v_a_686_: *mut lean_object = core::ptr::null_mut(); let mut v_sz_687_: usize = 0; let mut v___x_688_: usize = 0; let mut v___x_689_: *mut lean_object = core::ptr::null_mut(); let mut v___x_690_: *mut lean_object = core::ptr::null_mut(); let mut v___x_691_: usize = 0; let mut v___x_692_: usize = 0; let mut v_a_694_: *mut lean_object = core::ptr::null_mut(); let mut v___x_696_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_697_: u8 = 0; let mut v___x_699_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_700_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_701_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_680_ = lean_usize_dec_lt(v_i_677_, v_sz_676_);
if v___x_680_ == 0 {
let mut v___x_681_: *mut lean_object = core::ptr::null_mut(); 
v___x_681_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_681_, 0, v_b_678_);
return v___x_681_;
} else {
let mut v___x_682_: *mut lean_object = core::ptr::null_mut(); let mut v___x_683_: *mut lean_object = core::ptr::null_mut(); 
v___x_682_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__0;
v___x_683_ = l_IO_println___at___00T_check_spec__0(v___x_682_);
if lean_obj_tag(v___x_683_) == 0 {
let mut v___x_684_: *mut lean_object = core::ptr::null_mut(); let mut v___x_685_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_683_, 1);
v___x_684_ = l_T_empty;
v___x_685_ = l_T_check(v___x_684_);
if lean_obj_tag(v___x_685_) == 0 {
let mut v_a_686_: *mut lean_object = core::ptr::null_mut(); let mut v_sz_687_: usize = 0; let mut v___x_688_: usize = 0; let mut v___x_689_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_685_, 1);
v_a_686_ = lean_array_uget_borrowed(v_as_675_, v_i_677_);
v_sz_687_ = lean_array_size(v_a_686_);
v___x_688_ = 0usize;
v___x_689_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__0(v_a_686_, v_sz_687_, v___x_688_, v___x_684_);
if lean_obj_tag(v___x_689_) == 0 {
let mut v___x_690_: *mut lean_object = core::ptr::null_mut(); let mut v___x_691_: usize = 0; let mut v___x_692_: usize = 0; 
lean_dec_ref_known(v___x_689_, 1);
v___x_690_ = lean_box(0);
v___x_691_ = 1usize;
v___x_692_ = lean_usize_add(v_i_677_, v___x_691_);
v_i_677_ = v___x_692_;
v_b_678_ = v___x_690_;
state = 0; continue;
} else {
let mut v_a_694_: *mut lean_object = core::ptr::null_mut(); let mut v___x_696_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_697_: u8 = 0; let mut v_isSharedCheck_701_: u8 = 0; 
v_a_694_ = lean_ctor_get(v___x_689_, 0);
v_isSharedCheck_701_ = (!lean_is_exclusive(v___x_689_)) as u8;
if v_isSharedCheck_701_ == 0 {
v___x_696_ = v___x_689_;
v_isShared_697_ = v_isSharedCheck_701_;
state = 1; continue;
} else {
lean_inc(v_a_694_);
lean_dec(v___x_689_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_701_;
state = 1; continue;
}
}
} else {
return v___x_685_;
}
} else {
return v___x_683_;
}
}
}
1 => {
if v_isShared_697_ == 0 {
v___x_699_ = v___x_696_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_700_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_700_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_a_694_);
v___x_699_ = v_reuseFailAlloc_700_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___boxed(mut v_as_702_: *mut lean_object, mut v_sz_703_: *mut lean_object, mut v_i_704_: *mut lean_object, mut v_b_705_: *mut lean_object, mut v___y_706_: *mut lean_object) -> *mut lean_object{
let mut v_sz_boxed_707_: usize = 0; let mut v_i_boxed_708_: usize = 0; let mut v_res_709_: *mut lean_object = core::ptr::null_mut(); 
v_sz_boxed_707_ = lean_unbox_usize(v_sz_703_);
lean_dec(v_sz_703_);
v_i_boxed_708_ = lean_unbox_usize(v_i_704_);
lean_dec(v_i_704_);
v_res_709_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1(v_as_702_, v_sz_boxed_707_, v_i_boxed_708_, v_b_705_);
lean_dec_ref(v_as_702_);
return v_res_709_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__4() -> usize{
let mut v___x_742_: *mut lean_object = core::ptr::null_mut(); let mut v_sz_743_: usize = 0; 
v___x_742_ = l_main___closed__3;
v_sz_743_ = lean_array_size(v___x_742_);
return v_sz_743_;
}
#[no_mangle] pub unsafe extern "C" fn _lean_main() -> *mut lean_object{
let mut v___x_745_: *mut lean_object = core::ptr::null_mut(); let mut v___x_746_: *mut lean_object = core::ptr::null_mut(); let mut v_sz_747_: usize = 0; let mut v___x_748_: usize = 0; let mut v___x_749_: *mut lean_object = core::ptr::null_mut(); let mut v___x_751_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_752_: u8 = 0; let mut v___x_754_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_755_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_756_: u8 = 0; let mut v_unused_757_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_745_ = l_main___closed__3;
v___x_746_ = lean_box(0);
v_sz_747_ = lean_usize_once(core::ptr::addr_of_mut!(l_main___closed__4), core::ptr::addr_of_mut!(l_main___closed__4_once), _init_l_main___closed__4);
v___x_748_ = 0usize;
v___x_749_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1(v___x_745_, v_sz_747_, v___x_748_, v___x_746_);
if lean_obj_tag(v___x_749_) == 0 {
let mut v___x_751_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_752_: u8 = 0; let mut v_isSharedCheck_756_: u8 = 0; 
v_isSharedCheck_756_ = (!lean_is_exclusive(v___x_749_)) as u8;
if v_isSharedCheck_756_ == 0 {
let mut v_unused_757_: *mut lean_object = core::ptr::null_mut(); 
v_unused_757_ = lean_ctor_get(v___x_749_, 0);
lean_dec(v_unused_757_);
v___x_751_ = v___x_749_;
v_isShared_752_ = v_isSharedCheck_756_;
state = 1; continue;
} else {
lean_dec(v___x_749_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_756_;
state = 1; continue;
}
} else {
return v___x_749_;
}
}
1 => {
if v_isShared_752_ == 0 {
lean_ctor_set(v___x_751_, 0, v___x_746_);
v___x_754_ = v___x_751_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_755_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_755_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v___x_746_);
v___x_754_ = v_reuseFailAlloc_755_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_main___boxed(mut v_a_758_: *mut lean_object) -> *mut lean_object{
let mut v_res_759_: *mut lean_object = core::ptr::null_mut(); 
v_res_759_ = _lean_main();
return v_res_759_;
}
extern "C" { fn initialize_Init(builtin: u8) -> *mut lean_object; }
extern "C" { fn initialize_Lean_Data_Trie(builtin: u8) -> *mut lean_object; }
static mut _G_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn initialize_trie(builtin: u8) -> *mut lean_object {
let mut res: *mut lean_object = core::ptr::null_mut();
if _G_initialized { return lean_io_result_mk_ok(lean_box(0)); }
_G_initialized = true;
res = initialize_Init(builtin);
if lean_io_result_is_error(res) { return res; }
lean_dec_ref(res);
res = initialize_Lean_Data_Trie(builtin);
if lean_io_result_is_error(res) { return res; }
lean_dec_ref(res);
l_T_empty = _init_l_T_empty();
lean_mark_persistent(l_T_empty);
return lean_io_result_mk_ok(lean_box(0));
}
unsafe extern "C" fn run_main(argc: core::ffi::c_int, argv: *mut *mut core::ffi::c_char) -> *mut lean_object {
    return _lean_main();
}
#[no_mangle]
pub unsafe extern "C" fn main(argc: core::ffi::c_int, mut argv: *mut *mut core::ffi::c_char) -> core::ffi::c_int {
  argv = lean_setup_args(argc, argv);
  lean_initialize();
  let res = initialize_trie(1 /* builtin */);
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
