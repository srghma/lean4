// Lean compiler output
// Module: iterators
// Imports: public import Init public meta import Init public import Std.Data.Iterators
use lean_runtime::generated_abi::*;
extern "C" {
    fn lean_nat_dec_le(_: *mut lean_object, _: *mut lean_object) -> u8;
    fn lean_nat_add(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_nat_mod(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_nat_dec_eq(_: *mut lean_object, _: *mut lean_object) -> u8;
    fn l_Nat_reprFast(_: *mut lean_object) -> *mut lean_object;
    fn lean_string_append(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_string_push(_: *mut lean_object, _: u32) -> *mut lean_object;
    fn lean_get_stdout() -> *mut lean_object;
    fn lean_array_get_size(_: *mut lean_object) -> *mut lean_object;
    fn l_Array_toSubarray___redArg(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_nat_dec_lt(_: *mut lean_object, _: *mut lean_object) -> u8;
    fn lean_array_fget(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_nat_mul(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_mk_empty_array_with_capacity(_: *mut lean_object) -> *mut lean_object;
    fn lean_array_push(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_Lean_Name_mkStr4(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_nat_sub(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_array_to_list(_: *mut lean_object) -> *mut lean_object;
    fn l_Lean_Name_mkStr1(_: *mut lean_object) -> *mut lean_object;
    fn lean_array_size(_: *mut lean_object) -> usize;
    fn lean_usize_dec_lt(_: usize, _: usize) -> u8;
    fn lean_array_uget_borrowed(_: *mut lean_object, _: usize) -> *mut lean_object;
    fn lean_usize_add(_: usize, _: usize) -> usize;
    fn l_String_toRawSubstring_x27(_: *mut lean_object) -> *mut lean_object;
    fn l_Lean_Syntax_isOfKind(_: *mut lean_object, _: *mut lean_object) -> u8;
    fn l_Lean_Syntax_getArg(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_Lean_SourceInfo_fromRef(_: *mut lean_object, _: u8) -> *mut lean_object;
    fn l_Lean_addMacroScope(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_Lean_Syntax_node1(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_Lean_Syntax_node2(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_Array_mkArray0(_: *mut lean_object) -> *mut lean_object;
    fn l_Lean_Syntax_node3(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_Lean_Syntax_node4(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
}
#[no_mangle] pub static l_isolatedSteppedRange___closed__0_value: lean_ctor_object<1> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*1 + 0) as u16, m_other: 1, m_tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut lean_object] };
static mut l_isolatedSteppedRange___closed__0: *mut lean_object = core::ptr::addr_of!(l_isolatedSteppedRange___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_numDivisors___closed__0_value: lean_ctor_object<1> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*1 + 0) as u16, m_other: 1, m_tag: 1 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut lean_object] };
static mut l_numDivisors___closed__0: *mut lean_object = core::ptr::addr_of!(l_numDivisors___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_primes___closed__0_value: lean_array_object<0> = lean_array_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_primes___closed__0: *mut lean_object = core::ptr::addr_of!(l_primes___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_List_forIn_x27_loop___at___00printEveryNth_spec__1___redArg___closed__0_value: lean_string_object<4> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [120, 115, 91, 0]};
static mut l_List_forIn_x27_loop___at___00printEveryNth_spec__1___redArg___closed__0: *mut lean_object = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00printEveryNth_spec__1___redArg___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_List_forIn_x27_loop___at___00printEveryNth_spec__1___redArg___closed__1_value: lean_string_object<5> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [93, 32, 61, 32, 0]};
static mut l_List_forIn_x27_loop___at___00printEveryNth_spec__1___redArg___closed__1: *mut lean_object = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00printEveryNth_spec__1___redArg___closed__1_value) as *mut lean_object;
#[no_mangle] pub static l_longChainOfCombinators___closed__0_value: lean_ctor_object<1> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*1 + 0) as u16, m_other: 1, m_tag: 1 }, m_objs: [((( 2 as usize) << 1) | 1) as *mut lean_object] };
static mut l_longChainOfCombinators___closed__0: *mut lean_object = core::ptr::addr_of!(l_longChainOfCombinators___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_xs___closed__0_value: lean_ctor_object<2> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 0) as u16, m_other: 2, m_tag: 0 }, m_objs: [core::ptr::addr_of!(l_isolatedSteppedRange___closed__0_value) as *mut lean_object,((( 100000 as usize) << 1) | 1) as *mut lean_object] };
static mut l_xs___closed__0: *mut lean_object = core::ptr::addr_of!(l_xs___closed__0_value) as *mut lean_object;
static mut l_xs___closed__1_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_xs___closed__1: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static mut l_xs: *mut lean_object = core::ptr::null_mut();
static mut l_l___closed__0_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_l___closed__0: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static mut l_l: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static l_termRun___00__closed__0_value: lean_string_object<9> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [116, 101, 114, 109, 82, 117, 110, 95, 0]};
static mut l_termRun___00__closed__0: *mut lean_object = core::ptr::addr_of!(l_termRun___00__closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_termRun___00__closed__1_value: lean_ctor_object<3> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 8) as u16, m_other: 2, m_tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut lean_object,core::ptr::addr_of!(l_termRun___00__closed__0_value) as *mut lean_object,6210590618200463475 as *mut lean_object] };
static mut l_termRun___00__closed__1: *mut lean_object = core::ptr::addr_of!(l_termRun___00__closed__1_value) as *mut lean_object;
#[no_mangle] pub static l_termRun___00__closed__2_value: lean_string_object<8> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [97, 110, 100, 116, 104, 101, 110, 0]};
static mut l_termRun___00__closed__2: *mut lean_object = core::ptr::addr_of!(l_termRun___00__closed__2_value) as *mut lean_object;
#[no_mangle] pub static l_termRun___00__closed__3_value: lean_ctor_object<3> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 8) as u16, m_other: 2, m_tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut lean_object,core::ptr::addr_of!(l_termRun___00__closed__2_value) as *mut lean_object,12571085391447129896 as *mut lean_object] };
static mut l_termRun___00__closed__3: *mut lean_object = core::ptr::addr_of!(l_termRun___00__closed__3_value) as *mut lean_object;
#[no_mangle] pub static l_termRun___00__closed__4_value: lean_string_object<5> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [114, 117, 110, 32, 0]};
static mut l_termRun___00__closed__4: *mut lean_object = core::ptr::addr_of!(l_termRun___00__closed__4_value) as *mut lean_object;
#[no_mangle] pub static l_termRun___00__closed__5_value: lean_ctor_object<1> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*1 + 0) as u16, m_other: 1, m_tag: 5 }, m_objs: [core::ptr::addr_of!(l_termRun___00__closed__4_value) as *mut lean_object] };
static mut l_termRun___00__closed__5: *mut lean_object = core::ptr::addr_of!(l_termRun___00__closed__5_value) as *mut lean_object;
#[no_mangle] pub static l_termRun___00__closed__6_value: lean_string_object<5> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 101, 114, 109, 0]};
static mut l_termRun___00__closed__6: *mut lean_object = core::ptr::addr_of!(l_termRun___00__closed__6_value) as *mut lean_object;
#[no_mangle] pub static l_termRun___00__closed__7_value: lean_ctor_object<3> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 8) as u16, m_other: 2, m_tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut lean_object,core::ptr::addr_of!(l_termRun___00__closed__6_value) as *mut lean_object,8609355255726335675 as *mut lean_object] };
static mut l_termRun___00__closed__7: *mut lean_object = core::ptr::addr_of!(l_termRun___00__closed__7_value) as *mut lean_object;
#[no_mangle] pub static l_termRun___00__closed__8_value: lean_ctor_object<2> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 0) as u16, m_other: 2, m_tag: 7 }, m_objs: [core::ptr::addr_of!(l_termRun___00__closed__7_value) as *mut lean_object,((( 0 as usize) << 1) | 1) as *mut lean_object] };
static mut l_termRun___00__closed__8: *mut lean_object = core::ptr::addr_of!(l_termRun___00__closed__8_value) as *mut lean_object;
#[no_mangle] pub static l_termRun___00__closed__9_value: lean_ctor_object<3> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*3 + 0) as u16, m_other: 3, m_tag: 2 }, m_objs: [core::ptr::addr_of!(l_termRun___00__closed__3_value) as *mut lean_object,core::ptr::addr_of!(l_termRun___00__closed__5_value) as *mut lean_object,core::ptr::addr_of!(l_termRun___00__closed__8_value) as *mut lean_object] };
static mut l_termRun___00__closed__9: *mut lean_object = core::ptr::addr_of!(l_termRun___00__closed__9_value) as *mut lean_object;
#[no_mangle] pub static l_termRun___00__closed__10_value: lean_ctor_object<3> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*3 + 0) as u16, m_other: 3, m_tag: 3 }, m_objs: [core::ptr::addr_of!(l_termRun___00__closed__1_value) as *mut lean_object,((( 1022 as usize) << 1) | 1) as *mut lean_object,core::ptr::addr_of!(l_termRun___00__closed__9_value) as *mut lean_object] };
static mut l_termRun___00__closed__10: *mut lean_object = core::ptr::addr_of!(l_termRun___00__closed__10_value) as *mut lean_object;
#[no_mangle] pub static mut l_termRun__: *mut lean_object = core::ptr::addr_of!(l_termRun___00__closed__10_value) as *mut lean_object;
#[no_mangle] pub static l___aux__iterators______macroRules__termRun____1___closed__0_value: lean_string_object<10> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 101, 114, 109, 95, 60, 36, 62, 95, 0]};
static mut l___aux__iterators______macroRules__termRun____1___closed__0: *mut lean_object = core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l___aux__iterators______macroRules__termRun____1___closed__1_value: lean_ctor_object<3> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 8) as u16, m_other: 2, m_tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut lean_object,core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__0_value) as *mut lean_object,2038039306249128576 as *mut lean_object] };
static mut l___aux__iterators______macroRules__termRun____1___closed__1: *mut lean_object = core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__1_value) as *mut lean_object;
#[no_mangle] pub static l___aux__iterators______macroRules__termRun____1___closed__2_value: lean_string_object<5> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___aux__iterators______macroRules__termRun____1___closed__2: *mut lean_object = core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__2_value) as *mut lean_object;
#[no_mangle] pub static l___aux__iterators______macroRules__termRun____1___closed__3_value: lean_string_object<7> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___aux__iterators______macroRules__termRun____1___closed__3: *mut lean_object = core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__3_value) as *mut lean_object;
#[no_mangle] pub static l___aux__iterators______macroRules__termRun____1___closed__4_value: lean_string_object<5> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l___aux__iterators______macroRules__termRun____1___closed__4: *mut lean_object = core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__4_value) as *mut lean_object;
#[no_mangle] pub static l___aux__iterators______macroRules__termRun____1___closed__5_value: lean_string_object<6> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [112, 97, 114, 101, 110, 0]};
static mut l___aux__iterators______macroRules__termRun____1___closed__5: *mut lean_object = core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__5_value) as *mut lean_object;
static l___aux__iterators______macroRules__termRun____1___closed__6_value_aux_0: lean_ctor_object<3> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 8) as u16, m_other: 2, m_tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut lean_object,core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__2_value) as *mut lean_object,11948124481539785030 as *mut lean_object] };
static l___aux__iterators______macroRules__termRun____1___closed__6_value_aux_1: lean_ctor_object<3> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 8) as u16, m_other: 2, m_tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__6_value_aux_0) as *mut lean_object,core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__3_value) as *mut lean_object,8018486133748762727 as *mut lean_object] };
static l___aux__iterators______macroRules__termRun____1___closed__6_value_aux_2: lean_ctor_object<3> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 8) as u16, m_other: 2, m_tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__6_value_aux_1) as *mut lean_object,core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__4_value) as *mut lean_object,16572064140653406795 as *mut lean_object] };
#[no_mangle] pub static l___aux__iterators______macroRules__termRun____1___closed__6_value: lean_ctor_object<3> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 8) as u16, m_other: 2, m_tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__6_value_aux_2) as *mut lean_object,core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__5_value) as *mut lean_object,7932075773091973500 as *mut lean_object] };
static mut l___aux__iterators______macroRules__termRun____1___closed__6: *mut lean_object = core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__6_value) as *mut lean_object;
#[no_mangle] pub static l___aux__iterators______macroRules__termRun____1___closed__7_value: lean_string_object<15> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [104, 121, 103, 105, 101, 110, 105, 99, 76, 80, 97, 114, 101, 110, 0]};
static mut l___aux__iterators______macroRules__termRun____1___closed__7: *mut lean_object = core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__7_value) as *mut lean_object;
static l___aux__iterators______macroRules__termRun____1___closed__8_value_aux_0: lean_ctor_object<3> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 8) as u16, m_other: 2, m_tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut lean_object,core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__2_value) as *mut lean_object,11948124481539785030 as *mut lean_object] };
static l___aux__iterators______macroRules__termRun____1___closed__8_value_aux_1: lean_ctor_object<3> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 8) as u16, m_other: 2, m_tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__8_value_aux_0) as *mut lean_object,core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__3_value) as *mut lean_object,8018486133748762727 as *mut lean_object] };
static l___aux__iterators______macroRules__termRun____1___closed__8_value_aux_2: lean_ctor_object<3> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 8) as u16, m_other: 2, m_tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__8_value_aux_1) as *mut lean_object,core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__4_value) as *mut lean_object,16572064140653406795 as *mut lean_object] };
#[no_mangle] pub static l___aux__iterators______macroRules__termRun____1___closed__8_value: lean_ctor_object<3> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 8) as u16, m_other: 2, m_tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__8_value_aux_2) as *mut lean_object,core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__7_value) as *mut lean_object,7306243862518720553 as *mut lean_object] };
static mut l___aux__iterators______macroRules__termRun____1___closed__8: *mut lean_object = core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__8_value) as *mut lean_object;
#[no_mangle] pub static l___aux__iterators______macroRules__termRun____1___closed__9_value: lean_string_object<2> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l___aux__iterators______macroRules__termRun____1___closed__9: *mut lean_object = core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__9_value) as *mut lean_object;
#[no_mangle] pub static l___aux__iterators______macroRules__termRun____1___closed__10_value: lean_string_object<12> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0]};
static mut l___aux__iterators______macroRules__termRun____1___closed__10: *mut lean_object = core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__10_value) as *mut lean_object;
#[no_mangle] pub static l___aux__iterators______macroRules__termRun____1___closed__11_value: lean_ctor_object<3> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 8) as u16, m_other: 2, m_tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut lean_object,core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__10_value) as *mut lean_object,9871775667037945883 as *mut lean_object] };
static mut l___aux__iterators______macroRules__termRun____1___closed__11: *mut lean_object = core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__11_value) as *mut lean_object;
#[no_mangle] pub static l___aux__iterators______macroRules__termRun____1___closed__12_value: lean_string_object<1> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l___aux__iterators______macroRules__termRun____1___closed__12: *mut lean_object = core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__12_value) as *mut lean_object;
static mut l___aux__iterators______macroRules__termRun____1___closed__13_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l___aux__iterators______macroRules__termRun____1___closed__13: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static l___aux__iterators______macroRules__termRun____1___closed__14_value: lean_ctor_object<1> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*1 + 0) as u16, m_other: 1, m_tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut lean_object] };
static mut l___aux__iterators______macroRules__termRun____1___closed__14: *mut lean_object = core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__14_value) as *mut lean_object;
#[no_mangle] pub static l___aux__iterators______macroRules__termRun____1___closed__15_value: lean_ctor_object<2> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 0) as u16, m_other: 2, m_tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__14_value) as *mut lean_object,((( 0 as usize) << 1) | 1) as *mut lean_object] };
static mut l___aux__iterators______macroRules__termRun____1___closed__15: *mut lean_object = core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__15_value) as *mut lean_object;
#[no_mangle] pub static l___aux__iterators______macroRules__termRun____1___closed__16_value: lean_string_object<4> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [102, 117, 110, 0]};
static mut l___aux__iterators______macroRules__termRun____1___closed__16: *mut lean_object = core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__16_value) as *mut lean_object;
static l___aux__iterators______macroRules__termRun____1___closed__17_value_aux_0: lean_ctor_object<3> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 8) as u16, m_other: 2, m_tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut lean_object,core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__2_value) as *mut lean_object,11948124481539785030 as *mut lean_object] };
static l___aux__iterators______macroRules__termRun____1___closed__17_value_aux_1: lean_ctor_object<3> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 8) as u16, m_other: 2, m_tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__17_value_aux_0) as *mut lean_object,core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__3_value) as *mut lean_object,8018486133748762727 as *mut lean_object] };
static l___aux__iterators______macroRules__termRun____1___closed__17_value_aux_2: lean_ctor_object<3> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 8) as u16, m_other: 2, m_tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__17_value_aux_1) as *mut lean_object,core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__4_value) as *mut lean_object,16572064140653406795 as *mut lean_object] };
#[no_mangle] pub static l___aux__iterators______macroRules__termRun____1___closed__17_value: lean_ctor_object<3> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 8) as u16, m_other: 2, m_tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__17_value_aux_2) as *mut lean_object,core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__16_value) as *mut lean_object,7043493786777132025 as *mut lean_object] };
static mut l___aux__iterators______macroRules__termRun____1___closed__17: *mut lean_object = core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__17_value) as *mut lean_object;
#[no_mangle] pub static l___aux__iterators______macroRules__termRun____1___closed__18_value: lean_string_object<9> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [98, 97, 115, 105, 99, 70, 117, 110, 0]};
static mut l___aux__iterators______macroRules__termRun____1___closed__18: *mut lean_object = core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__18_value) as *mut lean_object;
static l___aux__iterators______macroRules__termRun____1___closed__19_value_aux_0: lean_ctor_object<3> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 8) as u16, m_other: 2, m_tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut lean_object,core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__2_value) as *mut lean_object,11948124481539785030 as *mut lean_object] };
static l___aux__iterators______macroRules__termRun____1___closed__19_value_aux_1: lean_ctor_object<3> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 8) as u16, m_other: 2, m_tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__19_value_aux_0) as *mut lean_object,core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__3_value) as *mut lean_object,8018486133748762727 as *mut lean_object] };
static l___aux__iterators______macroRules__termRun____1___closed__19_value_aux_2: lean_ctor_object<3> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 8) as u16, m_other: 2, m_tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__19_value_aux_1) as *mut lean_object,core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__4_value) as *mut lean_object,16572064140653406795 as *mut lean_object] };
#[no_mangle] pub static l___aux__iterators______macroRules__termRun____1___closed__19_value: lean_ctor_object<3> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 8) as u16, m_other: 2, m_tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__19_value_aux_2) as *mut lean_object,core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__18_value) as *mut lean_object,16077784126176397009 as *mut lean_object] };
static mut l___aux__iterators______macroRules__termRun____1___closed__19: *mut lean_object = core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__19_value) as *mut lean_object;
#[no_mangle] pub static l___aux__iterators______macroRules__termRun____1___closed__20_value: lean_string_object<5> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l___aux__iterators______macroRules__termRun____1___closed__20: *mut lean_object = core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__20_value) as *mut lean_object;
#[no_mangle] pub static l___aux__iterators______macroRules__termRun____1___closed__21_value: lean_ctor_object<3> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 8) as u16, m_other: 2, m_tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut lean_object,core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__20_value) as *mut lean_object,9855511589286918680 as *mut lean_object] };
static mut l___aux__iterators______macroRules__termRun____1___closed__21: *mut lean_object = core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__21_value) as *mut lean_object;
#[no_mangle] pub static l___aux__iterators______macroRules__termRun____1___closed__22_value: lean_string_object<5> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 111, 108, 101, 0]};
static mut l___aux__iterators______macroRules__termRun____1___closed__22: *mut lean_object = core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__22_value) as *mut lean_object;
static l___aux__iterators______macroRules__termRun____1___closed__23_value_aux_0: lean_ctor_object<3> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 8) as u16, m_other: 2, m_tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut lean_object,core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__2_value) as *mut lean_object,11948124481539785030 as *mut lean_object] };
static l___aux__iterators______macroRules__termRun____1___closed__23_value_aux_1: lean_ctor_object<3> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 8) as u16, m_other: 2, m_tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__23_value_aux_0) as *mut lean_object,core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__3_value) as *mut lean_object,8018486133748762727 as *mut lean_object] };
static l___aux__iterators______macroRules__termRun____1___closed__23_value_aux_2: lean_ctor_object<3> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 8) as u16, m_other: 2, m_tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__23_value_aux_1) as *mut lean_object,core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__4_value) as *mut lean_object,16572064140653406795 as *mut lean_object] };
#[no_mangle] pub static l___aux__iterators______macroRules__termRun____1___closed__23_value: lean_ctor_object<3> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 8) as u16, m_other: 2, m_tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__23_value_aux_2) as *mut lean_object,core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__22_value) as *mut lean_object,3984140175429830279 as *mut lean_object] };
static mut l___aux__iterators______macroRules__termRun____1___closed__23: *mut lean_object = core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__23_value) as *mut lean_object;
#[no_mangle] pub static l___aux__iterators______macroRules__termRun____1___closed__24_value: lean_string_object<2> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [95, 0]};
static mut l___aux__iterators______macroRules__termRun____1___closed__24: *mut lean_object = core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__24_value) as *mut lean_object;
static mut l___aux__iterators______macroRules__termRun____1___closed__25_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l___aux__iterators______macroRules__termRun____1___closed__25: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static l___aux__iterators______macroRules__termRun____1___closed__26_value: lean_string_object<3> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [61, 62, 0]};
static mut l___aux__iterators______macroRules__termRun____1___closed__26: *mut lean_object = core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__26_value) as *mut lean_object;
#[no_mangle] pub static l___aux__iterators______macroRules__termRun____1___closed__27_value: lean_string_object<6> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 117, 112, 108, 101, 0]};
static mut l___aux__iterators______macroRules__termRun____1___closed__27: *mut lean_object = core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__27_value) as *mut lean_object;
static l___aux__iterators______macroRules__termRun____1___closed__28_value_aux_0: lean_ctor_object<3> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 8) as u16, m_other: 2, m_tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut lean_object,core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__2_value) as *mut lean_object,11948124481539785030 as *mut lean_object] };
static l___aux__iterators______macroRules__termRun____1___closed__28_value_aux_1: lean_ctor_object<3> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 8) as u16, m_other: 2, m_tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__28_value_aux_0) as *mut lean_object,core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__3_value) as *mut lean_object,8018486133748762727 as *mut lean_object] };
static l___aux__iterators______macroRules__termRun____1___closed__28_value_aux_2: lean_ctor_object<3> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 8) as u16, m_other: 2, m_tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__28_value_aux_1) as *mut lean_object,core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__4_value) as *mut lean_object,16572064140653406795 as *mut lean_object] };
#[no_mangle] pub static l___aux__iterators______macroRules__termRun____1___closed__28_value: lean_ctor_object<3> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 8) as u16, m_other: 2, m_tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__28_value_aux_2) as *mut lean_object,core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__27_value) as *mut lean_object,15644373471618144447 as *mut lean_object] };
static mut l___aux__iterators______macroRules__termRun____1___closed__28: *mut lean_object = core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__28_value) as *mut lean_object;
#[no_mangle] pub static l___aux__iterators______macroRules__termRun____1___closed__29_value: lean_string_object<2> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l___aux__iterators______macroRules__termRun____1___closed__29: *mut lean_object = core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__29_value) as *mut lean_object;
#[no_mangle] pub static l___aux__iterators______macroRules__termRun____1___closed__30_value: lean_string_object<4> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [60, 36, 62, 0]};
static mut l___aux__iterators______macroRules__termRun____1___closed__30: *mut lean_object = core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__30_value) as *mut lean_object;
#[no_mangle] pub static l___aux__iterators______macroRules__termRun____1___closed__31_value: lean_string_object<4> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l___aux__iterators______macroRules__termRun____1___closed__31: *mut lean_object = core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__31_value) as *mut lean_object;
static l___aux__iterators______macroRules__termRun____1___closed__32_value_aux_0: lean_ctor_object<3> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 8) as u16, m_other: 2, m_tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut lean_object,core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__2_value) as *mut lean_object,11948124481539785030 as *mut lean_object] };
static l___aux__iterators______macroRules__termRun____1___closed__32_value_aux_1: lean_ctor_object<3> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 8) as u16, m_other: 2, m_tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__32_value_aux_0) as *mut lean_object,core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__3_value) as *mut lean_object,8018486133748762727 as *mut lean_object] };
static l___aux__iterators______macroRules__termRun____1___closed__32_value_aux_2: lean_ctor_object<3> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 8) as u16, m_other: 2, m_tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__32_value_aux_1) as *mut lean_object,core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__4_value) as *mut lean_object,16572064140653406795 as *mut lean_object] };
#[no_mangle] pub static l___aux__iterators______macroRules__termRun____1___closed__32_value: lean_ctor_object<3> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 8) as u16, m_other: 2, m_tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__32_value_aux_2) as *mut lean_object,core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__31_value) as *mut lean_object,12966880221525079621 as *mut lean_object] };
static mut l___aux__iterators______macroRules__termRun____1___closed__32: *mut lean_object = core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__32_value) as *mut lean_object;
#[no_mangle] pub static l___aux__iterators______macroRules__termRun____1___closed__33_value: lean_string_object<5> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [114, 117, 110, 39, 0]};
static mut l___aux__iterators______macroRules__termRun____1___closed__33: *mut lean_object = core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__33_value) as *mut lean_object;
static mut l___aux__iterators______macroRules__termRun____1___closed__34_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l___aux__iterators______macroRules__termRun____1___closed__34: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static l___aux__iterators______macroRules__termRun____1___closed__35_value: lean_ctor_object<3> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 8) as u16, m_other: 2, m_tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut lean_object,core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__33_value) as *mut lean_object,4314787603511419052 as *mut lean_object] };
static mut l___aux__iterators______macroRules__termRun____1___closed__35: *mut lean_object = core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__35_value) as *mut lean_object;
#[no_mangle] pub static l___aux__iterators______macroRules__termRun____1___closed__36_value: lean_ctor_object<2> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 0) as u16, m_other: 2, m_tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__35_value) as *mut lean_object,((( 0 as usize) << 1) | 1) as *mut lean_object] };
static mut l___aux__iterators______macroRules__termRun____1___closed__36: *mut lean_object = core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__36_value) as *mut lean_object;
#[no_mangle] pub static l___aux__iterators______macroRules__termRun____1___closed__37_value: lean_ctor_object<2> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 0) as u16, m_other: 2, m_tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__36_value) as *mut lean_object,((( 0 as usize) << 1) | 1) as *mut lean_object] };
static mut l___aux__iterators______macroRules__termRun____1___closed__37: *mut lean_object = core::ptr::addr_of!(l___aux__iterators______macroRules__termRun____1___closed__37_value) as *mut lean_object;
static mut l_main___lam__0___closed__0_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___lam__0___closed__0: *mut lean_object = core::ptr::null_mut();
static mut l_main___lam__1___closed__0_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___lam__1___closed__0: *mut lean_object = core::ptr::null_mut();
static mut l_main___lam__2___closed__0_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___lam__2___closed__0: *mut lean_object = core::ptr::null_mut();
static mut l_main___lam__3___closed__0_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___lam__3___closed__0: *mut lean_object = core::ptr::null_mut();
static mut l_main___lam__4___closed__0_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___lam__4___closed__0: *mut lean_object = core::ptr::null_mut();
static mut l_main___lam__5___closed__0_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___lam__5___closed__0: *mut lean_object = core::ptr::null_mut();
static mut l_main___lam__6___closed__0_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___lam__6___closed__0: *mut lean_object = core::ptr::null_mut();
static mut l_main___lam__7___closed__0_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___lam__7___closed__0: *mut lean_object = core::ptr::null_mut();
static mut l_main___lam__8___closed__0_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___lam__8___closed__0: *mut lean_object = core::ptr::null_mut();
static mut l_main___lam__9___closed__0_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___lam__9___closed__0: *mut lean_object = core::ptr::null_mut();
static mut l_main___lam__10___closed__0_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___lam__10___closed__0: *mut lean_object = core::ptr::null_mut();
static mut l_main___lam__11___closed__0_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___lam__11___closed__0: *mut lean_object = core::ptr::null_mut();
static mut l_main___lam__12___closed__0_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___lam__12___closed__0: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static l_main___closed__0_value: lean_closure_object<0> = lean_closure_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 245 }, m_fun: l_main___lam__0 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_main___closed__0: *mut lean_object = core::ptr::addr_of!(l_main___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__1_value: lean_closure_object<0> = lean_closure_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 245 }, m_fun: l_main___lam__1 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_main___closed__1: *mut lean_object = core::ptr::addr_of!(l_main___closed__1_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__2_value: lean_closure_object<0> = lean_closure_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 245 }, m_fun: l_main___lam__2 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_main___closed__2: *mut lean_object = core::ptr::addr_of!(l_main___closed__2_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__3_value: lean_closure_object<0> = lean_closure_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 245 }, m_fun: l_main___lam__3 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_main___closed__3: *mut lean_object = core::ptr::addr_of!(l_main___closed__3_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__4_value: lean_closure_object<0> = lean_closure_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 245 }, m_fun: l_main___lam__4 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_main___closed__4: *mut lean_object = core::ptr::addr_of!(l_main___closed__4_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__5_value: lean_closure_object<0> = lean_closure_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 245 }, m_fun: l_main___lam__5 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_main___closed__5: *mut lean_object = core::ptr::addr_of!(l_main___closed__5_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__6_value: lean_closure_object<0> = lean_closure_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 245 }, m_fun: l_main___lam__6 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_main___closed__6: *mut lean_object = core::ptr::addr_of!(l_main___closed__6_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__7_value: lean_closure_object<0> = lean_closure_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 245 }, m_fun: l_main___lam__7 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_main___closed__7: *mut lean_object = core::ptr::addr_of!(l_main___closed__7_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__8_value: lean_closure_object<0> = lean_closure_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 245 }, m_fun: l_main___lam__8 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_main___closed__8: *mut lean_object = core::ptr::addr_of!(l_main___closed__8_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__9_value: lean_closure_object<0> = lean_closure_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 245 }, m_fun: l_main___lam__9 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_main___closed__9: *mut lean_object = core::ptr::addr_of!(l_main___closed__9_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__10_value: lean_closure_object<0> = lean_closure_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 245 }, m_fun: l_main___lam__10 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_main___closed__10: *mut lean_object = core::ptr::addr_of!(l_main___closed__10_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__11_value: lean_closure_object<0> = lean_closure_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 245 }, m_fun: l_main___lam__11 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_main___closed__11: *mut lean_object = core::ptr::addr_of!(l_main___closed__11_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__12_value: lean_closure_object<0> = lean_closure_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 245 }, m_fun: l_main___lam__12 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_main___closed__12: *mut lean_object = core::ptr::addr_of!(l_main___closed__12_value) as *mut lean_object;
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00sum_u2081_spec__0___redArg(mut v_a_1_: *mut lean_object, mut v_b_2_: *mut lean_object) -> *mut lean_object{
let mut v_array_3_: *mut lean_object = core::ptr::null_mut(); let mut v_pos_4_: *mut lean_object = core::ptr::null_mut(); let mut v___x_6_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_7_: u8 = 0; let mut v___x_8_: *mut lean_object = core::ptr::null_mut(); let mut v___x_9_: u8 = 0; let mut v___x_10_: *mut lean_object = core::ptr::null_mut(); let mut v___x_11_: *mut lean_object = core::ptr::null_mut(); let mut v___x_13_: *mut lean_object = core::ptr::null_mut(); let mut v___x_14_: *mut lean_object = core::ptr::null_mut(); let mut v___x_15_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_17_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_18_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v_array_3_ = lean_ctor_get(v_a_1_, 0);
v_pos_4_ = lean_ctor_get(v_a_1_, 1);
v_isSharedCheck_18_ = (!lean_is_exclusive(v_a_1_)) as u8;
if v_isSharedCheck_18_ == 0 {
v___x_6_ = v_a_1_;
v_isShared_7_ = v_isSharedCheck_18_;
state = 1; continue;
} else {
lean_inc(v_pos_4_);
lean_inc(v_array_3_);
lean_dec(v_a_1_);
v___x_6_ = lean_box(0);
v_isShared_7_ = v_isSharedCheck_18_;
state = 1; continue;
}
}
1 => {
v___x_8_ = lean_array_get_size(v_array_3_);
v___x_9_ = lean_nat_dec_lt(v_pos_4_, v___x_8_);
if v___x_9_ == 0 {
lean_del_object(v___x_6_);
lean_dec(v_pos_4_);
lean_dec_ref(v_array_3_);
return v_b_2_;
} else {
let mut v___x_10_: *mut lean_object = core::ptr::null_mut(); let mut v___x_11_: *mut lean_object = core::ptr::null_mut(); let mut v___x_13_: *mut lean_object = core::ptr::null_mut(); 
v___x_10_ = lean_unsigned_to_nat(1);
v___x_11_ = lean_nat_add(v_pos_4_, v___x_10_);
lean_inc_ref(v_array_3_);
if v_isShared_7_ == 0 {
lean_ctor_set(v___x_6_, 1, v___x_11_);
v___x_13_ = v___x_6_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_17_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_17_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_17_, 0, v_array_3_);
lean_ctor_set(v_reuseFailAlloc_17_, 1, v___x_11_);
v___x_13_ = v_reuseFailAlloc_17_;
state = 2; continue;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_sum_u2081(mut v_xs_19_: *mut lean_object) -> *mut lean_object{
let mut v___x_20_: *mut lean_object = core::ptr::null_mut(); let mut v___x_21_: *mut lean_object = core::ptr::null_mut(); let mut v___x_22_: *mut lean_object = core::ptr::null_mut(); 
v___x_20_ = lean_unsigned_to_nat(0);
v___x_21_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_21_, 0, v_xs_19_);
lean_ctor_set(v___x_21_, 1, v___x_20_);
v___x_22_ = l_WellFounded_opaqueFix_u2083___at___00sum_u2081_spec__0___redArg(v___x_21_, v___x_20_);
return v___x_22_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00sum_u2081_spec__0(mut v_inst_23_: *mut lean_object, mut v_R_24_: *mut lean_object, mut v_a_25_: *mut lean_object, mut v_b_26_: *mut lean_object, mut v_c_27_: *mut lean_object) -> *mut lean_object{
let mut v___x_28_: *mut lean_object = core::ptr::null_mut(); 
v___x_28_ = l_WellFounded_opaqueFix_u2083___at___00sum_u2081_spec__0___redArg(v_a_25_, v_b_26_);
return v___x_28_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00sum_u2082_spec__0(mut v_as_29_: *mut lean_object, mut v_sz_30_: usize, mut v_i_31_: usize, mut v_b_32_: *mut lean_object) -> *mut lean_object{
let mut v___x_33_: u8 = 0; let mut v_a_34_: *mut lean_object = core::ptr::null_mut(); let mut v___x_35_: *mut lean_object = core::ptr::null_mut(); let mut v___x_36_: usize = 0; let mut v___x_37_: usize = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_33_ = lean_usize_dec_lt(v_i_31_, v_sz_30_);
if v___x_33_ == 0 {
return v_b_32_;
} else {
let mut v_a_34_: *mut lean_object = core::ptr::null_mut(); let mut v___x_35_: *mut lean_object = core::ptr::null_mut(); let mut v___x_36_: usize = 0; let mut v___x_37_: usize = 0; 
v_a_34_ = lean_array_uget_borrowed(v_as_29_, v_i_31_);
v___x_35_ = lean_nat_add(v_b_32_, v_a_34_);
lean_dec(v_b_32_);
v___x_36_ = 1usize;
v___x_37_ = lean_usize_add(v_i_31_, v___x_36_);
v_i_31_ = v___x_37_;
v_b_32_ = v___x_35_;
state = 0; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00sum_u2082_spec__0___boxed(mut v_as_39_: *mut lean_object, mut v_sz_40_: *mut lean_object, mut v_i_41_: *mut lean_object, mut v_b_42_: *mut lean_object) -> *mut lean_object{
let mut v_sz_boxed_43_: usize = 0; let mut v_i_boxed_44_: usize = 0; let mut v_res_45_: *mut lean_object = core::ptr::null_mut(); 
v_sz_boxed_43_ = lean_unbox_usize(v_sz_40_);
lean_dec(v_sz_40_);
v_i_boxed_44_ = lean_unbox_usize(v_i_41_);
lean_dec(v_i_41_);
v_res_45_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00sum_u2082_spec__0(v_as_39_, v_sz_boxed_43_, v_i_boxed_44_, v_b_42_);
lean_dec_ref(v_as_39_);
return v_res_45_;
}
#[no_mangle] pub unsafe extern "C" fn l_sum_u2082(mut v_xs_46_: *mut lean_object) -> *mut lean_object{
let mut v_sum_47_: *mut lean_object = core::ptr::null_mut(); let mut v_sz_48_: usize = 0; let mut v___x_49_: usize = 0; let mut v___x_50_: *mut lean_object = core::ptr::null_mut(); 
v_sum_47_ = lean_unsigned_to_nat(0);
v_sz_48_ = lean_array_size(v_xs_46_);
v___x_49_ = 0usize;
v___x_50_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00sum_u2082_spec__0(v_xs_46_, v_sz_48_, v___x_49_, v_sum_47_);
return v___x_50_;
}
#[no_mangle] pub unsafe extern "C" fn l_sum_u2082___boxed(mut v_xs_51_: *mut lean_object) -> *mut lean_object{
let mut v_res_52_: *mut lean_object = core::ptr::null_mut(); 
v_res_52_ = l_sum_u2082(v_xs_51_);
lean_dec_ref(v_xs_51_);
return v_res_52_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00isolatedMap_spec__0___redArg(mut v_a_53_: *mut lean_object, mut v_b_54_: *mut lean_object) -> *mut lean_object{
let mut v_array_55_: *mut lean_object = core::ptr::null_mut(); let mut v_pos_56_: *mut lean_object = core::ptr::null_mut(); let mut v___x_58_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_59_: u8 = 0; let mut v___x_60_: *mut lean_object = core::ptr::null_mut(); let mut v___x_61_: u8 = 0; let mut v___x_62_: *mut lean_object = core::ptr::null_mut(); let mut v___x_63_: *mut lean_object = core::ptr::null_mut(); let mut v___x_65_: *mut lean_object = core::ptr::null_mut(); let mut v___x_66_: *mut lean_object = core::ptr::null_mut(); let mut v___x_67_: *mut lean_object = core::ptr::null_mut(); let mut v___x_68_: *mut lean_object = core::ptr::null_mut(); let mut v___x_69_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_71_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_72_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v_array_55_ = lean_ctor_get(v_a_53_, 0);
v_pos_56_ = lean_ctor_get(v_a_53_, 1);
v_isSharedCheck_72_ = (!lean_is_exclusive(v_a_53_)) as u8;
if v_isSharedCheck_72_ == 0 {
v___x_58_ = v_a_53_;
v_isShared_59_ = v_isSharedCheck_72_;
state = 1; continue;
} else {
lean_inc(v_pos_56_);
lean_inc(v_array_55_);
lean_dec(v_a_53_);
v___x_58_ = lean_box(0);
v_isShared_59_ = v_isSharedCheck_72_;
state = 1; continue;
}
}
1 => {
v___x_60_ = lean_array_get_size(v_array_55_);
v___x_61_ = lean_nat_dec_lt(v_pos_56_, v___x_60_);
if v___x_61_ == 0 {
lean_del_object(v___x_58_);
lean_dec(v_pos_56_);
lean_dec_ref(v_array_55_);
return v_b_54_;
} else {
let mut v___x_62_: *mut lean_object = core::ptr::null_mut(); let mut v___x_63_: *mut lean_object = core::ptr::null_mut(); let mut v___x_65_: *mut lean_object = core::ptr::null_mut(); 
v___x_62_ = lean_unsigned_to_nat(1);
v___x_63_ = lean_nat_add(v_pos_56_, v___x_62_);
lean_inc_ref(v_array_55_);
if v_isShared_59_ == 0 {
lean_ctor_set(v___x_58_, 1, v___x_63_);
v___x_65_ = v___x_58_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_71_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_71_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_71_, 0, v_array_55_);
lean_ctor_set(v_reuseFailAlloc_71_, 1, v___x_63_);
v___x_65_ = v_reuseFailAlloc_71_;
state = 2; continue;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_isolatedMap(mut v_xs_73_: *mut lean_object) -> *mut lean_object{
let mut v___x_74_: *mut lean_object = core::ptr::null_mut(); let mut v___x_75_: *mut lean_object = core::ptr::null_mut(); let mut v___x_76_: *mut lean_object = core::ptr::null_mut(); 
v___x_74_ = lean_unsigned_to_nat(0);
v___x_75_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_75_, 0, v_xs_73_);
lean_ctor_set(v___x_75_, 1, v___x_74_);
v___x_76_ = l_WellFounded_opaqueFix_u2083___at___00isolatedMap_spec__0___redArg(v___x_75_, v___x_74_);
return v___x_76_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00isolatedMap_spec__0(mut v_inst_77_: *mut lean_object, mut v_R_78_: *mut lean_object, mut v_a_79_: *mut lean_object, mut v_b_80_: *mut lean_object, mut v_c_81_: *mut lean_object) -> *mut lean_object{
let mut v___x_82_: *mut lean_object = core::ptr::null_mut(); 
v___x_82_ = l_WellFounded_opaqueFix_u2083___at___00isolatedMap_spec__0___redArg(v_a_79_, v_b_80_);
return v___x_82_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00isolatedFilterMap_spec__0___redArg(mut v_a_83_: *mut lean_object, mut v_b_84_: *mut lean_object) -> *mut lean_object{
let mut v_array_85_: *mut lean_object = core::ptr::null_mut(); let mut v_pos_86_: *mut lean_object = core::ptr::null_mut(); let mut v___x_88_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_89_: u8 = 0; let mut v___x_90_: *mut lean_object = core::ptr::null_mut(); let mut v___x_91_: u8 = 0; let mut v___x_92_: *mut lean_object = core::ptr::null_mut(); let mut v___x_93_: *mut lean_object = core::ptr::null_mut(); let mut v___x_95_: *mut lean_object = core::ptr::null_mut(); let mut v___x_96_: *mut lean_object = core::ptr::null_mut(); let mut v___x_97_: *mut lean_object = core::ptr::null_mut(); let mut v___x_98_: *mut lean_object = core::ptr::null_mut(); let mut v___x_99_: *mut lean_object = core::ptr::null_mut(); let mut v___x_100_: *mut lean_object = core::ptr::null_mut(); let mut v___x_101_: *mut lean_object = core::ptr::null_mut(); let mut v___x_102_: u8 = 0; let mut v___x_104_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_106_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_107_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v_array_85_ = lean_ctor_get(v_a_83_, 0);
v_pos_86_ = lean_ctor_get(v_a_83_, 1);
v_isSharedCheck_107_ = (!lean_is_exclusive(v_a_83_)) as u8;
if v_isSharedCheck_107_ == 0 {
v___x_88_ = v_a_83_;
v_isShared_89_ = v_isSharedCheck_107_;
state = 1; continue;
} else {
lean_inc(v_pos_86_);
lean_inc(v_array_85_);
lean_dec(v_a_83_);
v___x_88_ = lean_box(0);
v_isShared_89_ = v_isSharedCheck_107_;
state = 1; continue;
}
}
1 => {
v___x_90_ = lean_array_get_size(v_array_85_);
v___x_91_ = lean_nat_dec_lt(v_pos_86_, v___x_90_);
if v___x_91_ == 0 {
lean_del_object(v___x_88_);
lean_dec(v_pos_86_);
lean_dec_ref(v_array_85_);
return v_b_84_;
} else {
let mut v___x_92_: *mut lean_object = core::ptr::null_mut(); let mut v___x_93_: *mut lean_object = core::ptr::null_mut(); let mut v___x_95_: *mut lean_object = core::ptr::null_mut(); 
v___x_92_ = lean_unsigned_to_nat(1);
v___x_93_ = lean_nat_add(v_pos_86_, v___x_92_);
lean_inc_ref(v_array_85_);
if v_isShared_89_ == 0 {
lean_ctor_set(v___x_88_, 1, v___x_93_);
v___x_95_ = v___x_88_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_106_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_106_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v_array_85_);
lean_ctor_set(v_reuseFailAlloc_106_, 1, v___x_93_);
v___x_95_ = v_reuseFailAlloc_106_;
state = 2; continue;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_isolatedFilterMap(mut v_xs_108_: *mut lean_object) -> *mut lean_object{
let mut v___x_109_: *mut lean_object = core::ptr::null_mut(); let mut v___x_110_: *mut lean_object = core::ptr::null_mut(); let mut v___x_111_: *mut lean_object = core::ptr::null_mut(); 
v___x_109_ = lean_unsigned_to_nat(0);
v___x_110_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_110_, 0, v_xs_108_);
lean_ctor_set(v___x_110_, 1, v___x_109_);
v___x_111_ = l_WellFounded_opaqueFix_u2083___at___00isolatedFilterMap_spec__0___redArg(v___x_110_, v___x_109_);
return v___x_111_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00isolatedFilterMap_spec__0(mut v_inst_112_: *mut lean_object, mut v_R_113_: *mut lean_object, mut v_a_114_: *mut lean_object, mut v_b_115_: *mut lean_object, mut v_c_116_: *mut lean_object) -> *mut lean_object{
let mut v___x_117_: *mut lean_object = core::ptr::null_mut(); 
v___x_117_ = l_WellFounded_opaqueFix_u2083___at___00isolatedFilterMap_spec__0___redArg(v_a_114_, v_b_115_);
return v___x_117_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00isolatedTake_spec__0___redArg(mut v_a_118_: *mut lean_object, mut v_b_119_: *mut lean_object) -> *mut lean_object{
let mut v_countdown_120_: *mut lean_object = core::ptr::null_mut(); let mut v_inner_121_: *mut lean_object = core::ptr::null_mut(); let mut v___x_123_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_124_: u8 = 0; let mut v___x_125_: *mut lean_object = core::ptr::null_mut(); let mut v___x_126_: u8 = 0; let mut v_array_127_: *mut lean_object = core::ptr::null_mut(); let mut v_pos_128_: *mut lean_object = core::ptr::null_mut(); let mut v___x_130_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_131_: u8 = 0; let mut v___x_132_: *mut lean_object = core::ptr::null_mut(); let mut v___x_133_: u8 = 0; let mut v___x_134_: *mut lean_object = core::ptr::null_mut(); let mut v___x_136_: *mut lean_object = core::ptr::null_mut(); let mut v___x_137_: *mut lean_object = core::ptr::null_mut(); let mut v___x_138_: *mut lean_object = core::ptr::null_mut(); let mut v___x_140_: *mut lean_object = core::ptr::null_mut(); let mut v___x_141_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_143_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_144_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_145_: u8 = 0; let mut v_isSharedCheck_146_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v_countdown_120_ = lean_ctor_get(v_a_118_, 0);
v_inner_121_ = lean_ctor_get(v_a_118_, 1);
v_isSharedCheck_146_ = (!lean_is_exclusive(v_a_118_)) as u8;
if v_isSharedCheck_146_ == 0 {
v___x_123_ = v_a_118_;
v_isShared_124_ = v_isSharedCheck_146_;
state = 1; continue;
} else {
lean_inc(v_inner_121_);
lean_inc(v_countdown_120_);
lean_dec(v_a_118_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_146_;
state = 1; continue;
}
}
1 => {
v___x_125_ = lean_unsigned_to_nat(1);
v___x_126_ = lean_nat_dec_eq(v_countdown_120_, v___x_125_);
if v___x_126_ == 0 {
let mut v_array_127_: *mut lean_object = core::ptr::null_mut(); let mut v_pos_128_: *mut lean_object = core::ptr::null_mut(); let mut v___x_130_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_131_: u8 = 0; let mut v_isSharedCheck_145_: u8 = 0; 
v_array_127_ = lean_ctor_get(v_inner_121_, 0);
v_pos_128_ = lean_ctor_get(v_inner_121_, 1);
v_isSharedCheck_145_ = (!lean_is_exclusive(v_inner_121_)) as u8;
if v_isSharedCheck_145_ == 0 {
v___x_130_ = v_inner_121_;
v_isShared_131_ = v_isSharedCheck_145_;
state = 2; continue;
} else {
lean_inc(v_pos_128_);
lean_inc(v_array_127_);
lean_dec(v_inner_121_);
v___x_130_ = lean_box(0);
v_isShared_131_ = v_isSharedCheck_145_;
state = 2; continue;
}
} else {
lean_del_object(v___x_123_);
lean_dec(v_inner_121_);
lean_dec(v_countdown_120_);
return v_b_119_;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_isolatedTake(mut v_xs_147_: *mut lean_object, mut v_n_148_: *mut lean_object) -> *mut lean_object{
let mut v___x_149_: *mut lean_object = core::ptr::null_mut(); let mut v___x_150_: *mut lean_object = core::ptr::null_mut(); let mut v___x_151_: *mut lean_object = core::ptr::null_mut(); let mut v___x_152_: *mut lean_object = core::ptr::null_mut(); let mut v___x_153_: *mut lean_object = core::ptr::null_mut(); let mut v___x_154_: *mut lean_object = core::ptr::null_mut(); 
v___x_149_ = lean_unsigned_to_nat(0);
v___x_150_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_150_, 0, v_xs_147_);
lean_ctor_set(v___x_150_, 1, v___x_149_);
v___x_151_ = lean_unsigned_to_nat(1);
v___x_152_ = lean_nat_add(v_n_148_, v___x_151_);
v___x_153_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_153_, 0, v___x_152_);
lean_ctor_set(v___x_153_, 1, v___x_150_);
v___x_154_ = l_WellFounded_opaqueFix_u2083___at___00isolatedTake_spec__0___redArg(v___x_153_, v___x_149_);
return v___x_154_;
}
#[no_mangle] pub unsafe extern "C" fn l_isolatedTake___boxed(mut v_xs_155_: *mut lean_object, mut v_n_156_: *mut lean_object) -> *mut lean_object{
let mut v_res_157_: *mut lean_object = core::ptr::null_mut(); 
v_res_157_ = l_isolatedTake(v_xs_155_, v_n_156_);
lean_dec(v_n_156_);
return v_res_157_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00isolatedTake_spec__0(mut v_inst_158_: *mut lean_object, mut v_R_159_: *mut lean_object, mut v_a_160_: *mut lean_object, mut v_b_161_: *mut lean_object, mut v_c_162_: *mut lean_object) -> *mut lean_object{
let mut v___x_163_: *mut lean_object = core::ptr::null_mut(); 
v___x_163_ = l_WellFounded_opaqueFix_u2083___at___00isolatedTake_spec__0___redArg(v_a_160_, v_b_161_);
return v___x_163_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00isolatedDrop_spec__0___redArg(mut v_a_164_: *mut lean_object, mut v_b_165_: *mut lean_object) -> *mut lean_object{
let mut v_inner_166_: *mut lean_object = core::ptr::null_mut(); let mut v_remaining_167_: *mut lean_object = core::ptr::null_mut(); let mut v___x_169_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_170_: u8 = 0; let mut v_array_171_: *mut lean_object = core::ptr::null_mut(); let mut v_pos_172_: *mut lean_object = core::ptr::null_mut(); let mut v___x_174_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_175_: u8 = 0; let mut v___x_176_: *mut lean_object = core::ptr::null_mut(); let mut v___x_177_: u8 = 0; let mut v___x_178_: *mut lean_object = core::ptr::null_mut(); let mut v___x_179_: *mut lean_object = core::ptr::null_mut(); let mut v___x_181_: *mut lean_object = core::ptr::null_mut(); let mut v_zero_182_: *mut lean_object = core::ptr::null_mut(); let mut v_isZero_183_: u8 = 0; let mut v___x_184_: *mut lean_object = core::ptr::null_mut(); let mut v___x_186_: *mut lean_object = core::ptr::null_mut(); let mut v___x_187_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_189_: *mut lean_object = core::ptr::null_mut(); let mut v_n_190_: *mut lean_object = core::ptr::null_mut(); let mut v___x_192_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_194_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_195_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_196_: u8 = 0; let mut v_isSharedCheck_197_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v_inner_166_ = lean_ctor_get(v_a_164_, 1);
v_remaining_167_ = lean_ctor_get(v_a_164_, 0);
v_isSharedCheck_197_ = (!lean_is_exclusive(v_a_164_)) as u8;
if v_isSharedCheck_197_ == 0 {
v___x_169_ = v_a_164_;
v_isShared_170_ = v_isSharedCheck_197_;
state = 1; continue;
} else {
lean_inc(v_inner_166_);
lean_inc(v_remaining_167_);
lean_dec(v_a_164_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_197_;
state = 1; continue;
}
}
1 => {
v_array_171_ = lean_ctor_get(v_inner_166_, 0);
v_pos_172_ = lean_ctor_get(v_inner_166_, 1);
v_isSharedCheck_196_ = (!lean_is_exclusive(v_inner_166_)) as u8;
if v_isSharedCheck_196_ == 0 {
v___x_174_ = v_inner_166_;
v_isShared_175_ = v_isSharedCheck_196_;
state = 2; continue;
} else {
lean_inc(v_pos_172_);
lean_inc(v_array_171_);
lean_dec(v_inner_166_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_196_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_isolatedDrop(mut v_xs_198_: *mut lean_object, mut v_n_199_: *mut lean_object) -> *mut lean_object{
let mut v___x_200_: *mut lean_object = core::ptr::null_mut(); let mut v___x_201_: *mut lean_object = core::ptr::null_mut(); let mut v___x_202_: *mut lean_object = core::ptr::null_mut(); let mut v___x_203_: *mut lean_object = core::ptr::null_mut(); 
v___x_200_ = lean_unsigned_to_nat(0);
v___x_201_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_201_, 0, v_xs_198_);
lean_ctor_set(v___x_201_, 1, v___x_200_);
v___x_202_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_202_, 0, v_n_199_);
lean_ctor_set(v___x_202_, 1, v___x_201_);
v___x_203_ = l_WellFounded_opaqueFix_u2083___at___00isolatedDrop_spec__0___redArg(v___x_202_, v___x_200_);
return v___x_203_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00isolatedDrop_spec__0(mut v_inst_204_: *mut lean_object, mut v_R_205_: *mut lean_object, mut v_a_206_: *mut lean_object, mut v_b_207_: *mut lean_object, mut v_c_208_: *mut lean_object) -> *mut lean_object{
let mut v___x_209_: *mut lean_object = core::ptr::null_mut(); 
v___x_209_ = l_WellFounded_opaqueFix_u2083___at___00isolatedDrop_spec__0___redArg(v_a_206_, v_b_207_);
return v___x_209_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00isolatedTakeWhile_spec__0___redArg(mut v_a_210_: *mut lean_object, mut v_b_211_: *mut lean_object) -> *mut lean_object{
let mut v_array_212_: *mut lean_object = core::ptr::null_mut(); let mut v_pos_213_: *mut lean_object = core::ptr::null_mut(); let mut v___x_215_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_216_: u8 = 0; let mut v___x_217_: *mut lean_object = core::ptr::null_mut(); let mut v___x_218_: u8 = 0; let mut v___x_219_: *mut lean_object = core::ptr::null_mut(); let mut v___x_220_: *mut lean_object = core::ptr::null_mut(); let mut v___x_221_: u8 = 0; let mut v___x_222_: *mut lean_object = core::ptr::null_mut(); let mut v___x_223_: *mut lean_object = core::ptr::null_mut(); let mut v___x_225_: *mut lean_object = core::ptr::null_mut(); let mut v___x_226_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_228_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_229_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v_array_212_ = lean_ctor_get(v_a_210_, 0);
v_pos_213_ = lean_ctor_get(v_a_210_, 1);
v_isSharedCheck_229_ = (!lean_is_exclusive(v_a_210_)) as u8;
if v_isSharedCheck_229_ == 0 {
v___x_215_ = v_a_210_;
v_isShared_216_ = v_isSharedCheck_229_;
state = 1; continue;
} else {
lean_inc(v_pos_213_);
lean_inc(v_array_212_);
lean_dec(v_a_210_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_229_;
state = 1; continue;
}
}
1 => {
v___x_217_ = lean_array_get_size(v_array_212_);
v___x_218_ = lean_nat_dec_lt(v_pos_213_, v___x_217_);
if v___x_218_ == 0 {
lean_del_object(v___x_215_);
lean_dec(v_pos_213_);
lean_dec_ref(v_array_212_);
return v_b_211_;
} else {
let mut v___x_219_: *mut lean_object = core::ptr::null_mut(); let mut v___x_220_: *mut lean_object = core::ptr::null_mut(); let mut v___x_221_: u8 = 0; 
v___x_219_ = lean_array_fget(v_array_212_, v_pos_213_);
v___x_220_ = lean_unsigned_to_nat(100000);
v___x_221_ = lean_nat_dec_lt(v___x_219_, v___x_220_);
if v___x_221_ == 0 {
lean_dec(v___x_219_);
lean_del_object(v___x_215_);
lean_dec(v_pos_213_);
lean_dec_ref(v_array_212_);
return v_b_211_;
} else {
let mut v___x_222_: *mut lean_object = core::ptr::null_mut(); let mut v___x_223_: *mut lean_object = core::ptr::null_mut(); let mut v___x_225_: *mut lean_object = core::ptr::null_mut(); 
v___x_222_ = lean_unsigned_to_nat(1);
v___x_223_ = lean_nat_add(v_pos_213_, v___x_222_);
lean_dec(v_pos_213_);
if v_isShared_216_ == 0 {
lean_ctor_set(v___x_215_, 1, v___x_223_);
v___x_225_ = v___x_215_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_228_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_228_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v_array_212_);
lean_ctor_set(v_reuseFailAlloc_228_, 1, v___x_223_);
v___x_225_ = v_reuseFailAlloc_228_;
state = 2; continue;
}
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_isolatedTakeWhile(mut v_xs_230_: *mut lean_object) -> *mut lean_object{
let mut v___x_231_: *mut lean_object = core::ptr::null_mut(); let mut v___x_232_: *mut lean_object = core::ptr::null_mut(); let mut v___x_233_: *mut lean_object = core::ptr::null_mut(); 
v___x_231_ = lean_unsigned_to_nat(0);
v___x_232_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_232_, 0, v_xs_230_);
lean_ctor_set(v___x_232_, 1, v___x_231_);
v___x_233_ = l_WellFounded_opaqueFix_u2083___at___00isolatedTakeWhile_spec__0___redArg(v___x_232_, v___x_231_);
return v___x_233_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00isolatedTakeWhile_spec__0(mut v_inst_234_: *mut lean_object, mut v_R_235_: *mut lean_object, mut v_a_236_: *mut lean_object, mut v_b_237_: *mut lean_object, mut v_c_238_: *mut lean_object) -> *mut lean_object{
let mut v___x_239_: *mut lean_object = core::ptr::null_mut(); 
v___x_239_ = l_WellFounded_opaqueFix_u2083___at___00isolatedTakeWhile_spec__0___redArg(v_a_236_, v_b_237_);
return v___x_239_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00isolatedDropWhile_spec__0___redArg(mut v_a_240_: *mut lean_object, mut v_b_241_: *mut lean_object) -> *mut lean_object{
let mut v_it_243_: *mut lean_object = core::ptr::null_mut(); let mut v_out_244_: *mut lean_object = core::ptr::null_mut(); let mut v___x_245_: *mut lean_object = core::ptr::null_mut(); let mut v_inner_247_: *mut lean_object = core::ptr::null_mut(); let mut v_dropping_248_: u8 = 0; let mut v___x_250_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_251_: u8 = 0; let mut v_array_252_: *mut lean_object = core::ptr::null_mut(); let mut v_pos_253_: *mut lean_object = core::ptr::null_mut(); let mut v___x_255_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_256_: u8 = 0; let mut v___x_257_: *mut lean_object = core::ptr::null_mut(); let mut v___x_258_: u8 = 0; let mut v___x_259_: *mut lean_object = core::ptr::null_mut(); let mut v___x_260_: *mut lean_object = core::ptr::null_mut(); let mut v___x_262_: *mut lean_object = core::ptr::null_mut(); let mut v___x_263_: *mut lean_object = core::ptr::null_mut(); let mut v___x_265_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_266_: *mut lean_object = core::ptr::null_mut(); let mut v___x_267_: *mut lean_object = core::ptr::null_mut(); let mut v___x_268_: u8 = 0; let mut v___x_270_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_271_: *mut lean_object = core::ptr::null_mut(); let mut v___x_273_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_275_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_276_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_277_: u8 = 0; let mut v_isSharedCheck_278_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v_inner_247_ = lean_ctor_get(v_a_240_, 0);
v_dropping_248_ = lean_ctor_get_uint8(v_a_240_, (core::mem::size_of::<*mut lean_object>()*1) as u32);
v_isSharedCheck_278_ = (!lean_is_exclusive(v_a_240_)) as u8;
if v_isSharedCheck_278_ == 0 {
v___x_250_ = v_a_240_;
v_isShared_251_ = v_isSharedCheck_278_;
state = 2; continue;
} else {
lean_inc(v_inner_247_);
lean_dec(v_a_240_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_278_;
state = 2; continue;
}
}
1 => {
v___x_245_ = lean_nat_add(v_b_241_, v_out_244_);
lean_dec(v_out_244_);
lean_dec(v_b_241_);
v_a_240_ = v_it_243_;
v_b_241_ = v___x_245_;
state = 0; continue;
}
2 => {
v_array_252_ = lean_ctor_get(v_inner_247_, 0);
v_pos_253_ = lean_ctor_get(v_inner_247_, 1);
v_isSharedCheck_277_ = (!lean_is_exclusive(v_inner_247_)) as u8;
if v_isSharedCheck_277_ == 0 {
v___x_255_ = v_inner_247_;
v_isShared_256_ = v_isSharedCheck_277_;
state = 3; continue;
} else {
lean_inc(v_pos_253_);
lean_inc(v_array_252_);
lean_dec(v_inner_247_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_277_;
state = 3; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_isolatedDropWhile(mut v_xs_279_: *mut lean_object) -> *mut lean_object{
let mut v___x_280_: *mut lean_object = core::ptr::null_mut(); let mut v___x_281_: *mut lean_object = core::ptr::null_mut(); let mut v___x_282_: u8 = 0; let mut v___x_283_: *mut lean_object = core::ptr::null_mut(); let mut v___x_284_: *mut lean_object = core::ptr::null_mut(); 
v___x_280_ = lean_unsigned_to_nat(0);
v___x_281_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_281_, 0, v_xs_279_);
lean_ctor_set(v___x_281_, 1, v___x_280_);
v___x_282_ = 1;
v___x_283_ = lean_alloc_ctor(0, 1, (1) as u32);
lean_ctor_set(v___x_283_, 0, v___x_281_);
lean_ctor_set_uint8(v___x_283_, (core::mem::size_of::<*mut lean_object>()*1) as u32, v___x_282_);
v___x_284_ = l_WellFounded_opaqueFix_u2083___at___00isolatedDropWhile_spec__0___redArg(v___x_283_, v___x_280_);
return v___x_284_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00isolatedDropWhile_spec__0(mut v_inst_285_: *mut lean_object, mut v_R_286_: *mut lean_object, mut v_a_287_: *mut lean_object, mut v_b_288_: *mut lean_object, mut v_c_289_: *mut lean_object) -> *mut lean_object{
let mut v___x_290_: *mut lean_object = core::ptr::null_mut(); 
v___x_290_ = l_WellFounded_opaqueFix_u2083___at___00isolatedDropWhile_spec__0___redArg(v_a_287_, v_b_288_);
return v___x_290_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00isolatedZip_spec__0___redArg(mut v_a_291_: *mut lean_object, mut v_b_292_: *mut lean_object) -> *mut lean_object{
let mut v_memoizedLeft_293_: *mut lean_object = core::ptr::null_mut(); let mut v_left_294_: *mut lean_object = core::ptr::null_mut(); let mut v_right_295_: *mut lean_object = core::ptr::null_mut(); let mut v___x_297_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_298_: u8 = 0; let mut v_array_299_: *mut lean_object = core::ptr::null_mut(); let mut v_pos_300_: *mut lean_object = core::ptr::null_mut(); let mut v___x_302_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_303_: u8 = 0; let mut v___x_304_: *mut lean_object = core::ptr::null_mut(); let mut v___x_305_: u8 = 0; let mut v___x_306_: *mut lean_object = core::ptr::null_mut(); let mut v___x_307_: *mut lean_object = core::ptr::null_mut(); let mut v___x_309_: *mut lean_object = core::ptr::null_mut(); let mut v___x_310_: *mut lean_object = core::ptr::null_mut(); let mut v___x_311_: *mut lean_object = core::ptr::null_mut(); let mut v___x_313_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_315_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_316_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_317_: u8 = 0; let mut v_isSharedCheck_318_: u8 = 0; let mut v_unused_319_: *mut lean_object = core::ptr::null_mut(); let mut v_right_320_: *mut lean_object = core::ptr::null_mut(); let mut v_left_321_: *mut lean_object = core::ptr::null_mut(); let mut v___x_323_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_324_: u8 = 0; let mut v_val_325_: *mut lean_object = core::ptr::null_mut(); let mut v_array_326_: *mut lean_object = core::ptr::null_mut(); let mut v_pos_327_: *mut lean_object = core::ptr::null_mut(); let mut v___x_329_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_330_: u8 = 0; let mut v___x_331_: *mut lean_object = core::ptr::null_mut(); let mut v___x_332_: u8 = 0; let mut v___x_333_: *mut lean_object = core::ptr::null_mut(); let mut v___x_334_: *mut lean_object = core::ptr::null_mut(); let mut v___x_336_: *mut lean_object = core::ptr::null_mut(); let mut v___x_337_: *mut lean_object = core::ptr::null_mut(); let mut v___x_338_: *mut lean_object = core::ptr::null_mut(); let mut v___x_340_: *mut lean_object = core::ptr::null_mut(); let mut v___x_341_: *mut lean_object = core::ptr::null_mut(); let mut v___x_342_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_344_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_345_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_346_: u8 = 0; let mut v_isSharedCheck_347_: u8 = 0; let mut v_unused_348_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v_memoizedLeft_293_ = lean_ctor_get(v_a_291_, 1);
if lean_obj_tag(v_memoizedLeft_293_) == 0 {
let mut v_left_294_: *mut lean_object = core::ptr::null_mut(); let mut v_right_295_: *mut lean_object = core::ptr::null_mut(); let mut v___x_297_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_298_: u8 = 0; let mut v_isSharedCheck_318_: u8 = 0; 
v_left_294_ = lean_ctor_get(v_a_291_, 0);
v_right_295_ = lean_ctor_get(v_a_291_, 2);
v_isSharedCheck_318_ = (!lean_is_exclusive(v_a_291_)) as u8;
if v_isSharedCheck_318_ == 0 {
let mut v_unused_319_: *mut lean_object = core::ptr::null_mut(); 
v_unused_319_ = lean_ctor_get(v_a_291_, 1);
lean_dec(v_unused_319_);
v___x_297_ = v_a_291_;
v_isShared_298_ = v_isSharedCheck_318_;
state = 1; continue;
} else {
lean_inc(v_right_295_);
lean_inc(v_left_294_);
lean_dec(v_a_291_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_318_;
state = 1; continue;
}
} else {
let mut v_right_320_: *mut lean_object = core::ptr::null_mut(); let mut v_left_321_: *mut lean_object = core::ptr::null_mut(); let mut v___x_323_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_324_: u8 = 0; let mut v_isSharedCheck_347_: u8 = 0; 
lean_inc_ref(v_memoizedLeft_293_);
v_right_320_ = lean_ctor_get(v_a_291_, 2);
v_left_321_ = lean_ctor_get(v_a_291_, 0);
v_isSharedCheck_347_ = (!lean_is_exclusive(v_a_291_)) as u8;
if v_isSharedCheck_347_ == 0 {
let mut v_unused_348_: *mut lean_object = core::ptr::null_mut(); 
v_unused_348_ = lean_ctor_get(v_a_291_, 1);
lean_dec(v_unused_348_);
v___x_323_ = v_a_291_;
v_isShared_324_ = v_isSharedCheck_347_;
state = 5; continue;
} else {
lean_inc(v_right_320_);
lean_inc(v_left_321_);
lean_dec(v_a_291_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_347_;
state = 5; continue;
}
}
}
1 => {
v_array_299_ = lean_ctor_get(v_left_294_, 0);
v_pos_300_ = lean_ctor_get(v_left_294_, 1);
v_isSharedCheck_317_ = (!lean_is_exclusive(v_left_294_)) as u8;
if v_isSharedCheck_317_ == 0 {
v___x_302_ = v_left_294_;
v_isShared_303_ = v_isSharedCheck_317_;
state = 2; continue;
} else {
lean_inc(v_pos_300_);
lean_inc(v_array_299_);
lean_dec(v_left_294_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_317_;
state = 2; continue;
}
}
5 => {
v_val_325_ = lean_ctor_get(v_memoizedLeft_293_, 0);
lean_inc(v_val_325_);
lean_dec_ref_known(v_memoizedLeft_293_, 1);
v_array_326_ = lean_ctor_get(v_right_320_, 0);
v_pos_327_ = lean_ctor_get(v_right_320_, 1);
v_isSharedCheck_346_ = (!lean_is_exclusive(v_right_320_)) as u8;
if v_isSharedCheck_346_ == 0 {
v___x_329_ = v_right_320_;
v_isShared_330_ = v_isSharedCheck_346_;
state = 6; continue;
} else {
lean_inc(v_pos_327_);
lean_inc(v_array_326_);
lean_dec(v_right_320_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_346_;
state = 6; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_isolatedZip(mut v_xs_349_: *mut lean_object, mut v_ys_350_: *mut lean_object) -> *mut lean_object{
let mut v___x_351_: *mut lean_object = core::ptr::null_mut(); let mut v___x_352_: *mut lean_object = core::ptr::null_mut(); let mut v___x_353_: *mut lean_object = core::ptr::null_mut(); let mut v___x_354_: *mut lean_object = core::ptr::null_mut(); let mut v___x_355_: *mut lean_object = core::ptr::null_mut(); let mut v___x_356_: *mut lean_object = core::ptr::null_mut(); 
v___x_351_ = lean_unsigned_to_nat(0);
v___x_352_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_352_, 0, v_xs_349_);
lean_ctor_set(v___x_352_, 1, v___x_351_);
v___x_353_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_353_, 0, v_ys_350_);
lean_ctor_set(v___x_353_, 1, v___x_351_);
v___x_354_ = lean_box(0);
v___x_355_ = lean_alloc_ctor(0, 3, (0) as u32);
lean_ctor_set(v___x_355_, 0, v___x_352_);
lean_ctor_set(v___x_355_, 1, v___x_354_);
lean_ctor_set(v___x_355_, 2, v___x_353_);
v___x_356_ = l_WellFounded_opaqueFix_u2083___at___00isolatedZip_spec__0___redArg(v___x_355_, v___x_351_);
return v___x_356_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00isolatedZip_spec__0(mut v_inst_357_: *mut lean_object, mut v_R_358_: *mut lean_object, mut v_a_359_: *mut lean_object, mut v_b_360_: *mut lean_object, mut v_c_361_: *mut lean_object) -> *mut lean_object{
let mut v___x_362_: *mut lean_object = core::ptr::null_mut(); 
v___x_362_ = l_WellFounded_opaqueFix_u2083___at___00isolatedZip_spec__0___redArg(v_a_359_, v_b_360_);
return v___x_362_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00isolatedSteppedRange_spec__0___redArg(mut v_a_363_: *mut lean_object, mut v_b_364_: *mut lean_object) -> *mut lean_object{
let mut v_inner_365_: *mut lean_object = core::ptr::null_mut(); let mut v_next_366_: *mut lean_object = core::ptr::null_mut(); let mut v_nextIdx_367_: *mut lean_object = core::ptr::null_mut(); let mut v_n_368_: *mut lean_object = core::ptr::null_mut(); let mut v___x_370_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_371_: u8 = 0; let mut v_upperBound_372_: *mut lean_object = core::ptr::null_mut(); let mut v___x_374_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_375_: u8 = 0; let mut v_val_376_: *mut lean_object = core::ptr::null_mut(); let mut v___x_378_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_379_: u8 = 0; let mut v___x_380_: *mut lean_object = core::ptr::null_mut(); let mut v___x_381_: u8 = 0; let mut v___x_382_: *mut lean_object = core::ptr::null_mut(); let mut v___x_383_: *mut lean_object = core::ptr::null_mut(); let mut v___x_385_: *mut lean_object = core::ptr::null_mut(); let mut v___x_387_: *mut lean_object = core::ptr::null_mut(); let mut v___x_389_: *mut lean_object = core::ptr::null_mut(); let mut v___x_390_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_392_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_393_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_394_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_395_: u8 = 0; let mut v_isSharedCheck_396_: u8 = 0; let mut v_unused_397_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_398_: u8 = 0; let mut v_unused_399_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v_inner_365_ = lean_ctor_get(v_a_363_, 2);
lean_inc(v_inner_365_);
v_next_366_ = lean_ctor_get(v_inner_365_, 0);
lean_inc(v_next_366_);
if lean_obj_tag(v_next_366_) == 0 {
lean_dec(v_inner_365_);
lean_dec_ref(v_a_363_);
return v_b_364_;
} else {
let mut v_nextIdx_367_: *mut lean_object = core::ptr::null_mut(); let mut v_n_368_: *mut lean_object = core::ptr::null_mut(); let mut v___x_370_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_371_: u8 = 0; let mut v_isSharedCheck_398_: u8 = 0; 
v_nextIdx_367_ = lean_ctor_get(v_a_363_, 0);
v_n_368_ = lean_ctor_get(v_a_363_, 1);
v_isSharedCheck_398_ = (!lean_is_exclusive(v_a_363_)) as u8;
if v_isSharedCheck_398_ == 0 {
let mut v_unused_399_: *mut lean_object = core::ptr::null_mut(); 
v_unused_399_ = lean_ctor_get(v_a_363_, 2);
lean_dec(v_unused_399_);
v___x_370_ = v_a_363_;
v_isShared_371_ = v_isSharedCheck_398_;
state = 1; continue;
} else {
lean_inc(v_n_368_);
lean_inc(v_nextIdx_367_);
lean_dec(v_a_363_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_398_;
state = 1; continue;
}
}
}
1 => {
v_upperBound_372_ = lean_ctor_get(v_inner_365_, 1);
v_isSharedCheck_396_ = (!lean_is_exclusive(v_inner_365_)) as u8;
if v_isSharedCheck_396_ == 0 {
let mut v_unused_397_: *mut lean_object = core::ptr::null_mut(); 
v_unused_397_ = lean_ctor_get(v_inner_365_, 0);
lean_dec(v_unused_397_);
v___x_374_ = v_inner_365_;
v_isShared_375_ = v_isSharedCheck_396_;
state = 2; continue;
} else {
lean_inc(v_upperBound_372_);
lean_dec(v_inner_365_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_396_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_isolatedSteppedRange(mut v_n_402_: *mut lean_object) -> *mut lean_object{
let mut v___x_403_: *mut lean_object = core::ptr::null_mut(); let mut v___x_404_: *mut lean_object = core::ptr::null_mut(); let mut v___x_405_: *mut lean_object = core::ptr::null_mut(); let mut v___x_406_: *mut lean_object = core::ptr::null_mut(); let mut v___x_407_: *mut lean_object = core::ptr::null_mut(); let mut v___x_408_: *mut lean_object = core::ptr::null_mut(); 
v___x_403_ = lean_unsigned_to_nat(0);
v___x_404_ = l_isolatedSteppedRange___closed__0;
v___x_405_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_405_, 0, v___x_404_);
lean_ctor_set(v___x_405_, 1, v_n_402_);
v___x_406_ = lean_unsigned_to_nat(1);
v___x_407_ = lean_alloc_ctor(0, 3, (0) as u32);
lean_ctor_set(v___x_407_, 0, v___x_403_);
lean_ctor_set(v___x_407_, 1, v___x_406_);
lean_ctor_set(v___x_407_, 2, v___x_405_);
v___x_408_ = l_WellFounded_opaqueFix_u2083___at___00isolatedSteppedRange_spec__0___redArg(v___x_407_, v___x_403_);
return v___x_408_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00isolatedSteppedRange_spec__0(mut v_inst_409_: *mut lean_object, mut v_R_410_: *mut lean_object, mut v_a_411_: *mut lean_object, mut v_b_412_: *mut lean_object, mut v_c_413_: *mut lean_object) -> *mut lean_object{
let mut v___x_414_: *mut lean_object = core::ptr::null_mut(); 
v___x_414_ = l_WellFounded_opaqueFix_u2083___at___00isolatedSteppedRange_spec__0___redArg(v_a_411_, v_b_412_);
return v___x_414_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00numDivisors_spec__0___redArg(mut v_n_415_: *mut lean_object, mut v_a_416_: *mut lean_object, mut v_b_417_: *mut lean_object) -> *mut lean_object{
let mut v_next_418_: *mut lean_object = core::ptr::null_mut(); let mut v_upperBound_419_: *mut lean_object = core::ptr::null_mut(); let mut v___x_421_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_422_: u8 = 0; let mut v_val_423_: *mut lean_object = core::ptr::null_mut(); let mut v___x_425_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_426_: u8 = 0; let mut v___x_427_: u8 = 0; let mut v___x_428_: *mut lean_object = core::ptr::null_mut(); let mut v___x_429_: *mut lean_object = core::ptr::null_mut(); let mut v___x_431_: *mut lean_object = core::ptr::null_mut(); let mut v___x_433_: *mut lean_object = core::ptr::null_mut(); let mut v___x_434_: *mut lean_object = core::ptr::null_mut(); let mut v___x_435_: *mut lean_object = core::ptr::null_mut(); let mut v___x_436_: u8 = 0; let mut v___x_438_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_440_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_441_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_442_: u8 = 0; let mut v_isSharedCheck_443_: u8 = 0; let mut v_unused_444_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v_next_418_ = lean_ctor_get(v_a_416_, 0);
lean_inc(v_next_418_);
if lean_obj_tag(v_next_418_) == 0 {
lean_dec_ref(v_a_416_);
return v_b_417_;
} else {
let mut v_upperBound_419_: *mut lean_object = core::ptr::null_mut(); let mut v___x_421_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_422_: u8 = 0; let mut v_isSharedCheck_443_: u8 = 0; 
v_upperBound_419_ = lean_ctor_get(v_a_416_, 1);
v_isSharedCheck_443_ = (!lean_is_exclusive(v_a_416_)) as u8;
if v_isSharedCheck_443_ == 0 {
let mut v_unused_444_: *mut lean_object = core::ptr::null_mut(); 
v_unused_444_ = lean_ctor_get(v_a_416_, 0);
lean_dec(v_unused_444_);
v___x_421_ = v_a_416_;
v_isShared_422_ = v_isSharedCheck_443_;
state = 1; continue;
} else {
lean_inc(v_upperBound_419_);
lean_dec(v_a_416_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_443_;
state = 1; continue;
}
}
}
1 => {
v_val_423_ = lean_ctor_get(v_next_418_, 0);
v_isSharedCheck_442_ = (!lean_is_exclusive(v_next_418_)) as u8;
if v_isSharedCheck_442_ == 0 {
v___x_425_ = v_next_418_;
v_isShared_426_ = v_isSharedCheck_442_;
state = 2; continue;
} else {
lean_inc(v_val_423_);
lean_dec(v_next_418_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_442_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00numDivisors_spec__0___redArg___boxed(mut v_n_445_: *mut lean_object, mut v_a_446_: *mut lean_object, mut v_b_447_: *mut lean_object) -> *mut lean_object{
let mut v_res_448_: *mut lean_object = core::ptr::null_mut(); 
v_res_448_ = l_WellFounded_opaqueFix_u2083___at___00numDivisors_spec__0___redArg(v_n_445_, v_a_446_, v_b_447_);
lean_dec(v_n_445_);
return v_res_448_;
}
#[no_mangle] pub unsafe extern "C" fn l_numDivisors(mut v_n_451_: *mut lean_object) -> *mut lean_object{
let mut v___x_452_: *mut lean_object = core::ptr::null_mut(); let mut v___x_453_: *mut lean_object = core::ptr::null_mut(); let mut v___x_454_: *mut lean_object = core::ptr::null_mut(); let mut v___x_455_: *mut lean_object = core::ptr::null_mut(); 
v___x_452_ = l_numDivisors___closed__0;
lean_inc(v_n_451_);
v___x_453_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_453_, 0, v___x_452_);
lean_ctor_set(v___x_453_, 1, v_n_451_);
v___x_454_ = lean_unsigned_to_nat(0);
v___x_455_ = l_WellFounded_opaqueFix_u2083___at___00numDivisors_spec__0___redArg(v_n_451_, v___x_453_, v___x_454_);
lean_dec(v_n_451_);
return v___x_455_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00numDivisors_spec__0(mut v_n_456_: *mut lean_object, mut v_inst_457_: *mut lean_object, mut v_R_458_: *mut lean_object, mut v_a_459_: *mut lean_object, mut v_b_460_: *mut lean_object, mut v_c_461_: *mut lean_object) -> *mut lean_object{
let mut v___x_462_: *mut lean_object = core::ptr::null_mut(); 
v___x_462_ = l_WellFounded_opaqueFix_u2083___at___00numDivisors_spec__0___redArg(v_n_456_, v_a_459_, v_b_460_);
return v___x_462_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00numDivisors_spec__0___boxed(mut v_n_463_: *mut lean_object, mut v_inst_464_: *mut lean_object, mut v_R_465_: *mut lean_object, mut v_a_466_: *mut lean_object, mut v_b_467_: *mut lean_object, mut v_c_468_: *mut lean_object) -> *mut lean_object{
let mut v_res_469_: *mut lean_object = core::ptr::null_mut(); 
v_res_469_ = l_WellFounded_opaqueFix_u2083___at___00numDivisors_spec__0(v_n_463_, v_inst_464_, v_R_465_, v_a_466_, v_b_467_, v_c_468_);
lean_dec(v_n_463_);
return v_res_469_;
}
#[no_mangle] pub unsafe extern "C" fn l_isPrime(mut v_n_470_: *mut lean_object) -> u8{
let mut v___x_471_: *mut lean_object = core::ptr::null_mut(); let mut v___x_472_: *mut lean_object = core::ptr::null_mut(); let mut v___x_473_: u8 = 0; 
v___x_471_ = l_numDivisors(v_n_470_);
v___x_472_ = lean_unsigned_to_nat(2);
v___x_473_ = lean_nat_dec_eq(v___x_471_, v___x_472_);
lean_dec(v___x_471_);
return v___x_473_;
}
#[no_mangle] pub unsafe extern "C" fn l_isPrime___boxed(mut v_n_474_: *mut lean_object) -> *mut lean_object{
let mut v_res_475_: u8 = 0; let mut v_r_476_: *mut lean_object = core::ptr::null_mut(); 
v_res_475_ = l_isPrime(v_n_474_);
v_r_476_ = lean_box((v_res_475_) as usize);
return v_r_476_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00primes_spec__0___redArg(mut v_a_477_: *mut lean_object, mut v_b_478_: *mut lean_object) -> *mut lean_object{
let mut v_countdown_479_: *mut lean_object = core::ptr::null_mut(); let mut v_inner_480_: *mut lean_object = core::ptr::null_mut(); let mut v___x_482_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_483_: u8 = 0; let mut v___x_484_: *mut lean_object = core::ptr::null_mut(); let mut v___x_485_: u8 = 0; let mut v_val_486_: *mut lean_object = core::ptr::null_mut(); let mut v___x_488_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_489_: u8 = 0; let mut v___x_490_: *mut lean_object = core::ptr::null_mut(); let mut v___x_492_: *mut lean_object = core::ptr::null_mut(); let mut v___x_493_: *mut lean_object = core::ptr::null_mut(); let mut v___x_495_: *mut lean_object = core::ptr::null_mut(); let mut v___x_496_: u8 = 0; let mut v___x_498_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_500_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_501_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_502_: u8 = 0; let mut v_isSharedCheck_503_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v_countdown_479_ = lean_ctor_get(v_a_477_, 0);
v_inner_480_ = lean_ctor_get(v_a_477_, 1);
v_isSharedCheck_503_ = (!lean_is_exclusive(v_a_477_)) as u8;
if v_isSharedCheck_503_ == 0 {
v___x_482_ = v_a_477_;
v_isShared_483_ = v_isSharedCheck_503_;
state = 1; continue;
} else {
lean_inc(v_inner_480_);
lean_inc(v_countdown_479_);
lean_dec(v_a_477_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_503_;
state = 1; continue;
}
}
1 => {
v___x_484_ = lean_unsigned_to_nat(1);
v___x_485_ = lean_nat_dec_eq(v_countdown_479_, v___x_484_);
if v___x_485_ == 0 {
if lean_obj_tag(v_inner_480_) == 0 {
lean_del_object(v___x_482_);
lean_dec(v_countdown_479_);
return v_b_478_;
} else {
let mut v_val_486_: *mut lean_object = core::ptr::null_mut(); let mut v___x_488_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_489_: u8 = 0; let mut v_isSharedCheck_502_: u8 = 0; 
v_val_486_ = lean_ctor_get(v_inner_480_, 0);
v_isSharedCheck_502_ = (!lean_is_exclusive(v_inner_480_)) as u8;
if v_isSharedCheck_502_ == 0 {
v___x_488_ = v_inner_480_;
v_isShared_489_ = v_isSharedCheck_502_;
state = 2; continue;
} else {
lean_inc(v_val_486_);
lean_dec(v_inner_480_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_502_;
state = 2; continue;
}
}
} else {
lean_del_object(v___x_482_);
lean_dec(v_inner_480_);
lean_dec(v_countdown_479_);
return v_b_478_;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_primes(mut v_n_506_: *mut lean_object) -> *mut lean_object{
let mut v___x_507_: *mut lean_object = core::ptr::null_mut(); let mut v___x_508_: *mut lean_object = core::ptr::null_mut(); let mut v___x_509_: *mut lean_object = core::ptr::null_mut(); let mut v___x_510_: *mut lean_object = core::ptr::null_mut(); let mut v___x_511_: *mut lean_object = core::ptr::null_mut(); let mut v___x_512_: *mut lean_object = core::ptr::null_mut(); let mut v___x_513_: *mut lean_object = core::ptr::null_mut(); 
v___x_507_ = l_isolatedSteppedRange___closed__0;
v___x_508_ = lean_unsigned_to_nat(1);
v___x_509_ = lean_nat_add(v_n_506_, v___x_508_);
v___x_510_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_510_, 0, v___x_509_);
lean_ctor_set(v___x_510_, 1, v___x_507_);
v___x_511_ = l_primes___closed__0;
v___x_512_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00primes_spec__0___redArg(v___x_510_, v___x_511_);
v___x_513_ = lean_array_to_list(v___x_512_);
return v___x_513_;
}
#[no_mangle] pub unsafe extern "C" fn l_primes___boxed(mut v_n_514_: *mut lean_object) -> *mut lean_object{
let mut v_res_515_: *mut lean_object = core::ptr::null_mut(); 
v_res_515_ = l_primes(v_n_514_);
lean_dec(v_n_514_);
return v_res_515_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00primes_spec__0(mut v_inst_516_: *mut lean_object, mut v_R_517_: *mut lean_object, mut v_a_518_: *mut lean_object, mut v_b_519_: *mut lean_object) -> *mut lean_object{
let mut v___x_520_: *mut lean_object = core::ptr::null_mut(); 
v___x_520_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00primes_spec__0___redArg(v_a_518_, v_b_519_);
return v___x_520_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00printEveryNth_spec__0_spec__0(mut v_s_521_: *mut lean_object) -> *mut lean_object{
let mut v___x_523_: *mut lean_object = core::ptr::null_mut(); let mut v_putStr_524_: *mut lean_object = core::ptr::null_mut(); let mut v___x_525_: *mut lean_object = core::ptr::null_mut(); 
v___x_523_ = lean_get_stdout();
v_putStr_524_ = lean_ctor_get(v___x_523_, 4);
lean_inc_ref(v_putStr_524_);
lean_dec_ref(v___x_523_);
v___x_525_ = lean_apply_2(v_putStr_524_, v_s_521_, lean_box(0));
return v___x_525_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00printEveryNth_spec__0_spec__0___boxed(mut v_s_526_: *mut lean_object, mut v_a_527_: *mut lean_object) -> *mut lean_object{
let mut v_res_528_: *mut lean_object = core::ptr::null_mut(); 
v_res_528_ = l_IO_print___at___00IO_println___at___00printEveryNth_spec__0_spec__0(v_s_526_);
return v_res_528_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00printEveryNth_spec__0(mut v_s_529_: *mut lean_object) -> *mut lean_object{
let mut v___x_531_: u32 = 0; let mut v___x_532_: *mut lean_object = core::ptr::null_mut(); let mut v___x_533_: *mut lean_object = core::ptr::null_mut(); 
v___x_531_ = 10;
v___x_532_ = lean_string_push(v_s_529_, v___x_531_);
v___x_533_ = l_IO_print___at___00IO_println___at___00printEveryNth_spec__0_spec__0(v___x_532_);
return v___x_533_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00printEveryNth_spec__0___boxed(mut v_s_534_: *mut lean_object, mut v_a_535_: *mut lean_object) -> *mut lean_object{
let mut v_res_536_: *mut lean_object = core::ptr::null_mut(); 
v_res_536_ = l_IO_println___at___00printEveryNth_spec__0(v_s_534_);
return v_res_536_;
}
#[no_mangle] pub unsafe extern "C" fn l_List_forIn_x27_loop___at___00printEveryNth_spec__1___redArg(mut v_n_539_: *mut lean_object, mut v_as_x27_540_: *mut lean_object, mut v_b_541_: *mut lean_object) -> *mut lean_object{
let mut v___x_543_: *mut lean_object = core::ptr::null_mut(); let mut v___x_544_: *mut lean_object = core::ptr::null_mut(); let mut v_head_545_: *mut lean_object = core::ptr::null_mut(); let mut v_tail_546_: *mut lean_object = core::ptr::null_mut(); let mut v_val_547_: *mut lean_object = core::ptr::null_mut(); let mut v___x_549_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_550_: u8 = 0; let mut v___x_551_: *mut lean_object = core::ptr::null_mut(); let mut v___x_552_: *mut lean_object = core::ptr::null_mut(); let mut v___x_554_: *mut lean_object = core::ptr::null_mut(); let mut v___x_555_: *mut lean_object = core::ptr::null_mut(); let mut v___x_556_: *mut lean_object = core::ptr::null_mut(); let mut v___x_557_: u8 = 0; let mut v___x_559_: *mut lean_object = core::ptr::null_mut(); let mut v___x_560_: *mut lean_object = core::ptr::null_mut(); let mut v___x_561_: *mut lean_object = core::ptr::null_mut(); let mut v___x_562_: *mut lean_object = core::ptr::null_mut(); let mut v___x_563_: *mut lean_object = core::ptr::null_mut(); let mut v___x_564_: *mut lean_object = core::ptr::null_mut(); let mut v___x_565_: *mut lean_object = core::ptr::null_mut(); let mut v___x_566_: *mut lean_object = core::ptr::null_mut(); let mut v_a_568_: *mut lean_object = core::ptr::null_mut(); let mut v___x_570_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_571_: u8 = 0; let mut v___x_573_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_574_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_575_: u8 = 0; let mut v_reuseFailAlloc_576_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_577_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_as_x27_540_) == 0 {
let mut v___x_543_: *mut lean_object = core::ptr::null_mut(); 
v___x_543_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_543_, 0, v_b_541_);
return v___x_543_;
} else {
if lean_obj_tag(v_b_541_) == 0 {
let mut v___x_544_: *mut lean_object = core::ptr::null_mut(); 
v___x_544_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_544_, 0, v_b_541_);
return v___x_544_;
} else {
let mut v_head_545_: *mut lean_object = core::ptr::null_mut(); let mut v_tail_546_: *mut lean_object = core::ptr::null_mut(); let mut v_val_547_: *mut lean_object = core::ptr::null_mut(); let mut v___x_549_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_550_: u8 = 0; let mut v_isSharedCheck_577_: u8 = 0; 
v_head_545_ = lean_ctor_get(v_as_x27_540_, 0);
v_tail_546_ = lean_ctor_get(v_as_x27_540_, 1);
v_val_547_ = lean_ctor_get(v_b_541_, 0);
v_isSharedCheck_577_ = (!lean_is_exclusive(v_b_541_)) as u8;
if v_isSharedCheck_577_ == 0 {
v___x_549_ = v_b_541_;
v_isShared_550_ = v_isSharedCheck_577_;
state = 1; continue;
} else {
lean_inc(v_val_547_);
lean_dec(v_b_541_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_577_;
state = 1; continue;
}
}
}
}
1 => {
v___x_551_ = lean_unsigned_to_nat(1);
v___x_552_ = lean_nat_add(v_val_547_, v___x_551_);
if v_isShared_550_ == 0 {
lean_ctor_set(v___x_549_, 0, v___x_552_);
v___x_554_ = v___x_549_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_576_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_576_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v___x_552_);
v___x_554_ = v_reuseFailAlloc_576_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_List_forIn_x27_loop___at___00printEveryNth_spec__1___redArg___boxed(mut v_n_578_: *mut lean_object, mut v_as_x27_579_: *mut lean_object, mut v_b_580_: *mut lean_object, mut v___y_581_: *mut lean_object) -> *mut lean_object{
let mut v_res_582_: *mut lean_object = core::ptr::null_mut(); 
v_res_582_ = l_List_forIn_x27_loop___at___00printEveryNth_spec__1___redArg(v_n_578_, v_as_x27_579_, v_b_580_);
lean_dec(v_as_x27_579_);
lean_dec(v_n_578_);
return v_res_582_;
}
#[no_mangle] pub unsafe extern "C" fn l_printEveryNth(mut v_xs_583_: *mut lean_object, mut v_n_584_: *mut lean_object) -> *mut lean_object{
let mut v___x_586_: *mut lean_object = core::ptr::null_mut(); let mut v___x_587_: *mut lean_object = core::ptr::null_mut(); let mut v___x_589_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_590_: u8 = 0; let mut v___x_591_: *mut lean_object = core::ptr::null_mut(); let mut v___x_593_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_594_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_595_: u8 = 0; let mut v_unused_596_: *mut lean_object = core::ptr::null_mut(); let mut v_a_597_: *mut lean_object = core::ptr::null_mut(); let mut v___x_599_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_600_: u8 = 0; let mut v___x_602_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_603_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_604_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_586_ = l_isolatedSteppedRange___closed__0;
v___x_587_ = l_List_forIn_x27_loop___at___00printEveryNth_spec__1___redArg(v_n_584_, v_xs_583_, v___x_586_);
if lean_obj_tag(v___x_587_) == 0 {
let mut v___x_589_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_590_: u8 = 0; let mut v_isSharedCheck_595_: u8 = 0; 
v_isSharedCheck_595_ = (!lean_is_exclusive(v___x_587_)) as u8;
if v_isSharedCheck_595_ == 0 {
let mut v_unused_596_: *mut lean_object = core::ptr::null_mut(); 
v_unused_596_ = lean_ctor_get(v___x_587_, 0);
lean_dec(v_unused_596_);
v___x_589_ = v___x_587_;
v_isShared_590_ = v_isSharedCheck_595_;
state = 1; continue;
} else {
lean_dec(v___x_587_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_595_;
state = 1; continue;
}
} else {
let mut v_a_597_: *mut lean_object = core::ptr::null_mut(); let mut v___x_599_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_600_: u8 = 0; let mut v_isSharedCheck_604_: u8 = 0; 
v_a_597_ = lean_ctor_get(v___x_587_, 0);
v_isSharedCheck_604_ = (!lean_is_exclusive(v___x_587_)) as u8;
if v_isSharedCheck_604_ == 0 {
v___x_599_ = v___x_587_;
v_isShared_600_ = v_isSharedCheck_604_;
state = 3; continue;
} else {
lean_inc(v_a_597_);
lean_dec(v___x_587_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_604_;
state = 3; continue;
}
}
}
1 => {
v___x_591_ = lean_box(0);
if v_isShared_590_ == 0 {
lean_ctor_set(v___x_589_, 0, v___x_591_);
v___x_593_ = v___x_589_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_594_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v___x_591_);
v___x_593_ = v_reuseFailAlloc_594_;
state = 2; continue;
}
}
3 => {
if v_isShared_600_ == 0 {
v___x_602_ = v___x_599_;
state = 4; continue;
} else {
let mut v_reuseFailAlloc_603_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_603_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v_a_597_);
v___x_602_ = v_reuseFailAlloc_603_;
state = 4; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_printEveryNth___boxed(mut v_xs_605_: *mut lean_object, mut v_n_606_: *mut lean_object, mut v_a_607_: *mut lean_object) -> *mut lean_object{
let mut v_res_608_: *mut lean_object = core::ptr::null_mut(); 
v_res_608_ = l_printEveryNth(v_xs_605_, v_n_606_);
lean_dec(v_n_606_);
lean_dec(v_xs_605_);
return v_res_608_;
}
#[no_mangle] pub unsafe extern "C" fn l_List_forIn_x27_loop___at___00printEveryNth_spec__1(mut v_n_609_: *mut lean_object, mut v_as_610_: *mut lean_object, mut v_as_x27_611_: *mut lean_object, mut v_b_612_: *mut lean_object, mut v_a_613_: *mut lean_object) -> *mut lean_object{
let mut v___x_615_: *mut lean_object = core::ptr::null_mut(); 
v___x_615_ = l_List_forIn_x27_loop___at___00printEveryNth_spec__1___redArg(v_n_609_, v_as_x27_611_, v_b_612_);
return v___x_615_;
}
#[no_mangle] pub unsafe extern "C" fn l_List_forIn_x27_loop___at___00printEveryNth_spec__1___boxed(mut v_n_616_: *mut lean_object, mut v_as_617_: *mut lean_object, mut v_as_x27_618_: *mut lean_object, mut v_b_619_: *mut lean_object, mut v_a_620_: *mut lean_object, mut v___y_621_: *mut lean_object) -> *mut lean_object{
let mut v_res_622_: *mut lean_object = core::ptr::null_mut(); 
v_res_622_ = l_List_forIn_x27_loop___at___00printEveryNth_spec__1(v_n_616_, v_as_617_, v_as_x27_618_, v_b_619_, v_a_620_);
lean_dec(v_as_x27_618_);
lean_dec(v_as_617_);
lean_dec(v_n_616_);
return v_res_622_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00printEveryNthSliceBased_spec__0___redArg(mut v_n_623_: *mut lean_object, mut v_a_624_: *mut lean_object, mut v_b_625_: *mut lean_object) -> *mut lean_object{
let mut v_array_627_: *mut lean_object = core::ptr::null_mut(); let mut v_start_628_: *mut lean_object = core::ptr::null_mut(); let mut v_stop_629_: *mut lean_object = core::ptr::null_mut(); let mut v___x_631_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_632_: u8 = 0; let mut v___x_633_: u8 = 0; let mut v___x_634_: *mut lean_object = core::ptr::null_mut(); let mut v___x_635_: *mut lean_object = core::ptr::null_mut(); let mut v_val_636_: *mut lean_object = core::ptr::null_mut(); let mut v___x_638_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_639_: u8 = 0; let mut v___x_640_: *mut lean_object = core::ptr::null_mut(); let mut v___x_641_: *mut lean_object = core::ptr::null_mut(); let mut v___x_643_: *mut lean_object = core::ptr::null_mut(); let mut v___x_644_: *mut lean_object = core::ptr::null_mut(); let mut v___x_646_: *mut lean_object = core::ptr::null_mut(); let mut v___x_647_: *mut lean_object = core::ptr::null_mut(); let mut v___x_648_: *mut lean_object = core::ptr::null_mut(); let mut v___x_649_: u8 = 0; let mut v___x_651_: *mut lean_object = core::ptr::null_mut(); let mut v___x_652_: *mut lean_object = core::ptr::null_mut(); let mut v___x_653_: *mut lean_object = core::ptr::null_mut(); let mut v___x_654_: *mut lean_object = core::ptr::null_mut(); let mut v___x_655_: *mut lean_object = core::ptr::null_mut(); let mut v___x_656_: *mut lean_object = core::ptr::null_mut(); let mut v___x_657_: *mut lean_object = core::ptr::null_mut(); let mut v___x_658_: *mut lean_object = core::ptr::null_mut(); let mut v___x_659_: *mut lean_object = core::ptr::null_mut(); let mut v_a_661_: *mut lean_object = core::ptr::null_mut(); let mut v___x_663_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_664_: u8 = 0; let mut v___x_666_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_667_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_668_: u8 = 0; let mut v_reuseFailAlloc_669_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_670_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_671_: u8 = 0; let mut v_isSharedCheck_672_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v_array_627_ = lean_ctor_get(v_a_624_, 0);
v_start_628_ = lean_ctor_get(v_a_624_, 1);
v_stop_629_ = lean_ctor_get(v_a_624_, 2);
v_isSharedCheck_672_ = (!lean_is_exclusive(v_a_624_)) as u8;
if v_isSharedCheck_672_ == 0 {
v___x_631_ = v_a_624_;
v_isShared_632_ = v_isSharedCheck_672_;
state = 1; continue;
} else {
lean_inc(v_stop_629_);
lean_inc(v_start_628_);
lean_inc(v_array_627_);
lean_dec(v_a_624_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_672_;
state = 1; continue;
}
}
1 => {
v___x_633_ = lean_nat_dec_lt(v_start_628_, v_stop_629_);
if v___x_633_ == 0 {
let mut v___x_634_: *mut lean_object = core::ptr::null_mut(); 
lean_del_object(v___x_631_);
lean_dec(v_stop_629_);
lean_dec(v_start_628_);
lean_dec_ref(v_array_627_);
v___x_634_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_634_, 0, v_b_625_);
return v___x_634_;
} else {
if lean_obj_tag(v_b_625_) == 0 {
let mut v___x_635_: *mut lean_object = core::ptr::null_mut(); 
lean_del_object(v___x_631_);
lean_dec(v_stop_629_);
lean_dec(v_start_628_);
lean_dec_ref(v_array_627_);
v___x_635_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_635_, 0, v_b_625_);
return v___x_635_;
} else {
let mut v_val_636_: *mut lean_object = core::ptr::null_mut(); let mut v___x_638_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_639_: u8 = 0; let mut v_isSharedCheck_671_: u8 = 0; 
v_val_636_ = lean_ctor_get(v_b_625_, 0);
v_isSharedCheck_671_ = (!lean_is_exclusive(v_b_625_)) as u8;
if v_isSharedCheck_671_ == 0 {
v___x_638_ = v_b_625_;
v_isShared_639_ = v_isSharedCheck_671_;
state = 2; continue;
} else {
lean_inc(v_val_636_);
lean_dec(v_b_625_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_671_;
state = 2; continue;
}
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00printEveryNthSliceBased_spec__0___redArg___boxed(mut v_n_673_: *mut lean_object, mut v_a_674_: *mut lean_object, mut v_b_675_: *mut lean_object, mut v___y_676_: *mut lean_object) -> *mut lean_object{
let mut v_res_677_: *mut lean_object = core::ptr::null_mut(); 
v_res_677_ = l_WellFounded_opaqueFix_u2083___at___00printEveryNthSliceBased_spec__0___redArg(v_n_673_, v_a_674_, v_b_675_);
lean_dec(v_n_673_);
return v_res_677_;
}
#[no_mangle] pub unsafe extern "C" fn l_printEveryNthSliceBased(mut v_xs_678_: *mut lean_object, mut v_n_679_: *mut lean_object) -> *mut lean_object{
let mut v___x_681_: *mut lean_object = core::ptr::null_mut(); let mut v___x_682_: *mut lean_object = core::ptr::null_mut(); let mut v___x_683_: *mut lean_object = core::ptr::null_mut(); let mut v___x_684_: *mut lean_object = core::ptr::null_mut(); let mut v___x_685_: *mut lean_object = core::ptr::null_mut(); let mut v___x_687_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_688_: u8 = 0; let mut v___x_689_: *mut lean_object = core::ptr::null_mut(); let mut v___x_691_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_692_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_693_: u8 = 0; let mut v_unused_694_: *mut lean_object = core::ptr::null_mut(); let mut v_a_695_: *mut lean_object = core::ptr::null_mut(); let mut v___x_697_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_698_: u8 = 0; let mut v___x_700_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_701_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_702_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_681_ = lean_unsigned_to_nat(0);
v___x_682_ = l_isolatedSteppedRange___closed__0;
v___x_683_ = lean_array_get_size(v_xs_678_);
v___x_684_ = l_Array_toSubarray___redArg(v_xs_678_, v___x_681_, v___x_683_);
v___x_685_ = l_WellFounded_opaqueFix_u2083___at___00printEveryNthSliceBased_spec__0___redArg(v_n_679_, v___x_684_, v___x_682_);
if lean_obj_tag(v___x_685_) == 0 {
let mut v___x_687_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_688_: u8 = 0; let mut v_isSharedCheck_693_: u8 = 0; 
v_isSharedCheck_693_ = (!lean_is_exclusive(v___x_685_)) as u8;
if v_isSharedCheck_693_ == 0 {
let mut v_unused_694_: *mut lean_object = core::ptr::null_mut(); 
v_unused_694_ = lean_ctor_get(v___x_685_, 0);
lean_dec(v_unused_694_);
v___x_687_ = v___x_685_;
v_isShared_688_ = v_isSharedCheck_693_;
state = 1; continue;
} else {
lean_dec(v___x_685_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_693_;
state = 1; continue;
}
} else {
let mut v_a_695_: *mut lean_object = core::ptr::null_mut(); let mut v___x_697_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_698_: u8 = 0; let mut v_isSharedCheck_702_: u8 = 0; 
v_a_695_ = lean_ctor_get(v___x_685_, 0);
v_isSharedCheck_702_ = (!lean_is_exclusive(v___x_685_)) as u8;
if v_isSharedCheck_702_ == 0 {
v___x_697_ = v___x_685_;
v_isShared_698_ = v_isSharedCheck_702_;
state = 3; continue;
} else {
lean_inc(v_a_695_);
lean_dec(v___x_685_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_702_;
state = 3; continue;
}
}
}
1 => {
v___x_689_ = lean_box(0);
if v_isShared_688_ == 0 {
lean_ctor_set(v___x_687_, 0, v___x_689_);
v___x_691_ = v___x_687_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_692_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v___x_689_);
v___x_691_ = v_reuseFailAlloc_692_;
state = 2; continue;
}
}
3 => {
if v_isShared_698_ == 0 {
v___x_700_ = v___x_697_;
state = 4; continue;
} else {
let mut v_reuseFailAlloc_701_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_701_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v_a_695_);
v___x_700_ = v_reuseFailAlloc_701_;
state = 4; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_printEveryNthSliceBased___boxed(mut v_xs_703_: *mut lean_object, mut v_n_704_: *mut lean_object, mut v_a_705_: *mut lean_object) -> *mut lean_object{
let mut v_res_706_: *mut lean_object = core::ptr::null_mut(); 
v_res_706_ = l_printEveryNthSliceBased(v_xs_703_, v_n_704_);
lean_dec(v_n_704_);
return v_res_706_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00printEveryNthSliceBased_spec__0(mut v_n_707_: *mut lean_object, mut v_inst_708_: *mut lean_object, mut v_R_709_: *mut lean_object, mut v_a_710_: *mut lean_object, mut v_b_711_: *mut lean_object, mut v_c_712_: *mut lean_object) -> *mut lean_object{
let mut v___x_714_: *mut lean_object = core::ptr::null_mut(); 
v___x_714_ = l_WellFounded_opaqueFix_u2083___at___00printEveryNthSliceBased_spec__0___redArg(v_n_707_, v_a_710_, v_b_711_);
return v___x_714_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00printEveryNthSliceBased_spec__0___boxed(mut v_n_715_: *mut lean_object, mut v_inst_716_: *mut lean_object, mut v_R_717_: *mut lean_object, mut v_a_718_: *mut lean_object, mut v_b_719_: *mut lean_object, mut v_c_720_: *mut lean_object, mut v___y_721_: *mut lean_object) -> *mut lean_object{
let mut v_res_722_: *mut lean_object = core::ptr::null_mut(); 
v_res_722_ = l_WellFounded_opaqueFix_u2083___at___00printEveryNthSliceBased_spec__0(v_n_715_, v_inst_716_, v_R_717_, v_a_718_, v_b_719_, v_c_720_);
lean_dec(v_n_715_);
return v_res_722_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00longChainOfCombinators_spec__0___redArg(mut v_a_723_: *mut lean_object, mut v_b_724_: *mut lean_object) -> *mut lean_object{
let mut v_countdown_725_: *mut lean_object = core::ptr::null_mut(); let mut v_inner_726_: *mut lean_object = core::ptr::null_mut(); let mut v___x_728_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_729_: u8 = 0; let mut v_it_731_: *mut lean_object = core::ptr::null_mut(); let mut v___x_733_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_735_: *mut lean_object = core::ptr::null_mut(); let mut v___x_736_: *mut lean_object = core::ptr::null_mut(); let mut v___x_737_: u8 = 0; let mut v_remaining_738_: *mut lean_object = core::ptr::null_mut(); let mut v_inner_739_: *mut lean_object = core::ptr::null_mut(); let mut v___x_741_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_742_: u8 = 0; let mut v_it_744_: *mut lean_object = core::ptr::null_mut(); let mut v___x_746_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_747_: *mut lean_object = core::ptr::null_mut(); let mut v_memoizedLeft_748_: *mut lean_object = core::ptr::null_mut(); let mut v_left_749_: *mut lean_object = core::ptr::null_mut(); let mut v_right_750_: *mut lean_object = core::ptr::null_mut(); let mut v___x_752_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_753_: u8 = 0; let mut v_array_754_: *mut lean_object = core::ptr::null_mut(); let mut v_pos_755_: *mut lean_object = core::ptr::null_mut(); let mut v___x_757_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_758_: u8 = 0; let mut v___x_759_: *mut lean_object = core::ptr::null_mut(); let mut v___x_760_: u8 = 0; let mut v___x_761_: *mut lean_object = core::ptr::null_mut(); let mut v___x_763_: *mut lean_object = core::ptr::null_mut(); let mut v___x_764_: *mut lean_object = core::ptr::null_mut(); let mut v___x_765_: *mut lean_object = core::ptr::null_mut(); let mut v___x_767_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_768_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_769_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_770_: u8 = 0; let mut v_isSharedCheck_771_: u8 = 0; let mut v_unused_772_: *mut lean_object = core::ptr::null_mut(); let mut v_right_773_: *mut lean_object = core::ptr::null_mut(); let mut v_left_774_: *mut lean_object = core::ptr::null_mut(); let mut v___x_776_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_777_: u8 = 0; let mut v_val_778_: *mut lean_object = core::ptr::null_mut(); let mut v___x_780_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_781_: u8 = 0; let mut v___x_782_: *mut lean_object = core::ptr::null_mut(); let mut v___x_784_: *mut lean_object = core::ptr::null_mut(); let mut v___x_785_: *mut lean_object = core::ptr::null_mut(); let mut v___x_787_: *mut lean_object = core::ptr::null_mut(); let mut v___x_788_: *mut lean_object = core::ptr::null_mut(); let mut v___x_789_: *mut lean_object = core::ptr::null_mut(); let mut v___x_790_: *mut lean_object = core::ptr::null_mut(); let mut v___x_791_: u8 = 0; let mut v_isZero_792_: u8 = 0; let mut v___x_793_: *mut lean_object = core::ptr::null_mut(); let mut v___x_794_: u8 = 0; let mut v___x_795_: *mut lean_object = core::ptr::null_mut(); let mut v___x_796_: *mut lean_object = core::ptr::null_mut(); let mut v___x_797_: *mut lean_object = core::ptr::null_mut(); let mut v___x_798_: *mut lean_object = core::ptr::null_mut(); let mut v_n_800_: *mut lean_object = core::ptr::null_mut(); let mut v___x_801_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_802_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_803_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_804_: u8 = 0; let mut v_isSharedCheck_805_: u8 = 0; let mut v_unused_806_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_807_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_808_: u8 = 0; let mut v_isSharedCheck_809_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v_countdown_725_ = lean_ctor_get(v_a_723_, 0);
v_inner_726_ = lean_ctor_get(v_a_723_, 1);
v_isSharedCheck_809_ = (!lean_is_exclusive(v_a_723_)) as u8;
if v_isSharedCheck_809_ == 0 {
v___x_728_ = v_a_723_;
v_isShared_729_ = v_isSharedCheck_809_;
state = 1; continue;
} else {
lean_inc(v_inner_726_);
lean_inc(v_countdown_725_);
lean_dec(v_a_723_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_809_;
state = 1; continue;
}
}
1 => {
v___x_736_ = lean_unsigned_to_nat(1);
v___x_737_ = lean_nat_dec_eq(v_countdown_725_, v___x_736_);
if v___x_737_ == 0 {
let mut v_remaining_738_: *mut lean_object = core::ptr::null_mut(); let mut v_inner_739_: *mut lean_object = core::ptr::null_mut(); let mut v___x_741_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_742_: u8 = 0; let mut v_isSharedCheck_808_: u8 = 0; 
v_remaining_738_ = lean_ctor_get(v_inner_726_, 0);
v_inner_739_ = lean_ctor_get(v_inner_726_, 1);
v_isSharedCheck_808_ = (!lean_is_exclusive(v_inner_726_)) as u8;
if v_isSharedCheck_808_ == 0 {
v___x_741_ = v_inner_726_;
v_isShared_742_ = v_isSharedCheck_808_;
state = 4; continue;
} else {
lean_inc(v_inner_739_);
lean_inc(v_remaining_738_);
lean_dec(v_inner_726_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_808_;
state = 4; continue;
}
} else {
lean_del_object(v___x_728_);
lean_dec(v_inner_726_);
lean_dec(v_countdown_725_);
return v_b_724_;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_longChainOfCombinators(mut v_xs_812_: *mut lean_object) -> *mut lean_object{
let mut v___x_813_: *mut lean_object = core::ptr::null_mut(); let mut v___x_814_: *mut lean_object = core::ptr::null_mut(); let mut v___x_815_: *mut lean_object = core::ptr::null_mut(); let mut v___x_816_: *mut lean_object = core::ptr::null_mut(); let mut v___x_817_: *mut lean_object = core::ptr::null_mut(); let mut v___x_818_: *mut lean_object = core::ptr::null_mut(); let mut v___x_819_: *mut lean_object = core::ptr::null_mut(); let mut v___x_820_: *mut lean_object = core::ptr::null_mut(); let mut v___x_821_: *mut lean_object = core::ptr::null_mut(); let mut v___x_822_: *mut lean_object = core::ptr::null_mut(); 
v___x_813_ = lean_unsigned_to_nat(0);
v___x_814_ = lean_unsigned_to_nat(1);
v___x_815_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_815_, 0, v_xs_812_);
lean_ctor_set(v___x_815_, 1, v___x_813_);
v___x_816_ = l_longChainOfCombinators___closed__0;
v___x_817_ = lean_box(0);
v___x_818_ = lean_alloc_ctor(0, 3, (0) as u32);
lean_ctor_set(v___x_818_, 0, v___x_815_);
lean_ctor_set(v___x_818_, 1, v___x_817_);
lean_ctor_set(v___x_818_, 2, v___x_816_);
v___x_819_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_819_, 0, v___x_814_);
lean_ctor_set(v___x_819_, 1, v___x_818_);
v___x_820_ = lean_unsigned_to_nat(10000001);
v___x_821_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_821_, 0, v___x_820_);
lean_ctor_set(v___x_821_, 1, v___x_819_);
v___x_822_ = l_WellFounded_opaqueFix_u2083___at___00longChainOfCombinators_spec__0___redArg(v___x_821_, v___x_813_);
return v___x_822_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00longChainOfCombinators_spec__0(mut v_inst_823_: *mut lean_object, mut v_R_824_: *mut lean_object, mut v_a_825_: *mut lean_object, mut v_b_826_: *mut lean_object, mut v_c_827_: *mut lean_object) -> *mut lean_object{
let mut v___x_828_: *mut lean_object = core::ptr::null_mut(); 
v___x_828_ = l_WellFounded_opaqueFix_u2083___at___00longChainOfCombinators_spec__0___redArg(v_a_825_, v_b_826_);
return v___x_828_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00xs_spec__0___redArg(mut v_a_829_: *mut lean_object, mut v_b_830_: *mut lean_object) -> *mut lean_object{
let mut v_next_831_: *mut lean_object = core::ptr::null_mut(); let mut v_upperBound_832_: *mut lean_object = core::ptr::null_mut(); let mut v___x_834_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_835_: u8 = 0; let mut v_val_836_: *mut lean_object = core::ptr::null_mut(); let mut v___x_838_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_839_: u8 = 0; let mut v___x_840_: u8 = 0; let mut v___x_841_: *mut lean_object = core::ptr::null_mut(); let mut v___x_842_: *mut lean_object = core::ptr::null_mut(); let mut v___x_844_: *mut lean_object = core::ptr::null_mut(); let mut v___x_846_: *mut lean_object = core::ptr::null_mut(); let mut v___x_847_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_849_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_850_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_851_: u8 = 0; let mut v_isSharedCheck_852_: u8 = 0; let mut v_unused_853_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v_next_831_ = lean_ctor_get(v_a_829_, 0);
lean_inc(v_next_831_);
if lean_obj_tag(v_next_831_) == 0 {
lean_dec_ref(v_a_829_);
return v_b_830_;
} else {
let mut v_upperBound_832_: *mut lean_object = core::ptr::null_mut(); let mut v___x_834_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_835_: u8 = 0; let mut v_isSharedCheck_852_: u8 = 0; 
v_upperBound_832_ = lean_ctor_get(v_a_829_, 1);
v_isSharedCheck_852_ = (!lean_is_exclusive(v_a_829_)) as u8;
if v_isSharedCheck_852_ == 0 {
let mut v_unused_853_: *mut lean_object = core::ptr::null_mut(); 
v_unused_853_ = lean_ctor_get(v_a_829_, 0);
lean_dec(v_unused_853_);
v___x_834_ = v_a_829_;
v_isShared_835_ = v_isSharedCheck_852_;
state = 1; continue;
} else {
lean_inc(v_upperBound_832_);
lean_dec(v_a_829_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_852_;
state = 1; continue;
}
}
}
1 => {
v_val_836_ = lean_ctor_get(v_next_831_, 0);
v_isSharedCheck_851_ = (!lean_is_exclusive(v_next_831_)) as u8;
if v_isSharedCheck_851_ == 0 {
v___x_838_ = v_next_831_;
v_isShared_839_ = v_isSharedCheck_851_;
state = 2; continue;
} else {
lean_inc(v_val_836_);
lean_dec(v_next_831_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_851_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn _init_l_xs___closed__1() -> *mut lean_object{
let mut v___x_857_: *mut lean_object = core::ptr::null_mut(); let mut v___x_858_: *mut lean_object = core::ptr::null_mut(); let mut v___x_859_: *mut lean_object = core::ptr::null_mut(); 
v___x_857_ = l_primes___closed__0;
v___x_858_ = l_xs___closed__0;
v___x_859_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00xs_spec__0___redArg(v___x_858_, v___x_857_);
return v___x_859_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_xs() -> *mut lean_object{
let mut v___x_860_: *mut lean_object = core::ptr::null_mut(); 
v___x_860_ = lean_obj_once(core::ptr::addr_of_mut!(l_xs___closed__1), core::ptr::addr_of_mut!(l_xs___closed__1_once), _init_l_xs___closed__1);
return v___x_860_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00xs_spec__0(mut v_inst_861_: *mut lean_object, mut v_R_862_: *mut lean_object, mut v_a_863_: *mut lean_object, mut v_b_864_: *mut lean_object) -> *mut lean_object{
let mut v___x_865_: *mut lean_object = core::ptr::null_mut(); 
v___x_865_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00xs_spec__0___redArg(v_a_863_, v_b_864_);
return v___x_865_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_l___closed__0() -> *mut lean_object{
let mut v___x_866_: *mut lean_object = core::ptr::null_mut(); let mut v___x_867_: *mut lean_object = core::ptr::null_mut(); 
v___x_866_ = lean_obj_once(core::ptr::addr_of_mut!(l_xs___closed__1), core::ptr::addr_of_mut!(l_xs___closed__1_once), _init_l_xs___closed__1);
v___x_867_ = lean_array_to_list(v___x_866_);
return v___x_867_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_l() -> *mut lean_object{
let mut v___x_868_: *mut lean_object = core::ptr::null_mut(); 
v___x_868_ = lean_obj_once(core::ptr::addr_of_mut!(l_l___closed__0), core::ptr::addr_of_mut!(l_l___closed__0_once), _init_l_l___closed__0);
return v___x_868_;
}
#[no_mangle] pub unsafe extern "C" fn l_run_x27___redArg(mut v_f_869_: *mut lean_object) -> *mut lean_object{
let mut v___x_871_: *mut lean_object = core::ptr::null_mut(); let mut v___x_872_: *mut lean_object = core::ptr::null_mut(); let mut v___x_873_: *mut lean_object = core::ptr::null_mut(); 
v___x_871_ = lean_box(0);
v___x_872_ = lean_apply_1(v_f_869_, v___x_871_);
v___x_873_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_873_, 0, v___x_872_);
return v___x_873_;
}
#[no_mangle] pub unsafe extern "C" fn l_run_x27___redArg___boxed(mut v_f_874_: *mut lean_object, mut v_a_875_: *mut lean_object) -> *mut lean_object{
let mut v_res_876_: *mut lean_object = core::ptr::null_mut(); 
v_res_876_ = l_run_x27___redArg(v_f_874_);
return v_res_876_;
}
#[no_mangle] pub unsafe extern "C" fn l_run_x27(mut v_00_u03b1_877_: *mut lean_object, mut v_f_878_: *mut lean_object) -> *mut lean_object{
let mut v___x_880_: *mut lean_object = core::ptr::null_mut(); 
v___x_880_ = l_run_x27___redArg(v_f_878_);
return v___x_880_;
}
#[no_mangle] pub unsafe extern "C" fn l_run_x27___boxed(mut v_00_u03b1_881_: *mut lean_object, mut v_f_882_: *mut lean_object, mut v_a_883_: *mut lean_object) -> *mut lean_object{
let mut v_res_884_: *mut lean_object = core::ptr::null_mut(); 
v_res_884_ = l_run_x27(v_00_u03b1_881_, v_f_882_);
return v_res_884_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l___aux__iterators______macroRules__termRun____1___closed__13() -> *mut lean_object{
let mut v___x_932_: *mut lean_object = core::ptr::null_mut(); let mut v___x_933_: *mut lean_object = core::ptr::null_mut(); 
v___x_932_ = l___aux__iterators______macroRules__termRun____1___closed__12;
v___x_933_ = l_String_toRawSubstring_x27(v___x_932_);
return v___x_933_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l___aux__iterators______macroRules__termRun____1___closed__25() -> *mut lean_object{
let mut v___x_961_: *mut lean_object = core::ptr::null_mut(); 
v___x_961_ = l_Array_mkArray0(lean_box(0));
return v___x_961_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l___aux__iterators______macroRules__termRun____1___closed__34() -> *mut lean_object{
let mut v___x_978_: *mut lean_object = core::ptr::null_mut(); let mut v___x_979_: *mut lean_object = core::ptr::null_mut(); 
v___x_978_ = l___aux__iterators______macroRules__termRun____1___closed__33;
v___x_979_ = l_String_toRawSubstring_x27(v___x_978_);
return v___x_979_;
}
#[no_mangle] pub unsafe extern "C" fn l___aux__iterators______macroRules__termRun____1(mut v_x_988_: *mut lean_object, mut v_a_989_: *mut lean_object, mut v_a_990_: *mut lean_object) -> *mut lean_object{
let mut v___x_991_: *mut lean_object = core::ptr::null_mut(); let mut v___x_992_: u8 = 0; 
v___x_991_ = l_termRun___00__closed__1;
lean_inc(v_x_988_);
v___x_992_ = l_Lean_Syntax_isOfKind(v_x_988_, v___x_991_);
if v___x_992_ == 0 {
let mut v___x_993_: *mut lean_object = core::ptr::null_mut(); let mut v___x_994_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_x_988_);
v___x_993_ = lean_box(1);
v___x_994_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_994_, 0, v___x_993_);
lean_ctor_set(v___x_994_, 1, v_a_990_);
return v___x_994_;
} else {
let mut v_quotContext_995_: *mut lean_object = core::ptr::null_mut(); let mut v_currMacroScope_996_: *mut lean_object = core::ptr::null_mut(); let mut v_ref_997_: *mut lean_object = core::ptr::null_mut(); let mut v___x_998_: *mut lean_object = core::ptr::null_mut(); let mut v___x_999_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1000_: u8 = 0; let mut v___x_1001_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1002_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1003_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1004_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1005_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1006_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1007_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1008_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1009_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1010_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1011_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1012_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1013_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1014_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1015_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1016_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1017_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1018_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1019_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1020_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1021_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1022_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1023_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1024_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1025_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1026_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1027_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1028_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1029_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1030_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1031_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1032_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1033_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1034_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1035_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1036_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1037_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1038_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1039_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1040_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1041_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1042_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1043_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1044_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1045_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1046_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1047_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1048_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1049_: *mut lean_object = core::ptr::null_mut(); 
v_quotContext_995_ = lean_ctor_get(v_a_989_, 1);
v_currMacroScope_996_ = lean_ctor_get(v_a_989_, 2);
v_ref_997_ = lean_ctor_get(v_a_989_, 5);
v___x_998_ = lean_unsigned_to_nat(1);
v___x_999_ = l_Lean_Syntax_getArg(v_x_988_, v___x_998_);
lean_dec(v_x_988_);
v___x_1000_ = 0;
v___x_1001_ = l_Lean_SourceInfo_fromRef(v_ref_997_, v___x_1000_);
v___x_1002_ = l___aux__iterators______macroRules__termRun____1___closed__1;
v___x_1003_ = l___aux__iterators______macroRules__termRun____1___closed__6;
v___x_1004_ = l___aux__iterators______macroRules__termRun____1___closed__8;
v___x_1005_ = l___aux__iterators______macroRules__termRun____1___closed__9;
lean_inc_n(v___x_1001_, 21);
v___x_1006_ = lean_alloc_ctor(2, 2, (0) as u32);
lean_ctor_set(v___x_1006_, 0, v___x_1001_);
lean_ctor_set(v___x_1006_, 1, v___x_1005_);
v___x_1007_ = l___aux__iterators______macroRules__termRun____1___closed__11;
v___x_1008_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__iterators______macroRules__termRun____1___closed__13), core::ptr::addr_of_mut!(l___aux__iterators______macroRules__termRun____1___closed__13_once), _init_l___aux__iterators______macroRules__termRun____1___closed__13);
v___x_1009_ = lean_box(0);
lean_inc_n(v_currMacroScope_996_, 2);
lean_inc_n(v_quotContext_995_, 2);
v___x_1010_ = l_Lean_addMacroScope(v_quotContext_995_, v___x_1009_, v_currMacroScope_996_);
v___x_1011_ = l___aux__iterators______macroRules__termRun____1___closed__15;
v___x_1012_ = lean_alloc_ctor(3, 4, (0) as u32);
lean_ctor_set(v___x_1012_, 0, v___x_1001_);
lean_ctor_set(v___x_1012_, 1, v___x_1008_);
lean_ctor_set(v___x_1012_, 2, v___x_1010_);
lean_ctor_set(v___x_1012_, 3, v___x_1011_);
v___x_1013_ = l_Lean_Syntax_node1(v___x_1001_, v___x_1007_, v___x_1012_);
v___x_1014_ = l_Lean_Syntax_node2(v___x_1001_, v___x_1004_, v___x_1006_, v___x_1013_);
v___x_1015_ = l___aux__iterators______macroRules__termRun____1___closed__16;
v___x_1016_ = l___aux__iterators______macroRules__termRun____1___closed__17;
v___x_1017_ = lean_alloc_ctor(2, 2, (0) as u32);
lean_ctor_set(v___x_1017_, 0, v___x_1001_);
lean_ctor_set(v___x_1017_, 1, v___x_1015_);
v___x_1018_ = l___aux__iterators______macroRules__termRun____1___closed__19;
v___x_1019_ = l___aux__iterators______macroRules__termRun____1___closed__21;
v___x_1020_ = l___aux__iterators______macroRules__termRun____1___closed__23;
v___x_1021_ = l___aux__iterators______macroRules__termRun____1___closed__24;
v___x_1022_ = lean_alloc_ctor(2, 2, (0) as u32);
lean_ctor_set(v___x_1022_, 0, v___x_1001_);
lean_ctor_set(v___x_1022_, 1, v___x_1021_);
v___x_1023_ = l_Lean_Syntax_node1(v___x_1001_, v___x_1020_, v___x_1022_);
v___x_1024_ = l_Lean_Syntax_node1(v___x_1001_, v___x_1019_, v___x_1023_);
v___x_1025_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__iterators______macroRules__termRun____1___closed__25), core::ptr::addr_of_mut!(l___aux__iterators______macroRules__termRun____1___closed__25_once), _init_l___aux__iterators______macroRules__termRun____1___closed__25);
v___x_1026_ = lean_alloc_ctor(1, 3, (0) as u32);
lean_ctor_set(v___x_1026_, 0, v___x_1001_);
lean_ctor_set(v___x_1026_, 1, v___x_1019_);
lean_ctor_set(v___x_1026_, 2, v___x_1025_);
v___x_1027_ = l___aux__iterators______macroRules__termRun____1___closed__26;
v___x_1028_ = lean_alloc_ctor(2, 2, (0) as u32);
lean_ctor_set(v___x_1028_, 0, v___x_1001_);
lean_ctor_set(v___x_1028_, 1, v___x_1027_);
v___x_1029_ = l___aux__iterators______macroRules__termRun____1___closed__28;
v___x_1030_ = l___aux__iterators______macroRules__termRun____1___closed__29;
v___x_1031_ = lean_alloc_ctor(2, 2, (0) as u32);
lean_ctor_set(v___x_1031_, 0, v___x_1001_);
lean_ctor_set(v___x_1031_, 1, v___x_1030_);
lean_inc_ref(v___x_1031_);
lean_inc_ref_n(v___x_1026_, 2);
lean_inc(v___x_1014_);
v___x_1032_ = l_Lean_Syntax_node3(v___x_1001_, v___x_1029_, v___x_1014_, v___x_1026_, v___x_1031_);
lean_inc_ref(v___x_1028_);
lean_inc(v___x_1024_);
v___x_1033_ = l_Lean_Syntax_node4(v___x_1001_, v___x_1018_, v___x_1024_, v___x_1026_, v___x_1028_, v___x_1032_);
lean_inc_ref(v___x_1017_);
v___x_1034_ = l_Lean_Syntax_node2(v___x_1001_, v___x_1016_, v___x_1017_, v___x_1033_);
v___x_1035_ = l_Lean_Syntax_node3(v___x_1001_, v___x_1003_, v___x_1014_, v___x_1034_, v___x_1031_);
v___x_1036_ = l___aux__iterators______macroRules__termRun____1___closed__30;
v___x_1037_ = lean_alloc_ctor(2, 2, (0) as u32);
lean_ctor_set(v___x_1037_, 0, v___x_1001_);
lean_ctor_set(v___x_1037_, 1, v___x_1036_);
v___x_1038_ = l___aux__iterators______macroRules__termRun____1___closed__32;
v___x_1039_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__iterators______macroRules__termRun____1___closed__34), core::ptr::addr_of_mut!(l___aux__iterators______macroRules__termRun____1___closed__34_once), _init_l___aux__iterators______macroRules__termRun____1___closed__34);
v___x_1040_ = l___aux__iterators______macroRules__termRun____1___closed__35;
v___x_1041_ = l_Lean_addMacroScope(v_quotContext_995_, v___x_1040_, v_currMacroScope_996_);
v___x_1042_ = l___aux__iterators______macroRules__termRun____1___closed__37;
v___x_1043_ = lean_alloc_ctor(3, 4, (0) as u32);
lean_ctor_set(v___x_1043_, 0, v___x_1001_);
lean_ctor_set(v___x_1043_, 1, v___x_1039_);
lean_ctor_set(v___x_1043_, 2, v___x_1041_);
lean_ctor_set(v___x_1043_, 3, v___x_1042_);
v___x_1044_ = l_Lean_Syntax_node4(v___x_1001_, v___x_1018_, v___x_1024_, v___x_1026_, v___x_1028_, v___x_999_);
v___x_1045_ = l_Lean_Syntax_node2(v___x_1001_, v___x_1016_, v___x_1017_, v___x_1044_);
v___x_1046_ = l_Lean_Syntax_node1(v___x_1001_, v___x_1019_, v___x_1045_);
v___x_1047_ = l_Lean_Syntax_node2(v___x_1001_, v___x_1038_, v___x_1043_, v___x_1046_);
v___x_1048_ = l_Lean_Syntax_node3(v___x_1001_, v___x_1002_, v___x_1035_, v___x_1037_, v___x_1047_);
v___x_1049_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_1049_, 0, v___x_1048_);
lean_ctor_set(v___x_1049_, 1, v_a_990_);
return v___x_1049_;
}
}
#[no_mangle] pub unsafe extern "C" fn l___aux__iterators______macroRules__termRun____1___boxed(mut v_x_1050_: *mut lean_object, mut v_a_1051_: *mut lean_object, mut v_a_1052_: *mut lean_object) -> *mut lean_object{
let mut v_res_1053_: *mut lean_object = core::ptr::null_mut(); 
v_res_1053_ = l___aux__iterators______macroRules__termRun____1(v_x_1050_, v_a_1051_, v_a_1052_);
lean_dec_ref(v_a_1051_);
return v_res_1053_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___lam__0___closed__0() -> *mut lean_object{
let mut v___x_1054_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1055_: *mut lean_object = core::ptr::null_mut(); 
v___x_1054_ = l_xs;
v___x_1055_ = l_sum_u2081(v___x_1054_);
return v___x_1055_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___lam__0(mut v_x_1056_: *mut lean_object) -> *mut lean_object{
let mut v___x_1057_: *mut lean_object = core::ptr::null_mut(); 
v___x_1057_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___lam__0___closed__0), core::ptr::addr_of_mut!(l_main___lam__0___closed__0_once), _init_l_main___lam__0___closed__0);
return v___x_1057_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___lam__1___closed__0() -> *mut lean_object{
let mut v___x_1058_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1059_: *mut lean_object = core::ptr::null_mut(); 
v___x_1058_ = l_xs;
v___x_1059_ = l_sum_u2082(v___x_1058_);
return v___x_1059_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___lam__1(mut v_x_1060_: *mut lean_object) -> *mut lean_object{
let mut v___x_1061_: *mut lean_object = core::ptr::null_mut(); 
v___x_1061_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___lam__1___closed__0), core::ptr::addr_of_mut!(l_main___lam__1___closed__0_once), _init_l_main___lam__1___closed__0);
return v___x_1061_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___lam__2___closed__0() -> *mut lean_object{
let mut v___x_1062_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1063_: *mut lean_object = core::ptr::null_mut(); 
v___x_1062_ = l_xs;
v___x_1063_ = l_isolatedMap(v___x_1062_);
return v___x_1063_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___lam__2(mut v_x_1064_: *mut lean_object) -> *mut lean_object{
let mut v___x_1065_: *mut lean_object = core::ptr::null_mut(); 
v___x_1065_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___lam__2___closed__0), core::ptr::addr_of_mut!(l_main___lam__2___closed__0_once), _init_l_main___lam__2___closed__0);
return v___x_1065_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___lam__3___closed__0() -> *mut lean_object{
let mut v___x_1066_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1067_: *mut lean_object = core::ptr::null_mut(); 
v___x_1066_ = l_xs;
v___x_1067_ = l_isolatedFilterMap(v___x_1066_);
return v___x_1067_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___lam__3(mut v_x_1068_: *mut lean_object) -> *mut lean_object{
let mut v___x_1069_: *mut lean_object = core::ptr::null_mut(); 
v___x_1069_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___lam__3___closed__0), core::ptr::addr_of_mut!(l_main___lam__3___closed__0_once), _init_l_main___lam__3___closed__0);
return v___x_1069_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___lam__4___closed__0() -> *mut lean_object{
let mut v___x_1070_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1071_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1072_: *mut lean_object = core::ptr::null_mut(); 
v___x_1070_ = lean_unsigned_to_nat(1000000);
v___x_1071_ = l_xs;
v___x_1072_ = l_isolatedTake(v___x_1071_, v___x_1070_);
return v___x_1072_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___lam__4(mut v_x_1073_: *mut lean_object) -> *mut lean_object{
let mut v___x_1074_: *mut lean_object = core::ptr::null_mut(); 
v___x_1074_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___lam__4___closed__0), core::ptr::addr_of_mut!(l_main___lam__4___closed__0_once), _init_l_main___lam__4___closed__0);
return v___x_1074_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___lam__5___closed__0() -> *mut lean_object{
let mut v___x_1075_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1076_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1077_: *mut lean_object = core::ptr::null_mut(); 
v___x_1075_ = lean_unsigned_to_nat(1000000);
v___x_1076_ = l_xs;
v___x_1077_ = l_isolatedDrop(v___x_1076_, v___x_1075_);
return v___x_1077_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___lam__5(mut v_x_1078_: *mut lean_object) -> *mut lean_object{
let mut v___x_1079_: *mut lean_object = core::ptr::null_mut(); 
v___x_1079_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___lam__5___closed__0), core::ptr::addr_of_mut!(l_main___lam__5___closed__0_once), _init_l_main___lam__5___closed__0);
return v___x_1079_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___lam__6___closed__0() -> *mut lean_object{
let mut v___x_1080_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1081_: *mut lean_object = core::ptr::null_mut(); 
v___x_1080_ = l_xs;
v___x_1081_ = l_isolatedTakeWhile(v___x_1080_);
return v___x_1081_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___lam__6(mut v_x_1082_: *mut lean_object) -> *mut lean_object{
let mut v___x_1083_: *mut lean_object = core::ptr::null_mut(); 
v___x_1083_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___lam__6___closed__0), core::ptr::addr_of_mut!(l_main___lam__6___closed__0_once), _init_l_main___lam__6___closed__0);
return v___x_1083_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___lam__7___closed__0() -> *mut lean_object{
let mut v___x_1084_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1085_: *mut lean_object = core::ptr::null_mut(); 
v___x_1084_ = l_xs;
v___x_1085_ = l_isolatedDropWhile(v___x_1084_);
return v___x_1085_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___lam__7(mut v_x_1086_: *mut lean_object) -> *mut lean_object{
let mut v___x_1087_: *mut lean_object = core::ptr::null_mut(); 
v___x_1087_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___lam__7___closed__0), core::ptr::addr_of_mut!(l_main___lam__7___closed__0_once), _init_l_main___lam__7___closed__0);
return v___x_1087_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___lam__8___closed__0() -> *mut lean_object{
let mut v___x_1088_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1089_: *mut lean_object = core::ptr::null_mut(); 
v___x_1088_ = l_xs;
v___x_1089_ = l_isolatedZip(v___x_1088_, v___x_1088_);
return v___x_1089_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___lam__8(mut v_x_1090_: *mut lean_object) -> *mut lean_object{
let mut v___x_1091_: *mut lean_object = core::ptr::null_mut(); 
v___x_1091_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___lam__8___closed__0), core::ptr::addr_of_mut!(l_main___lam__8___closed__0_once), _init_l_main___lam__8___closed__0);
return v___x_1091_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___lam__9___closed__0() -> *mut lean_object{
let mut v___x_1092_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1093_: *mut lean_object = core::ptr::null_mut(); 
v___x_1092_ = lean_unsigned_to_nat(1000000);
v___x_1093_ = l_isolatedSteppedRange(v___x_1092_);
return v___x_1093_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___lam__9(mut v_x_1094_: *mut lean_object) -> *mut lean_object{
let mut v___x_1095_: *mut lean_object = core::ptr::null_mut(); 
v___x_1095_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___lam__9___closed__0), core::ptr::addr_of_mut!(l_main___lam__9___closed__0_once), _init_l_main___lam__9___closed__0);
return v___x_1095_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___lam__10___closed__0() -> *mut lean_object{
let mut v___x_1096_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1097_: *mut lean_object = core::ptr::null_mut(); 
v___x_1096_ = l_xs;
v___x_1097_ = l_longChainOfCombinators(v___x_1096_);
return v___x_1097_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___lam__10(mut v_x_1098_: *mut lean_object) -> *mut lean_object{
let mut v___x_1099_: *mut lean_object = core::ptr::null_mut(); 
v___x_1099_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___lam__10___closed__0), core::ptr::addr_of_mut!(l_main___lam__10___closed__0_once), _init_l_main___lam__10___closed__0);
return v___x_1099_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00main_spec__0___redArg(mut v_upperBound_1100_: *mut lean_object, mut v_a_1101_: *mut lean_object, mut v_b_1102_: *mut lean_object) -> *mut lean_object{
let mut v___x_1103_: u8 = 0; let mut v___x_1104_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1105_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1106_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_1103_ = lean_nat_dec_lt(v_a_1101_, v_upperBound_1100_);
if v___x_1103_ == 0 {
lean_dec(v_a_1101_);
return v_b_1102_;
} else {
let mut v___x_1104_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1105_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1106_: *mut lean_object = core::ptr::null_mut(); 
v___x_1104_ = lean_nat_add(v_b_1102_, v_a_1101_);
lean_dec(v_b_1102_);
v___x_1105_ = lean_unsigned_to_nat(1);
v___x_1106_ = lean_nat_add(v_a_1101_, v___x_1105_);
lean_dec(v_a_1101_);
v_a_1101_ = v___x_1106_;
v_b_1102_ = v___x_1104_;
state = 0; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00main_spec__0___redArg___boxed(mut v_upperBound_1108_: *mut lean_object, mut v_a_1109_: *mut lean_object, mut v_b_1110_: *mut lean_object) -> *mut lean_object{
let mut v_res_1111_: *mut lean_object = core::ptr::null_mut(); 
v_res_1111_ = l_WellFounded_opaqueFix_u2083___at___00main_spec__0___redArg(v_upperBound_1108_, v_a_1109_, v_b_1110_);
lean_dec(v_upperBound_1108_);
return v_res_1111_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___lam__11___closed__0() -> *mut lean_object{
let mut v___x_1112_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1113_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1114_: *mut lean_object = core::ptr::null_mut(); 
v___x_1112_ = lean_unsigned_to_nat(0);
v___x_1113_ = lean_unsigned_to_nat(1000000);
v___x_1114_ = l_WellFounded_opaqueFix_u2083___at___00main_spec__0___redArg(v___x_1113_, v___x_1112_, v___x_1112_);
return v___x_1114_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___lam__11(mut v_x_1115_: *mut lean_object) -> *mut lean_object{
let mut v___x_1116_: *mut lean_object = core::ptr::null_mut(); 
v___x_1116_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___lam__11___closed__0), core::ptr::addr_of_mut!(l_main___lam__11___closed__0_once), _init_l_main___lam__11___closed__0);
return v___x_1116_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___lam__12___closed__0() -> *mut lean_object{
let mut v___x_1117_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1118_: *mut lean_object = core::ptr::null_mut(); 
v___x_1117_ = lean_unsigned_to_nat(3000);
v___x_1118_ = l_primes(v___x_1117_);
return v___x_1118_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___lam__12(mut v_x_1119_: *mut lean_object) -> *mut lean_object{
let mut v___x_1120_: *mut lean_object = core::ptr::null_mut(); 
v___x_1120_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___lam__12___closed__0), core::ptr::addr_of_mut!(l_main___lam__12___closed__0_once), _init_l_main___lam__12___closed__0);
return v___x_1120_;
}
#[no_mangle] pub unsafe extern "C" fn _lean_main() -> *mut lean_object{
let mut v___f_1135_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1136_: *mut lean_object = core::ptr::null_mut(); let mut v___f_1137_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1138_: *mut lean_object = core::ptr::null_mut(); let mut v___f_1139_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1140_: *mut lean_object = core::ptr::null_mut(); let mut v___f_1141_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1142_: *mut lean_object = core::ptr::null_mut(); let mut v___f_1143_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1144_: *mut lean_object = core::ptr::null_mut(); let mut v___f_1145_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1146_: *mut lean_object = core::ptr::null_mut(); let mut v___f_1147_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1148_: *mut lean_object = core::ptr::null_mut(); let mut v___f_1149_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1150_: *mut lean_object = core::ptr::null_mut(); let mut v___f_1151_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1152_: *mut lean_object = core::ptr::null_mut(); let mut v___f_1153_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1154_: *mut lean_object = core::ptr::null_mut(); let mut v___f_1155_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1156_: *mut lean_object = core::ptr::null_mut(); let mut v___f_1157_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1158_: *mut lean_object = core::ptr::null_mut(); let mut v___f_1159_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1160_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1161_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1162_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1163_: *mut lean_object = core::ptr::null_mut(); 
v___f_1135_ = l_main___closed__0;
v___x_1136_ = l_run_x27___redArg(v___f_1135_);
lean_dec_ref(v___x_1136_);
v___f_1137_ = l_main___closed__1;
v___x_1138_ = l_run_x27___redArg(v___f_1137_);
lean_dec_ref(v___x_1138_);
v___f_1139_ = l_main___closed__2;
v___x_1140_ = l_run_x27___redArg(v___f_1139_);
lean_dec_ref(v___x_1140_);
v___f_1141_ = l_main___closed__3;
v___x_1142_ = l_run_x27___redArg(v___f_1141_);
lean_dec_ref(v___x_1142_);
v___f_1143_ = l_main___closed__4;
v___x_1144_ = l_run_x27___redArg(v___f_1143_);
lean_dec_ref(v___x_1144_);
v___f_1145_ = l_main___closed__5;
v___x_1146_ = l_run_x27___redArg(v___f_1145_);
lean_dec_ref(v___x_1146_);
v___f_1147_ = l_main___closed__6;
v___x_1148_ = l_run_x27___redArg(v___f_1147_);
lean_dec_ref(v___x_1148_);
v___f_1149_ = l_main___closed__7;
v___x_1150_ = l_run_x27___redArg(v___f_1149_);
lean_dec_ref(v___x_1150_);
v___f_1151_ = l_main___closed__8;
v___x_1152_ = l_run_x27___redArg(v___f_1151_);
lean_dec_ref(v___x_1152_);
v___f_1153_ = l_main___closed__9;
v___x_1154_ = l_run_x27___redArg(v___f_1153_);
lean_dec_ref(v___x_1154_);
v___f_1155_ = l_main___closed__10;
v___x_1156_ = l_run_x27___redArg(v___f_1155_);
lean_dec_ref(v___x_1156_);
v___f_1157_ = l_main___closed__11;
v___x_1158_ = l_run_x27___redArg(v___f_1157_);
lean_dec_ref(v___x_1158_);
v___f_1159_ = l_main___closed__12;
v___x_1160_ = l_run_x27___redArg(v___f_1159_);
lean_dec_ref(v___x_1160_);
v___x_1161_ = l_l;
v___x_1162_ = lean_unsigned_to_nat(10000);
v___x_1163_ = l_printEveryNth(v___x_1161_, v___x_1162_);
if lean_obj_tag(v___x_1163_) == 0 {
let mut v___x_1164_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1165_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_1163_, 1);
v___x_1164_ = l_xs;
v___x_1165_ = l_printEveryNthSliceBased(v___x_1164_, v___x_1162_);
return v___x_1165_;
} else {
return v___x_1163_;
}
}
#[no_mangle] pub unsafe extern "C" fn l_main___boxed(mut v_a_1166_: *mut lean_object) -> *mut lean_object{
let mut v_res_1167_: *mut lean_object = core::ptr::null_mut(); 
v_res_1167_ = _lean_main();
return v_res_1167_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00main_spec__0(mut v_upperBound_1168_: *mut lean_object, mut v_inst_1169_: *mut lean_object, mut v_R_1170_: *mut lean_object, mut v_a_1171_: *mut lean_object, mut v_b_1172_: *mut lean_object, mut v_c_1173_: *mut lean_object) -> *mut lean_object{
let mut v___x_1174_: *mut lean_object = core::ptr::null_mut(); 
v___x_1174_ = l_WellFounded_opaqueFix_u2083___at___00main_spec__0___redArg(v_upperBound_1168_, v_a_1171_, v_b_1172_);
return v___x_1174_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00main_spec__0___boxed(mut v_upperBound_1175_: *mut lean_object, mut v_inst_1176_: *mut lean_object, mut v_R_1177_: *mut lean_object, mut v_a_1178_: *mut lean_object, mut v_b_1179_: *mut lean_object, mut v_c_1180_: *mut lean_object) -> *mut lean_object{
let mut v_res_1181_: *mut lean_object = core::ptr::null_mut(); 
v_res_1181_ = l_WellFounded_opaqueFix_u2083___at___00main_spec__0(v_upperBound_1175_, v_inst_1176_, v_R_1177_, v_a_1178_, v_b_1179_, v_c_1180_);
lean_dec(v_upperBound_1175_);
return v_res_1181_;
}
extern "C" { fn initialize_Init(builtin: u8) -> *mut lean_object; }
extern "C" { fn initialize_Std_Data_Iterators(builtin: u8) -> *mut lean_object; }
static mut _G_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn initialize_iterators(builtin: u8) -> *mut lean_object {
let mut res: *mut lean_object = core::ptr::null_mut();
if _G_initialized { return lean_io_result_mk_ok(lean_box(0)); }
_G_initialized = true;
res = initialize_Init(builtin);
if lean_io_result_is_error(res) { return res; }
lean_dec_ref(res);
res = initialize_Std_Data_Iterators(builtin);
if lean_io_result_is_error(res) { return res; }
lean_dec_ref(res);
l_xs = _init_l_xs();
lean_mark_persistent(l_xs);
l_l = _init_l_l();
lean_mark_persistent(l_l);
return lean_io_result_mk_ok(lean_box(0));
}
unsafe extern "C" fn run_main(argc: core::ffi::c_int, argv: *mut *mut core::ffi::c_char) -> *mut lean_object {
    return _lean_main();
}
#[no_mangle]
pub unsafe extern "C" fn main(argc: core::ffi::c_int, mut argv: *mut *mut core::ffi::c_char) -> core::ffi::c_int {
  argv = lean_setup_args(argc, argv);
  lean_initialize_runtime_module();
  let res = initialize_iterators(1 /* builtin */);
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
