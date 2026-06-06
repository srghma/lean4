// Lean compiler output
// Module: qsort
// Imports: public import Init public meta import Init
use lean_runtime::generated_abi::*;
extern "C" {
    fn l_Lean_Name_mkStr2(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_Lean_Name_mkStr1(_: *mut lean_object) -> *mut lean_object;
    fn l_String_toRawSubstring_x27(_: *mut lean_object) -> *mut lean_object;
    fn lean_array_get_size(_: *mut lean_object) -> *mut lean_object;
    fn lean_nat_sub(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_nat_dec_lt(_: *mut lean_object, _: *mut lean_object) -> u8;
    static mut l_instInhabitedUInt32: u32;
    fn lean_array_get_borrowed(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_nat_add(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_uint32_dec_le(_: u32, _: u32) -> u8;
    fn lean_uint32_dec_lt(_: u32, _: u32) -> u8;
    fn lean_uint32_add(_: u32, _: u32) -> u32;
    fn lean_uint32_to_nat(_: u32) -> *mut lean_object;
    fn lean_array_swap(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_uint32_shift_right(_: u32, _: u32) -> u32;
    fn lean_nat_dec_eq(_: *mut lean_object, _: *mut lean_object) -> u8;
    fn lean_uint32_of_nat(_: *mut lean_object) -> u32;
    fn lean_mk_empty_array_with_capacity(_: *mut lean_object) -> *mut lean_object;
    fn lean_uint32_mul(_: u32, _: u32) -> u32;
    fn lean_array_push(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_array_get(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_List_head_x21___redArg(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_string_utf8_byte_size(_: *mut lean_object) -> *mut lean_object;
    fn l_String_Slice_toNat_x21(_: *mut lean_object) -> *mut lean_object;
    fn l_Lean_Syntax_isOfKind(_: *mut lean_object, _: *mut lean_object) -> u8;
    fn l_Lean_Syntax_getArg(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_Lean_SourceInfo_fromRef(_: *mut lean_object, _: u8) -> *mut lean_object;
    fn l_Lean_Name_mkStr4(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_Lean_addMacroScope(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_Lean_Syntax_node1(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_Lean_Syntax_node2(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
}
#[no_mangle] pub static l_checkSortedAux___closed__0_value: lean_string_object<20> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [97, 114, 114, 97, 121, 32, 105, 115, 32, 110, 111, 116, 32, 115, 111, 114, 116, 101, 100, 0]};
static mut l_checkSortedAux___closed__0: *mut lean_object = core::ptr::addr_of!(l_checkSortedAux___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_checkSortedAux___closed__1_value: lean_ctor_object<1> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*1 + 0) as u16, m_other: 1, m_tag: 18 }, m_objs: [core::ptr::addr_of!(l_checkSortedAux___closed__0_value) as *mut lean_object] };
static mut l_checkSortedAux___closed__1: *mut lean_object = core::ptr::addr_of!(l_checkSortedAux___closed__1_value) as *mut lean_object;
#[no_mangle] pub static mut l_checkSortedAux___boxed__const__1: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static l_term_u2191___00__closed__0_value: lean_string_object<9> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 9, m_capacity: 9, m_length: 6, m_data: [116, 101, 114, 109, 226, 134, 145, 95, 0]};
static mut l_term_u2191___00__closed__0: *mut lean_object = core::ptr::addr_of!(l_term_u2191___00__closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_term_u2191___00__closed__1_value: lean_ctor_object<3> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 8) as u16, m_other: 2, m_tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut lean_object,core::ptr::addr_of!(l_term_u2191___00__closed__0_value) as *mut lean_object,17309880346548667397 as *mut lean_object] };
static mut l_term_u2191___00__closed__1: *mut lean_object = core::ptr::addr_of!(l_term_u2191___00__closed__1_value) as *mut lean_object;
#[no_mangle] pub static l_term_u2191___00__closed__2_value: lean_string_object<8> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [97, 110, 100, 116, 104, 101, 110, 0]};
static mut l_term_u2191___00__closed__2: *mut lean_object = core::ptr::addr_of!(l_term_u2191___00__closed__2_value) as *mut lean_object;
#[no_mangle] pub static l_term_u2191___00__closed__3_value: lean_ctor_object<3> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 8) as u16, m_other: 2, m_tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut lean_object,core::ptr::addr_of!(l_term_u2191___00__closed__2_value) as *mut lean_object,12571085391447129896 as *mut lean_object] };
static mut l_term_u2191___00__closed__3: *mut lean_object = core::ptr::addr_of!(l_term_u2191___00__closed__3_value) as *mut lean_object;
#[no_mangle] pub static l_term_u2191___00__closed__4_value: lean_string_object<4> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 134, 145, 0]};
static mut l_term_u2191___00__closed__4: *mut lean_object = core::ptr::addr_of!(l_term_u2191___00__closed__4_value) as *mut lean_object;
#[no_mangle] pub static l_term_u2191___00__closed__5_value: lean_ctor_object<1> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*1 + 0) as u16, m_other: 1, m_tag: 5 }, m_objs: [core::ptr::addr_of!(l_term_u2191___00__closed__4_value) as *mut lean_object] };
static mut l_term_u2191___00__closed__5: *mut lean_object = core::ptr::addr_of!(l_term_u2191___00__closed__5_value) as *mut lean_object;
#[no_mangle] pub static l_term_u2191___00__closed__6_value: lean_string_object<5> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 101, 114, 109, 0]};
static mut l_term_u2191___00__closed__6: *mut lean_object = core::ptr::addr_of!(l_term_u2191___00__closed__6_value) as *mut lean_object;
#[no_mangle] pub static l_term_u2191___00__closed__7_value: lean_ctor_object<3> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 8) as u16, m_other: 2, m_tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut lean_object,core::ptr::addr_of!(l_term_u2191___00__closed__6_value) as *mut lean_object,8609355255726335675 as *mut lean_object] };
static mut l_term_u2191___00__closed__7: *mut lean_object = core::ptr::addr_of!(l_term_u2191___00__closed__7_value) as *mut lean_object;
#[no_mangle] pub static l_term_u2191___00__closed__8_value: lean_ctor_object<2> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 0) as u16, m_other: 2, m_tag: 7 }, m_objs: [core::ptr::addr_of!(l_term_u2191___00__closed__7_value) as *mut lean_object,((( 1024 as usize) << 1) | 1) as *mut lean_object] };
static mut l_term_u2191___00__closed__8: *mut lean_object = core::ptr::addr_of!(l_term_u2191___00__closed__8_value) as *mut lean_object;
#[no_mangle] pub static l_term_u2191___00__closed__9_value: lean_ctor_object<3> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*3 + 0) as u16, m_other: 3, m_tag: 2 }, m_objs: [core::ptr::addr_of!(l_term_u2191___00__closed__3_value) as *mut lean_object,core::ptr::addr_of!(l_term_u2191___00__closed__5_value) as *mut lean_object,core::ptr::addr_of!(l_term_u2191___00__closed__8_value) as *mut lean_object] };
static mut l_term_u2191___00__closed__9: *mut lean_object = core::ptr::addr_of!(l_term_u2191___00__closed__9_value) as *mut lean_object;
#[no_mangle] pub static l_term_u2191___00__closed__10_value: lean_ctor_object<3> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*3 + 0) as u16, m_other: 3, m_tag: 3 }, m_objs: [core::ptr::addr_of!(l_term_u2191___00__closed__1_value) as *mut lean_object,((( 1024 as usize) << 1) | 1) as *mut lean_object,core::ptr::addr_of!(l_term_u2191___00__closed__9_value) as *mut lean_object] };
static mut l_term_u2191___00__closed__10: *mut lean_object = core::ptr::addr_of!(l_term_u2191___00__closed__10_value) as *mut lean_object;
#[no_mangle] pub static mut l_term_u2191__: *mut lean_object = core::ptr::addr_of!(l_term_u2191___00__closed__10_value) as *mut lean_object;
#[no_mangle] pub static l___aux__qsort______macroRules__term_u2191____1___closed__0_value: lean_string_object<5> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___aux__qsort______macroRules__term_u2191____1___closed__0: *mut lean_object = core::ptr::addr_of!(l___aux__qsort______macroRules__term_u2191____1___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l___aux__qsort______macroRules__term_u2191____1___closed__1_value: lean_string_object<7> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___aux__qsort______macroRules__term_u2191____1___closed__1: *mut lean_object = core::ptr::addr_of!(l___aux__qsort______macroRules__term_u2191____1___closed__1_value) as *mut lean_object;
#[no_mangle] pub static l___aux__qsort______macroRules__term_u2191____1___closed__2_value: lean_string_object<5> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l___aux__qsort______macroRules__term_u2191____1___closed__2: *mut lean_object = core::ptr::addr_of!(l___aux__qsort______macroRules__term_u2191____1___closed__2_value) as *mut lean_object;
#[no_mangle] pub static l___aux__qsort______macroRules__term_u2191____1___closed__3_value: lean_string_object<4> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l___aux__qsort______macroRules__term_u2191____1___closed__3: *mut lean_object = core::ptr::addr_of!(l___aux__qsort______macroRules__term_u2191____1___closed__3_value) as *mut lean_object;
static l___aux__qsort______macroRules__term_u2191____1___closed__4_value_aux_0: lean_ctor_object<3> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 8) as u16, m_other: 2, m_tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut lean_object,core::ptr::addr_of!(l___aux__qsort______macroRules__term_u2191____1___closed__0_value) as *mut lean_object,11948124481539785030 as *mut lean_object] };
static l___aux__qsort______macroRules__term_u2191____1___closed__4_value_aux_1: lean_ctor_object<3> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 8) as u16, m_other: 2, m_tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__qsort______macroRules__term_u2191____1___closed__4_value_aux_0) as *mut lean_object,core::ptr::addr_of!(l___aux__qsort______macroRules__term_u2191____1___closed__1_value) as *mut lean_object,8018486133748762727 as *mut lean_object] };
static l___aux__qsort______macroRules__term_u2191____1___closed__4_value_aux_2: lean_ctor_object<3> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 8) as u16, m_other: 2, m_tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__qsort______macroRules__term_u2191____1___closed__4_value_aux_1) as *mut lean_object,core::ptr::addr_of!(l___aux__qsort______macroRules__term_u2191____1___closed__2_value) as *mut lean_object,16572064140653406795 as *mut lean_object] };
#[no_mangle] pub static l___aux__qsort______macroRules__term_u2191____1___closed__4_value: lean_ctor_object<3> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 8) as u16, m_other: 2, m_tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__qsort______macroRules__term_u2191____1___closed__4_value_aux_2) as *mut lean_object,core::ptr::addr_of!(l___aux__qsort______macroRules__term_u2191____1___closed__3_value) as *mut lean_object,12966880221525079621 as *mut lean_object] };
static mut l___aux__qsort______macroRules__term_u2191____1___closed__4: *mut lean_object = core::ptr::addr_of!(l___aux__qsort______macroRules__term_u2191____1___closed__4_value) as *mut lean_object;
#[no_mangle] pub static l___aux__qsort______macroRules__term_u2191____1___closed__5_value: lean_string_object<13> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [85, 73, 110, 116, 51, 50, 46, 116, 111, 78, 97, 116, 0]};
static mut l___aux__qsort______macroRules__term_u2191____1___closed__5: *mut lean_object = core::ptr::addr_of!(l___aux__qsort______macroRules__term_u2191____1___closed__5_value) as *mut lean_object;
static mut l___aux__qsort______macroRules__term_u2191____1___closed__6_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l___aux__qsort______macroRules__term_u2191____1___closed__6: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static l___aux__qsort______macroRules__term_u2191____1___closed__7_value: lean_string_object<7> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [85, 73, 110, 116, 51, 50, 0]};
static mut l___aux__qsort______macroRules__term_u2191____1___closed__7: *mut lean_object = core::ptr::addr_of!(l___aux__qsort______macroRules__term_u2191____1___closed__7_value) as *mut lean_object;
#[no_mangle] pub static l___aux__qsort______macroRules__term_u2191____1___closed__8_value: lean_string_object<6> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 111, 78, 97, 116, 0]};
static mut l___aux__qsort______macroRules__term_u2191____1___closed__8: *mut lean_object = core::ptr::addr_of!(l___aux__qsort______macroRules__term_u2191____1___closed__8_value) as *mut lean_object;
static l___aux__qsort______macroRules__term_u2191____1___closed__9_value_aux_0: lean_ctor_object<3> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 8) as u16, m_other: 2, m_tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut lean_object,core::ptr::addr_of!(l___aux__qsort______macroRules__term_u2191____1___closed__7_value) as *mut lean_object,13474504806189678690 as *mut lean_object] };
#[no_mangle] pub static l___aux__qsort______macroRules__term_u2191____1___closed__9_value: lean_ctor_object<3> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 8) as u16, m_other: 2, m_tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__qsort______macroRules__term_u2191____1___closed__9_value_aux_0) as *mut lean_object,core::ptr::addr_of!(l___aux__qsort______macroRules__term_u2191____1___closed__8_value) as *mut lean_object,1121087383445210552 as *mut lean_object] };
static mut l___aux__qsort______macroRules__term_u2191____1___closed__9: *mut lean_object = core::ptr::addr_of!(l___aux__qsort______macroRules__term_u2191____1___closed__9_value) as *mut lean_object;
#[no_mangle] pub static l___aux__qsort______macroRules__term_u2191____1___closed__10_value: lean_ctor_object<2> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 0) as u16, m_other: 2, m_tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__qsort______macroRules__term_u2191____1___closed__9_value) as *mut lean_object,((( 0 as usize) << 1) | 1) as *mut lean_object] };
static mut l___aux__qsort______macroRules__term_u2191____1___closed__10: *mut lean_object = core::ptr::addr_of!(l___aux__qsort______macroRules__term_u2191____1___closed__10_value) as *mut lean_object;
#[no_mangle] pub static l___aux__qsort______macroRules__term_u2191____1___closed__11_value: lean_ctor_object<1> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*1 + 0) as u16, m_other: 1, m_tag: 0 }, m_objs: [core::ptr::addr_of!(l___aux__qsort______macroRules__term_u2191____1___closed__9_value) as *mut lean_object] };
static mut l___aux__qsort______macroRules__term_u2191____1___closed__11: *mut lean_object = core::ptr::addr_of!(l___aux__qsort______macroRules__term_u2191____1___closed__11_value) as *mut lean_object;
#[no_mangle] pub static l___aux__qsort______macroRules__term_u2191____1___closed__12_value: lean_ctor_object<2> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 0) as u16, m_other: 2, m_tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__qsort______macroRules__term_u2191____1___closed__11_value) as *mut lean_object,((( 0 as usize) << 1) | 1) as *mut lean_object] };
static mut l___aux__qsort______macroRules__term_u2191____1___closed__12: *mut lean_object = core::ptr::addr_of!(l___aux__qsort______macroRules__term_u2191____1___closed__12_value) as *mut lean_object;
#[no_mangle] pub static l___aux__qsort______macroRules__term_u2191____1___closed__13_value: lean_ctor_object<2> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 0) as u16, m_other: 2, m_tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__qsort______macroRules__term_u2191____1___closed__10_value) as *mut lean_object,core::ptr::addr_of!(l___aux__qsort______macroRules__term_u2191____1___closed__12_value) as *mut lean_object] };
static mut l___aux__qsort______macroRules__term_u2191____1___closed__13: *mut lean_object = core::ptr::addr_of!(l___aux__qsort______macroRules__term_u2191____1___closed__13_value) as *mut lean_object;
#[no_mangle] pub static l___aux__qsort______macroRules__term_u2191____1___closed__14_value: lean_string_object<5> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l___aux__qsort______macroRules__term_u2191____1___closed__14: *mut lean_object = core::ptr::addr_of!(l___aux__qsort______macroRules__term_u2191____1___closed__14_value) as *mut lean_object;
#[no_mangle] pub static l___aux__qsort______macroRules__term_u2191____1___closed__15_value: lean_ctor_object<3> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 8) as u16, m_other: 2, m_tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut lean_object,core::ptr::addr_of!(l___aux__qsort______macroRules__term_u2191____1___closed__14_value) as *mut lean_object,9855511589286918680 as *mut lean_object] };
static mut l___aux__qsort______macroRules__term_u2191____1___closed__15: *mut lean_object = core::ptr::addr_of!(l___aux__qsort______macroRules__term_u2191____1___closed__15_value) as *mut lean_object;
#[no_mangle] pub static l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00main_spec__1___redArg___closed__0_value: lean_array_object<0> = lean_array_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00main_spec__1___redArg___closed__0: *mut lean_object = core::ptr::addr_of!(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00main_spec__1___redArg___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__0_value: lean_string_object<1> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_main___closed__0: *mut lean_object = core::ptr::addr_of!(l_main___closed__0_value) as *mut lean_object;
#[no_mangle] pub unsafe extern "C" fn l_badRand(mut v_seed_1_: u32) -> u32{
let mut v___x_2_: u32 = 0; let mut v___x_3_: u32 = 0; let mut v___x_4_: u32 = 0; let mut v___x_5_: u32 = 0; 
v___x_2_ = 1664525;
v___x_3_ = lean_uint32_mul(v_seed_1_, v___x_2_);
v___x_4_ = 1013904223;
v___x_5_ = lean_uint32_add(v___x_3_, v___x_4_);
return v___x_5_;
}
#[no_mangle] pub unsafe extern "C" fn l_badRand___boxed(mut v_seed_6_: *mut lean_object) -> *mut lean_object{
let mut v_seed_boxed_7_: u32 = 0; let mut v_res_8_: u32 = 0; let mut v_r_9_: *mut lean_object = core::ptr::null_mut(); 
v_seed_boxed_7_ = lean_unbox_uint32(v_seed_6_);
lean_dec(v_seed_6_);
v_res_8_ = l_badRand(v_seed_boxed_7_);
v_r_9_ = lean_box_uint32(v_res_8_);
return v_r_9_;
}
#[no_mangle] pub unsafe extern "C" fn l_mkRandomArray(mut v_x_10_: *mut lean_object, mut v_x_11_: u32, mut v_x_12_: *mut lean_object) -> *mut lean_object{
let mut v_zero_13_: *mut lean_object = core::ptr::null_mut(); let mut v_isZero_14_: u8 = 0; let mut v_one_15_: *mut lean_object = core::ptr::null_mut(); let mut v_n_16_: *mut lean_object = core::ptr::null_mut(); let mut v___x_17_: u32 = 0; let mut v___x_18_: *mut lean_object = core::ptr::null_mut(); let mut v___x_19_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v_zero_13_ = lean_unsigned_to_nat(0);
v_isZero_14_ = lean_nat_dec_eq(v_x_10_, v_zero_13_);
if v_isZero_14_ == 1 {
lean_dec(v_x_10_);
return v_x_12_;
} else {
let mut v_one_15_: *mut lean_object = core::ptr::null_mut(); let mut v_n_16_: *mut lean_object = core::ptr::null_mut(); let mut v___x_17_: u32 = 0; let mut v___x_18_: *mut lean_object = core::ptr::null_mut(); let mut v___x_19_: *mut lean_object = core::ptr::null_mut(); 
v_one_15_ = lean_unsigned_to_nat(1);
v_n_16_ = lean_nat_sub(v_x_10_, v_one_15_);
lean_dec(v_x_10_);
v___x_17_ = l_badRand(v_x_11_);
v___x_18_ = lean_box_uint32(v_x_11_);
v___x_19_ = lean_array_push(v_x_12_, v___x_18_);
v_x_10_ = v_n_16_;
v_x_11_ = v___x_17_;
v_x_12_ = v___x_19_;
state = 0; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_mkRandomArray___boxed(mut v_x_21_: *mut lean_object, mut v_x_22_: *mut lean_object, mut v_x_23_: *mut lean_object) -> *mut lean_object{
let mut v_x_20__boxed_24_: u32 = 0; let mut v_res_25_: *mut lean_object = core::ptr::null_mut(); 
v_x_20__boxed_24_ = lean_unbox_uint32(v_x_22_);
lean_dec(v_x_22_);
v_res_25_ = l_mkRandomArray(v_x_21_, v_x_20__boxed_24_, v_x_23_);
return v_res_25_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_checkSortedAux___boxed__const__1() -> *mut lean_object{
let mut v___x_29_: u32 = 0; let mut v___x_30_: *mut lean_object = core::ptr::null_mut(); 
v___x_29_ = l_instInhabitedUInt32;
v___x_30_ = lean_box_uint32(v___x_29_);
return v___x_30_;
}
#[no_mangle] pub unsafe extern "C" fn l_checkSortedAux(mut v_a_31_: *mut lean_object, mut v_x_32_: *mut lean_object) -> *mut lean_object{
let mut v___x_34_: *mut lean_object = core::ptr::null_mut(); let mut v___x_35_: *mut lean_object = core::ptr::null_mut(); let mut v___x_36_: *mut lean_object = core::ptr::null_mut(); let mut v___x_37_: u8 = 0; let mut v___x_38_: *mut lean_object = core::ptr::null_mut(); let mut v___x_39_: *mut lean_object = core::ptr::null_mut(); let mut v___x_40_: *mut lean_object = core::ptr::null_mut(); let mut v___x_41_: *mut lean_object = core::ptr::null_mut(); let mut v___x_42_: *mut lean_object = core::ptr::null_mut(); let mut v___x_43_: *mut lean_object = core::ptr::null_mut(); let mut v___x_44_: *mut lean_object = core::ptr::null_mut(); let mut v___x_45_: u32 = 0; let mut v___x_46_: u32 = 0; let mut v___x_47_: u8 = 0; let mut v___x_48_: *mut lean_object = core::ptr::null_mut(); let mut v___x_49_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_34_ = lean_array_get_size(v_a_31_);
v___x_35_ = lean_unsigned_to_nat(1);
v___x_36_ = lean_nat_sub(v___x_34_, v___x_35_);
v___x_37_ = lean_nat_dec_lt(v_x_32_, v___x_36_);
lean_dec(v___x_36_);
if v___x_37_ == 0 {
let mut v___x_38_: *mut lean_object = core::ptr::null_mut(); let mut v___x_39_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_x_32_);
v___x_38_ = lean_box(0);
v___x_39_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_39_, 0, v___x_38_);
return v___x_39_;
} else {
let mut v___x_40_: *mut lean_object = core::ptr::null_mut(); let mut v___x_41_: *mut lean_object = core::ptr::null_mut(); let mut v___x_42_: *mut lean_object = core::ptr::null_mut(); let mut v___x_43_: *mut lean_object = core::ptr::null_mut(); let mut v___x_44_: *mut lean_object = core::ptr::null_mut(); let mut v___x_45_: u32 = 0; let mut v___x_46_: u32 = 0; let mut v___x_47_: u8 = 0; 
v___x_40_ = l_checkSortedAux___boxed__const__1;
v___x_41_ = lean_array_get_borrowed(v___x_40_, v_a_31_, v_x_32_);
v___x_42_ = lean_nat_add(v_x_32_, v___x_35_);
lean_dec(v_x_32_);
v___x_43_ = l_checkSortedAux___boxed__const__1;
v___x_44_ = lean_array_get_borrowed(v___x_43_, v_a_31_, v___x_42_);
v___x_45_ = lean_unbox_uint32(v___x_41_);
v___x_46_ = lean_unbox_uint32(v___x_44_);
v___x_47_ = lean_uint32_dec_le(v___x_45_, v___x_46_);
if v___x_47_ == 0 {
let mut v___x_48_: *mut lean_object = core::ptr::null_mut(); let mut v___x_49_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v___x_42_);
v___x_48_ = l_checkSortedAux___closed__1;
v___x_49_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v___x_49_, 0, v___x_48_);
return v___x_49_;
} else {
v_x_32_ = v___x_42_;
state = 0; continue;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_checkSortedAux___boxed(mut v_a_51_: *mut lean_object, mut v_x_52_: *mut lean_object, mut v_a_53_: *mut lean_object) -> *mut lean_object{
let mut v_res_54_: *mut lean_object = core::ptr::null_mut(); 
v_res_54_ = l_checkSortedAux(v_a_51_, v_x_52_);
lean_dec_ref(v_a_51_);
return v_res_54_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l___aux__qsort______macroRules__term_u2191____1___closed__6() -> *mut lean_object{
let mut v___x_89_: *mut lean_object = core::ptr::null_mut(); let mut v___x_90_: *mut lean_object = core::ptr::null_mut(); 
v___x_89_ = l___aux__qsort______macroRules__term_u2191____1___closed__5;
v___x_90_ = l_String_toRawSubstring_x27(v___x_89_);
return v___x_90_;
}
#[no_mangle] pub unsafe extern "C" fn l___aux__qsort______macroRules__term_u2191____1(mut v_x_110_: *mut lean_object, mut v_a_111_: *mut lean_object, mut v_a_112_: *mut lean_object) -> *mut lean_object{
let mut v___x_113_: *mut lean_object = core::ptr::null_mut(); let mut v___x_114_: u8 = 0; 
v___x_113_ = l_term_u2191___00__closed__1;
lean_inc(v_x_110_);
v___x_114_ = l_Lean_Syntax_isOfKind(v_x_110_, v___x_113_);
if v___x_114_ == 0 {
let mut v___x_115_: *mut lean_object = core::ptr::null_mut(); let mut v___x_116_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_x_110_);
v___x_115_ = lean_box(1);
v___x_116_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_116_, 0, v___x_115_);
lean_ctor_set(v___x_116_, 1, v_a_112_);
return v___x_116_;
} else {
let mut v_quotContext_117_: *mut lean_object = core::ptr::null_mut(); let mut v_currMacroScope_118_: *mut lean_object = core::ptr::null_mut(); let mut v_ref_119_: *mut lean_object = core::ptr::null_mut(); let mut v___x_120_: *mut lean_object = core::ptr::null_mut(); let mut v___x_121_: *mut lean_object = core::ptr::null_mut(); let mut v___x_122_: u8 = 0; let mut v___x_123_: *mut lean_object = core::ptr::null_mut(); let mut v___x_124_: *mut lean_object = core::ptr::null_mut(); let mut v___x_125_: *mut lean_object = core::ptr::null_mut(); let mut v___x_126_: *mut lean_object = core::ptr::null_mut(); let mut v___x_127_: *mut lean_object = core::ptr::null_mut(); let mut v___x_128_: *mut lean_object = core::ptr::null_mut(); let mut v___x_129_: *mut lean_object = core::ptr::null_mut(); let mut v___x_130_: *mut lean_object = core::ptr::null_mut(); let mut v___x_131_: *mut lean_object = core::ptr::null_mut(); let mut v___x_132_: *mut lean_object = core::ptr::null_mut(); let mut v___x_133_: *mut lean_object = core::ptr::null_mut(); 
v_quotContext_117_ = lean_ctor_get(v_a_111_, 1);
v_currMacroScope_118_ = lean_ctor_get(v_a_111_, 2);
v_ref_119_ = lean_ctor_get(v_a_111_, 5);
v___x_120_ = lean_unsigned_to_nat(1);
v___x_121_ = l_Lean_Syntax_getArg(v_x_110_, v___x_120_);
lean_dec(v_x_110_);
v___x_122_ = 0;
v___x_123_ = l_Lean_SourceInfo_fromRef(v_ref_119_, v___x_122_);
v___x_124_ = l___aux__qsort______macroRules__term_u2191____1___closed__4;
v___x_125_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__qsort______macroRules__term_u2191____1___closed__6), core::ptr::addr_of_mut!(l___aux__qsort______macroRules__term_u2191____1___closed__6_once), _init_l___aux__qsort______macroRules__term_u2191____1___closed__6);
v___x_126_ = l___aux__qsort______macroRules__term_u2191____1___closed__9;
lean_inc(v_currMacroScope_118_);
lean_inc(v_quotContext_117_);
v___x_127_ = l_Lean_addMacroScope(v_quotContext_117_, v___x_126_, v_currMacroScope_118_);
v___x_128_ = l___aux__qsort______macroRules__term_u2191____1___closed__13;
lean_inc_n(v___x_123_, 2);
v___x_129_ = lean_alloc_ctor(3, 4, (0) as u32);
lean_ctor_set(v___x_129_, 0, v___x_123_);
lean_ctor_set(v___x_129_, 1, v___x_125_);
lean_ctor_set(v___x_129_, 2, v___x_127_);
lean_ctor_set(v___x_129_, 3, v___x_128_);
v___x_130_ = l___aux__qsort______macroRules__term_u2191____1___closed__15;
v___x_131_ = l_Lean_Syntax_node1(v___x_123_, v___x_130_, v___x_121_);
v___x_132_ = l_Lean_Syntax_node2(v___x_123_, v___x_124_, v___x_129_, v___x_131_);
v___x_133_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_133_, 0, v___x_132_);
lean_ctor_set(v___x_133_, 1, v_a_112_);
return v___x_133_;
}
}
#[no_mangle] pub unsafe extern "C" fn l___aux__qsort______macroRules__term_u2191____1___boxed(mut v_x_134_: *mut lean_object, mut v_a_135_: *mut lean_object, mut v_a_136_: *mut lean_object) -> *mut lean_object{
let mut v_res_137_: *mut lean_object = core::ptr::null_mut(); 
v_res_137_ = l___aux__qsort______macroRules__term_u2191____1(v_x_134_, v_a_135_, v_a_136_);
lean_dec_ref(v_a_135_);
return v_res_137_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_qsort_0__partitionAux___redArg(mut v_inst_138_: *mut lean_object, mut v_lt_139_: *mut lean_object, mut v_hi_140_: u32, mut v_pivot_141_: *mut lean_object, mut v_x_142_: *mut lean_object, mut v_x_143_: u32, mut v_x_144_: u32) -> *mut lean_object{
let mut v___x_145_: u8 = 0; let mut v___x_146_: *mut lean_object = core::ptr::null_mut(); let mut v___x_147_: *mut lean_object = core::ptr::null_mut(); let mut v_as_148_: *mut lean_object = core::ptr::null_mut(); let mut v___x_149_: *mut lean_object = core::ptr::null_mut(); let mut v___x_150_: *mut lean_object = core::ptr::null_mut(); let mut v___x_151_: *mut lean_object = core::ptr::null_mut(); let mut v___x_152_: *mut lean_object = core::ptr::null_mut(); let mut v___x_153_: *mut lean_object = core::ptr::null_mut(); let mut v___x_154_: u8 = 0; let mut v___x_155_: u32 = 0; let mut v___x_156_: u32 = 0; let mut v___x_158_: *mut lean_object = core::ptr::null_mut(); let mut v_as_159_: *mut lean_object = core::ptr::null_mut(); let mut v___x_160_: u32 = 0; let mut v___x_161_: u32 = 0; let mut v___x_162_: u32 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_145_ = lean_uint32_dec_lt(v_x_144_, v_hi_140_);
if v___x_145_ == 0 {
let mut v___x_146_: *mut lean_object = core::ptr::null_mut(); let mut v___x_147_: *mut lean_object = core::ptr::null_mut(); let mut v_as_148_: *mut lean_object = core::ptr::null_mut(); let mut v___x_149_: *mut lean_object = core::ptr::null_mut(); let mut v___x_150_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_pivot_141_);
lean_dec_ref(v_lt_139_);
v___x_146_ = lean_uint32_to_nat(v_x_143_);
v___x_147_ = lean_uint32_to_nat(v_hi_140_);
v_as_148_ = lean_array_swap(v_x_142_, v___x_146_, v___x_147_);
lean_dec(v___x_147_);
lean_dec(v___x_146_);
v___x_149_ = lean_box_uint32(v_x_143_);
v___x_150_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_150_, 0, v___x_149_);
lean_ctor_set(v___x_150_, 1, v_as_148_);
return v___x_150_;
} else {
let mut v___x_151_: *mut lean_object = core::ptr::null_mut(); let mut v___x_152_: *mut lean_object = core::ptr::null_mut(); let mut v___x_153_: *mut lean_object = core::ptr::null_mut(); let mut v___x_154_: u8 = 0; 
v___x_151_ = lean_uint32_to_nat(v_x_144_);
v___x_152_ = lean_array_get_borrowed(v_inst_138_, v_x_142_, v___x_151_);
lean_inc_ref(v_lt_139_);
lean_inc(v_pivot_141_);
lean_inc(v___x_152_);
v___x_153_ = lean_apply_2(v_lt_139_, v___x_152_, v_pivot_141_);
v___x_154_ = (lean_unbox(v___x_153_) as u8);
if v___x_154_ == 0 {
let mut v___x_155_: u32 = 0; let mut v___x_156_: u32 = 0; 
lean_dec(v___x_151_);
v___x_155_ = 1;
v___x_156_ = lean_uint32_add(v_x_144_, v___x_155_);
v_x_144_ = v___x_156_;
state = 0; continue;
} else {
let mut v___x_158_: *mut lean_object = core::ptr::null_mut(); let mut v_as_159_: *mut lean_object = core::ptr::null_mut(); let mut v___x_160_: u32 = 0; let mut v___x_161_: u32 = 0; let mut v___x_162_: u32 = 0; 
v___x_158_ = lean_uint32_to_nat(v_x_143_);
v_as_159_ = lean_array_swap(v_x_142_, v___x_158_, v___x_151_);
lean_dec(v___x_151_);
lean_dec(v___x_158_);
v___x_160_ = 1;
v___x_161_ = lean_uint32_add(v_x_143_, v___x_160_);
v___x_162_ = lean_uint32_add(v_x_144_, v___x_160_);
v_x_142_ = v_as_159_;
v_x_143_ = v___x_161_;
v_x_144_ = v___x_162_;
state = 0; continue;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_qsort_0__partitionAux___redArg___boxed(mut v_inst_164_: *mut lean_object, mut v_lt_165_: *mut lean_object, mut v_hi_166_: *mut lean_object, mut v_pivot_167_: *mut lean_object, mut v_x_168_: *mut lean_object, mut v_x_169_: *mut lean_object, mut v_x_170_: *mut lean_object) -> *mut lean_object{
let mut v_hi_boxed_171_: u32 = 0; let mut v_x_144__boxed_172_: u32 = 0; let mut v_x_145__boxed_173_: u32 = 0; let mut v_res_174_: *mut lean_object = core::ptr::null_mut(); 
v_hi_boxed_171_ = lean_unbox_uint32(v_hi_166_);
lean_dec(v_hi_166_);
v_x_144__boxed_172_ = lean_unbox_uint32(v_x_169_);
lean_dec(v_x_169_);
v_x_145__boxed_173_ = lean_unbox_uint32(v_x_170_);
lean_dec(v_x_170_);
v_res_174_ = l___private_qsort_0__partitionAux___redArg(v_inst_164_, v_lt_165_, v_hi_boxed_171_, v_pivot_167_, v_x_168_, v_x_144__boxed_172_, v_x_145__boxed_173_);
lean_dec(v_inst_164_);
return v_res_174_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_qsort_0__partitionAux(mut v_00_u03b1_175_: *mut lean_object, mut v_inst_176_: *mut lean_object, mut v_lt_177_: *mut lean_object, mut v_hi_178_: u32, mut v_pivot_179_: *mut lean_object, mut v_x_180_: *mut lean_object, mut v_x_181_: u32, mut v_x_182_: u32) -> *mut lean_object{
let mut v___x_183_: *mut lean_object = core::ptr::null_mut(); 
v___x_183_ = l___private_qsort_0__partitionAux___redArg(v_inst_176_, v_lt_177_, v_hi_178_, v_pivot_179_, v_x_180_, v_x_181_, v_x_182_);
return v___x_183_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_qsort_0__partitionAux___boxed(mut v_00_u03b1_184_: *mut lean_object, mut v_inst_185_: *mut lean_object, mut v_lt_186_: *mut lean_object, mut v_hi_187_: *mut lean_object, mut v_pivot_188_: *mut lean_object, mut v_x_189_: *mut lean_object, mut v_x_190_: *mut lean_object, mut v_x_191_: *mut lean_object) -> *mut lean_object{
let mut v_hi_boxed_192_: u32 = 0; let mut v_x_190__boxed_193_: u32 = 0; let mut v_x_191__boxed_194_: u32 = 0; let mut v_res_195_: *mut lean_object = core::ptr::null_mut(); 
v_hi_boxed_192_ = lean_unbox_uint32(v_hi_187_);
lean_dec(v_hi_187_);
v_x_190__boxed_193_ = lean_unbox_uint32(v_x_190_);
lean_dec(v_x_190_);
v_x_191__boxed_194_ = lean_unbox_uint32(v_x_191_);
lean_dec(v_x_191_);
v_res_195_ = l___private_qsort_0__partitionAux(v_00_u03b1_184_, v_inst_185_, v_lt_186_, v_hi_boxed_192_, v_pivot_188_, v_x_189_, v_x_190__boxed_193_, v_x_191__boxed_194_);
lean_dec(v_inst_185_);
return v_res_195_;
}
#[no_mangle] pub unsafe extern "C" fn l_partition___redArg(mut v_inst_196_: *mut lean_object, mut v_as_197_: *mut lean_object, mut v_lt_198_: *mut lean_object, mut v_lo_199_: u32, mut v_hi_200_: u32) -> *mut lean_object{
let mut v___y_202_: *mut lean_object = core::ptr::null_mut(); let mut v___y_203_: *mut lean_object = core::ptr::null_mut(); let mut v_pivot_204_: *mut lean_object = core::ptr::null_mut(); let mut v___x_205_: *mut lean_object = core::ptr::null_mut(); let mut v___x_206_: u32 = 0; let mut v___x_207_: u32 = 0; let mut v_mid_208_: u32 = 0; let mut v___x_209_: *mut lean_object = core::ptr::null_mut(); let mut v___y_211_: *mut lean_object = core::ptr::null_mut(); let mut v___y_212_: *mut lean_object = core::ptr::null_mut(); let mut v___x_213_: *mut lean_object = core::ptr::null_mut(); let mut v___x_214_: *mut lean_object = core::ptr::null_mut(); let mut v___x_215_: *mut lean_object = core::ptr::null_mut(); let mut v___x_216_: u8 = 0; let mut v___x_217_: *mut lean_object = core::ptr::null_mut(); let mut v___x_218_: *mut lean_object = core::ptr::null_mut(); let mut v___x_219_: *mut lean_object = core::ptr::null_mut(); let mut v___y_221_: *mut lean_object = core::ptr::null_mut(); let mut v___x_222_: *mut lean_object = core::ptr::null_mut(); let mut v___x_223_: *mut lean_object = core::ptr::null_mut(); let mut v___x_224_: *mut lean_object = core::ptr::null_mut(); let mut v___x_225_: *mut lean_object = core::ptr::null_mut(); let mut v___x_226_: u8 = 0; let mut v___x_227_: *mut lean_object = core::ptr::null_mut(); let mut v___x_228_: *mut lean_object = core::ptr::null_mut(); let mut v___x_229_: *mut lean_object = core::ptr::null_mut(); let mut v___x_230_: u8 = 0; let mut v___x_231_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_206_ = lean_uint32_add(v_lo_199_, v_hi_200_);
v___x_207_ = 1;
v_mid_208_ = lean_uint32_shift_right(v___x_206_, v___x_207_);
v___x_209_ = lean_uint32_to_nat(v_mid_208_);
v___x_218_ = lean_array_get_borrowed(v_inst_196_, v_as_197_, v___x_209_);
v___x_219_ = lean_uint32_to_nat(v_lo_199_);
v___x_228_ = lean_array_get_borrowed(v_inst_196_, v_as_197_, v___x_219_);
lean_inc_ref(v_lt_198_);
lean_inc(v___x_228_);
lean_inc(v___x_218_);
v___x_229_ = lean_apply_2(v_lt_198_, v___x_218_, v___x_228_);
v___x_230_ = (lean_unbox(v___x_229_) as u8);
if v___x_230_ == 0 {
v___y_221_ = v_as_197_;
state = 3; continue;
} else {
let mut v___x_231_: *mut lean_object = core::ptr::null_mut(); 
v___x_231_ = lean_array_swap(v_as_197_, v___x_219_, v___x_209_);
v___y_221_ = v___x_231_;
state = 3; continue;
}
}
1 => {
v_pivot_204_ = lean_array_get(v_inst_196_, v___y_203_, v___y_202_);
lean_dec(v___y_202_);
v___x_205_ = l___private_qsort_0__partitionAux___redArg(v_inst_196_, v_lt_198_, v_hi_200_, v_pivot_204_, v___y_203_, v_lo_199_, v_lo_199_);
return v___x_205_;
}
2 => {
v___x_213_ = lean_array_get_borrowed(v_inst_196_, v___y_212_, v___x_209_);
v___x_214_ = lean_array_get_borrowed(v_inst_196_, v___y_212_, v___y_211_);
lean_inc_ref(v_lt_198_);
lean_inc(v___x_214_);
lean_inc(v___x_213_);
v___x_215_ = lean_apply_2(v_lt_198_, v___x_213_, v___x_214_);
v___x_216_ = (lean_unbox(v___x_215_) as u8);
if v___x_216_ == 0 {
lean_dec(v___x_209_);
v___y_202_ = v___y_211_;
v___y_203_ = v___y_212_;
state = 1; continue;
} else {
let mut v___x_217_: *mut lean_object = core::ptr::null_mut(); 
v___x_217_ = lean_array_swap(v___y_212_, v___x_209_, v___y_211_);
lean_dec(v___x_209_);
v___y_202_ = v___y_211_;
v___y_203_ = v___x_217_;
state = 1; continue;
}
}
3 => {
v___x_222_ = lean_uint32_to_nat(v_hi_200_);
v___x_223_ = lean_array_get_borrowed(v_inst_196_, v___y_221_, v___x_222_);
v___x_224_ = lean_array_get_borrowed(v_inst_196_, v___y_221_, v___x_219_);
lean_inc_ref(v_lt_198_);
lean_inc(v___x_224_);
lean_inc(v___x_223_);
v___x_225_ = lean_apply_2(v_lt_198_, v___x_223_, v___x_224_);
v___x_226_ = (lean_unbox(v___x_225_) as u8);
if v___x_226_ == 0 {
lean_dec(v___x_219_);
v___y_211_ = v___x_222_;
v___y_212_ = v___y_221_;
state = 2; continue;
} else {
let mut v___x_227_: *mut lean_object = core::ptr::null_mut(); 
v___x_227_ = lean_array_swap(v___y_221_, v___x_219_, v___x_222_);
lean_dec(v___x_219_);
v___y_211_ = v___x_222_;
v___y_212_ = v___x_227_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_partition___redArg___boxed(mut v_inst_232_: *mut lean_object, mut v_as_233_: *mut lean_object, mut v_lt_234_: *mut lean_object, mut v_lo_235_: *mut lean_object, mut v_hi_236_: *mut lean_object) -> *mut lean_object{
let mut v_lo_boxed_237_: u32 = 0; let mut v_hi_boxed_238_: u32 = 0; let mut v_res_239_: *mut lean_object = core::ptr::null_mut(); 
v_lo_boxed_237_ = lean_unbox_uint32(v_lo_235_);
lean_dec(v_lo_235_);
v_hi_boxed_238_ = lean_unbox_uint32(v_hi_236_);
lean_dec(v_hi_236_);
v_res_239_ = l_partition___redArg(v_inst_232_, v_as_233_, v_lt_234_, v_lo_boxed_237_, v_hi_boxed_238_);
lean_dec(v_inst_232_);
return v_res_239_;
}
#[no_mangle] pub unsafe extern "C" fn l_partition(mut v_00_u03b1_240_: *mut lean_object, mut v_inst_241_: *mut lean_object, mut v_as_242_: *mut lean_object, mut v_lt_243_: *mut lean_object, mut v_lo_244_: u32, mut v_hi_245_: u32) -> *mut lean_object{
let mut v___y_247_: *mut lean_object = core::ptr::null_mut(); let mut v___y_248_: *mut lean_object = core::ptr::null_mut(); let mut v_pivot_249_: *mut lean_object = core::ptr::null_mut(); let mut v___x_250_: *mut lean_object = core::ptr::null_mut(); let mut v___x_251_: u32 = 0; let mut v___x_252_: u32 = 0; let mut v_mid_253_: u32 = 0; let mut v___x_254_: *mut lean_object = core::ptr::null_mut(); let mut v___y_256_: *mut lean_object = core::ptr::null_mut(); let mut v___y_257_: *mut lean_object = core::ptr::null_mut(); let mut v___x_258_: *mut lean_object = core::ptr::null_mut(); let mut v___x_259_: *mut lean_object = core::ptr::null_mut(); let mut v___x_260_: *mut lean_object = core::ptr::null_mut(); let mut v___x_261_: u8 = 0; let mut v___x_262_: *mut lean_object = core::ptr::null_mut(); let mut v___x_263_: *mut lean_object = core::ptr::null_mut(); let mut v___x_264_: *mut lean_object = core::ptr::null_mut(); let mut v___y_266_: *mut lean_object = core::ptr::null_mut(); let mut v___x_267_: *mut lean_object = core::ptr::null_mut(); let mut v___x_268_: *mut lean_object = core::ptr::null_mut(); let mut v___x_269_: *mut lean_object = core::ptr::null_mut(); let mut v___x_270_: *mut lean_object = core::ptr::null_mut(); let mut v___x_271_: u8 = 0; let mut v___x_272_: *mut lean_object = core::ptr::null_mut(); let mut v___x_273_: *mut lean_object = core::ptr::null_mut(); let mut v___x_274_: *mut lean_object = core::ptr::null_mut(); let mut v___x_275_: u8 = 0; let mut v___x_276_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_251_ = lean_uint32_add(v_lo_244_, v_hi_245_);
v___x_252_ = 1;
v_mid_253_ = lean_uint32_shift_right(v___x_251_, v___x_252_);
v___x_254_ = lean_uint32_to_nat(v_mid_253_);
v___x_263_ = lean_array_get_borrowed(v_inst_241_, v_as_242_, v___x_254_);
v___x_264_ = lean_uint32_to_nat(v_lo_244_);
v___x_273_ = lean_array_get_borrowed(v_inst_241_, v_as_242_, v___x_264_);
lean_inc_ref(v_lt_243_);
lean_inc(v___x_273_);
lean_inc(v___x_263_);
v___x_274_ = lean_apply_2(v_lt_243_, v___x_263_, v___x_273_);
v___x_275_ = (lean_unbox(v___x_274_) as u8);
if v___x_275_ == 0 {
v___y_266_ = v_as_242_;
state = 3; continue;
} else {
let mut v___x_276_: *mut lean_object = core::ptr::null_mut(); 
v___x_276_ = lean_array_swap(v_as_242_, v___x_264_, v___x_254_);
v___y_266_ = v___x_276_;
state = 3; continue;
}
}
1 => {
v_pivot_249_ = lean_array_get(v_inst_241_, v___y_248_, v___y_247_);
lean_dec(v___y_247_);
v___x_250_ = l___private_qsort_0__partitionAux___redArg(v_inst_241_, v_lt_243_, v_hi_245_, v_pivot_249_, v___y_248_, v_lo_244_, v_lo_244_);
return v___x_250_;
}
2 => {
v___x_258_ = lean_array_get_borrowed(v_inst_241_, v___y_257_, v___x_254_);
v___x_259_ = lean_array_get_borrowed(v_inst_241_, v___y_257_, v___y_256_);
lean_inc_ref(v_lt_243_);
lean_inc(v___x_259_);
lean_inc(v___x_258_);
v___x_260_ = lean_apply_2(v_lt_243_, v___x_258_, v___x_259_);
v___x_261_ = (lean_unbox(v___x_260_) as u8);
if v___x_261_ == 0 {
lean_dec(v___x_254_);
v___y_247_ = v___y_256_;
v___y_248_ = v___y_257_;
state = 1; continue;
} else {
let mut v___x_262_: *mut lean_object = core::ptr::null_mut(); 
v___x_262_ = lean_array_swap(v___y_257_, v___x_254_, v___y_256_);
lean_dec(v___x_254_);
v___y_247_ = v___y_256_;
v___y_248_ = v___x_262_;
state = 1; continue;
}
}
3 => {
v___x_267_ = lean_uint32_to_nat(v_hi_245_);
v___x_268_ = lean_array_get_borrowed(v_inst_241_, v___y_266_, v___x_267_);
v___x_269_ = lean_array_get_borrowed(v_inst_241_, v___y_266_, v___x_264_);
lean_inc_ref(v_lt_243_);
lean_inc(v___x_269_);
lean_inc(v___x_268_);
v___x_270_ = lean_apply_2(v_lt_243_, v___x_268_, v___x_269_);
v___x_271_ = (lean_unbox(v___x_270_) as u8);
if v___x_271_ == 0 {
lean_dec(v___x_264_);
v___y_256_ = v___x_267_;
v___y_257_ = v___y_266_;
state = 2; continue;
} else {
let mut v___x_272_: *mut lean_object = core::ptr::null_mut(); 
v___x_272_ = lean_array_swap(v___y_266_, v___x_264_, v___x_267_);
lean_dec(v___x_264_);
v___y_256_ = v___x_267_;
v___y_257_ = v___x_272_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_partition___boxed(mut v_00_u03b1_277_: *mut lean_object, mut v_inst_278_: *mut lean_object, mut v_as_279_: *mut lean_object, mut v_lt_280_: *mut lean_object, mut v_lo_281_: *mut lean_object, mut v_hi_282_: *mut lean_object) -> *mut lean_object{
let mut v_lo_boxed_283_: u32 = 0; let mut v_hi_boxed_284_: u32 = 0; let mut v_res_285_: *mut lean_object = core::ptr::null_mut(); 
v_lo_boxed_283_ = lean_unbox_uint32(v_lo_281_);
lean_dec(v_lo_281_);
v_hi_boxed_284_ = lean_unbox_uint32(v_hi_282_);
lean_dec(v_hi_282_);
v_res_285_ = l_partition(v_00_u03b1_277_, v_inst_278_, v_as_279_, v_lt_280_, v_lo_boxed_283_, v_hi_boxed_284_);
lean_dec(v_inst_278_);
return v_res_285_;
}
#[no_mangle] pub unsafe extern "C" fn l_qsortAux___redArg(mut v_inst_286_: *mut lean_object, mut v_lt_287_: *mut lean_object, mut v_x_288_: *mut lean_object, mut v_x_289_: u32, mut v_x_290_: u32) -> *mut lean_object{
let mut v___x_291_: u8 = 0; let mut v___x_292_: u32 = 0; let mut v___x_293_: u32 = 0; let mut v___y_295_: *mut lean_object = core::ptr::null_mut(); let mut v___y_296_: *mut lean_object = core::ptr::null_mut(); let mut v_pivot_297_: *mut lean_object = core::ptr::null_mut(); let mut v___x_298_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_299_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_300_: *mut lean_object = core::ptr::null_mut(); let mut v___x_301_: u32 = 0; let mut v_as_302_: *mut lean_object = core::ptr::null_mut(); let mut v___x_303_: u32 = 0; let mut v___x_304_: u32 = 0; let mut v_mid_306_: u32 = 0; let mut v___x_307_: *mut lean_object = core::ptr::null_mut(); let mut v___y_309_: *mut lean_object = core::ptr::null_mut(); let mut v___y_310_: *mut lean_object = core::ptr::null_mut(); let mut v___x_311_: *mut lean_object = core::ptr::null_mut(); let mut v___x_312_: *mut lean_object = core::ptr::null_mut(); let mut v___x_313_: *mut lean_object = core::ptr::null_mut(); let mut v___x_314_: u8 = 0; let mut v___x_315_: *mut lean_object = core::ptr::null_mut(); let mut v___x_316_: *mut lean_object = core::ptr::null_mut(); let mut v___x_317_: *mut lean_object = core::ptr::null_mut(); let mut v___y_319_: *mut lean_object = core::ptr::null_mut(); let mut v___x_320_: *mut lean_object = core::ptr::null_mut(); let mut v___x_321_: *mut lean_object = core::ptr::null_mut(); let mut v___x_322_: *mut lean_object = core::ptr::null_mut(); let mut v___x_323_: *mut lean_object = core::ptr::null_mut(); let mut v___x_324_: u8 = 0; let mut v___x_325_: *mut lean_object = core::ptr::null_mut(); let mut v___x_326_: *mut lean_object = core::ptr::null_mut(); let mut v___x_327_: *mut lean_object = core::ptr::null_mut(); let mut v___x_328_: u8 = 0; let mut v___x_329_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_291_ = lean_uint32_dec_lt(v_x_289_, v_x_290_);
if v___x_291_ == 0 {
lean_dec_ref(v_lt_287_);
return v_x_288_;
} else {
let mut v___x_292_: u32 = 0; let mut v___x_293_: u32 = 0; let mut v___y_295_: *mut lean_object = core::ptr::null_mut(); let mut v___y_296_: *mut lean_object = core::ptr::null_mut(); let mut v_mid_306_: u32 = 0; let mut v___x_307_: *mut lean_object = core::ptr::null_mut(); let mut v___y_309_: *mut lean_object = core::ptr::null_mut(); let mut v___y_310_: *mut lean_object = core::ptr::null_mut(); let mut v___x_316_: *mut lean_object = core::ptr::null_mut(); let mut v___x_317_: *mut lean_object = core::ptr::null_mut(); let mut v___y_319_: *mut lean_object = core::ptr::null_mut(); let mut v___x_326_: *mut lean_object = core::ptr::null_mut(); let mut v___x_327_: *mut lean_object = core::ptr::null_mut(); let mut v___x_328_: u8 = 0; 
v___x_292_ = lean_uint32_add(v_x_289_, v_x_290_);
v___x_293_ = 1;
v_mid_306_ = lean_uint32_shift_right(v___x_292_, v___x_293_);
v___x_307_ = lean_uint32_to_nat(v_mid_306_);
v___x_316_ = lean_array_get_borrowed(v_inst_286_, v_x_288_, v___x_307_);
v___x_317_ = lean_uint32_to_nat(v_x_289_);
v___x_326_ = lean_array_get_borrowed(v_inst_286_, v_x_288_, v___x_317_);
lean_inc_ref(v_lt_287_);
lean_inc(v___x_326_);
lean_inc(v___x_316_);
v___x_327_ = lean_apply_2(v_lt_287_, v___x_316_, v___x_326_);
v___x_328_ = (lean_unbox(v___x_327_) as u8);
if v___x_328_ == 0 {
v___y_319_ = v_x_288_;
state = 3; continue;
} else {
let mut v___x_329_: *mut lean_object = core::ptr::null_mut(); 
v___x_329_ = lean_array_swap(v_x_288_, v___x_317_, v___x_307_);
v___y_319_ = v___x_329_;
state = 3; continue;
}
}
}
1 => {
v_pivot_297_ = lean_array_get(v_inst_286_, v___y_296_, v___y_295_);
lean_dec(v___y_295_);
lean_inc_ref_n(v_lt_287_, 2);
v___x_298_ = l___private_qsort_0__partitionAux___redArg(v_inst_286_, v_lt_287_, v_x_290_, v_pivot_297_, v___y_296_, v_x_289_, v_x_289_);
v_fst_299_ = lean_ctor_get(v___x_298_, 0);
lean_inc(v_fst_299_);
v_snd_300_ = lean_ctor_get(v___x_298_, 1);
lean_inc(v_snd_300_);
lean_dec_ref(v___x_298_);
v___x_301_ = lean_unbox_uint32(v_fst_299_);
v_as_302_ = l_qsortAux___redArg(v_inst_286_, v_lt_287_, v_snd_300_, v_x_289_, v___x_301_);
v___x_303_ = lean_unbox_uint32(v_fst_299_);
lean_dec(v_fst_299_);
v___x_304_ = lean_uint32_add(v___x_303_, v___x_293_);
v_x_288_ = v_as_302_;
v_x_289_ = v___x_304_;
state = 0; continue;
}
2 => {
v___x_311_ = lean_array_get_borrowed(v_inst_286_, v___y_310_, v___x_307_);
v___x_312_ = lean_array_get_borrowed(v_inst_286_, v___y_310_, v___y_309_);
lean_inc_ref(v_lt_287_);
lean_inc(v___x_312_);
lean_inc(v___x_311_);
v___x_313_ = lean_apply_2(v_lt_287_, v___x_311_, v___x_312_);
v___x_314_ = (lean_unbox(v___x_313_) as u8);
if v___x_314_ == 0 {
lean_dec(v___x_307_);
v___y_295_ = v___y_309_;
v___y_296_ = v___y_310_;
state = 1; continue;
} else {
let mut v___x_315_: *mut lean_object = core::ptr::null_mut(); 
v___x_315_ = lean_array_swap(v___y_310_, v___x_307_, v___y_309_);
lean_dec(v___x_307_);
v___y_295_ = v___y_309_;
v___y_296_ = v___x_315_;
state = 1; continue;
}
}
3 => {
v___x_320_ = lean_uint32_to_nat(v_x_290_);
v___x_321_ = lean_array_get_borrowed(v_inst_286_, v___y_319_, v___x_320_);
v___x_322_ = lean_array_get_borrowed(v_inst_286_, v___y_319_, v___x_317_);
lean_inc_ref(v_lt_287_);
lean_inc(v___x_322_);
lean_inc(v___x_321_);
v___x_323_ = lean_apply_2(v_lt_287_, v___x_321_, v___x_322_);
v___x_324_ = (lean_unbox(v___x_323_) as u8);
if v___x_324_ == 0 {
lean_dec(v___x_317_);
v___y_309_ = v___x_320_;
v___y_310_ = v___y_319_;
state = 2; continue;
} else {
let mut v___x_325_: *mut lean_object = core::ptr::null_mut(); 
v___x_325_ = lean_array_swap(v___y_319_, v___x_317_, v___x_320_);
lean_dec(v___x_317_);
v___y_309_ = v___x_320_;
v___y_310_ = v___x_325_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_qsortAux___redArg___boxed(mut v_inst_330_: *mut lean_object, mut v_lt_331_: *mut lean_object, mut v_x_332_: *mut lean_object, mut v_x_333_: *mut lean_object, mut v_x_334_: *mut lean_object) -> *mut lean_object{
let mut v_x_107__boxed_335_: u32 = 0; let mut v_x_108__boxed_336_: u32 = 0; let mut v_res_337_: *mut lean_object = core::ptr::null_mut(); 
v_x_107__boxed_335_ = lean_unbox_uint32(v_x_333_);
lean_dec(v_x_333_);
v_x_108__boxed_336_ = lean_unbox_uint32(v_x_334_);
lean_dec(v_x_334_);
v_res_337_ = l_qsortAux___redArg(v_inst_330_, v_lt_331_, v_x_332_, v_x_107__boxed_335_, v_x_108__boxed_336_);
lean_dec(v_inst_330_);
return v_res_337_;
}
#[no_mangle] pub unsafe extern "C" fn l_qsortAux(mut v_00_u03b1_338_: *mut lean_object, mut v_inst_339_: *mut lean_object, mut v_lt_340_: *mut lean_object, mut v_x_341_: *mut lean_object, mut v_x_342_: u32, mut v_x_343_: u32) -> *mut lean_object{
let mut v___x_344_: *mut lean_object = core::ptr::null_mut(); 
v___x_344_ = l_qsortAux___redArg(v_inst_339_, v_lt_340_, v_x_341_, v_x_342_, v_x_343_);
return v___x_344_;
}
#[no_mangle] pub unsafe extern "C" fn l_qsortAux___boxed(mut v_00_u03b1_345_: *mut lean_object, mut v_inst_346_: *mut lean_object, mut v_lt_347_: *mut lean_object, mut v_x_348_: *mut lean_object, mut v_x_349_: *mut lean_object, mut v_x_350_: *mut lean_object) -> *mut lean_object{
let mut v_x_187__boxed_351_: u32 = 0; let mut v_x_188__boxed_352_: u32 = 0; let mut v_res_353_: *mut lean_object = core::ptr::null_mut(); 
v_x_187__boxed_351_ = lean_unbox_uint32(v_x_349_);
lean_dec(v_x_349_);
v_x_188__boxed_352_ = lean_unbox_uint32(v_x_350_);
lean_dec(v_x_350_);
v_res_353_ = l_qsortAux(v_00_u03b1_345_, v_inst_346_, v_lt_347_, v_x_348_, v_x_187__boxed_351_, v_x_188__boxed_352_);
lean_dec(v_inst_346_);
return v_res_353_;
}
#[no_mangle] pub unsafe extern "C" fn l_qsort___redArg(mut v_inst_354_: *mut lean_object, mut v_as_355_: *mut lean_object, mut v_lt_356_: *mut lean_object) -> *mut lean_object{
let mut v___x_357_: u32 = 0; let mut v___x_358_: *mut lean_object = core::ptr::null_mut(); let mut v___x_359_: *mut lean_object = core::ptr::null_mut(); let mut v___x_360_: *mut lean_object = core::ptr::null_mut(); let mut v___x_361_: u32 = 0; let mut v___x_362_: *mut lean_object = core::ptr::null_mut(); 
v___x_357_ = 0;
v___x_358_ = lean_array_get_size(v_as_355_);
v___x_359_ = lean_unsigned_to_nat(1);
v___x_360_ = lean_nat_sub(v___x_358_, v___x_359_);
v___x_361_ = lean_uint32_of_nat(v___x_360_);
lean_dec(v___x_360_);
v___x_362_ = l_qsortAux___redArg(v_inst_354_, v_lt_356_, v_as_355_, v___x_357_, v___x_361_);
return v___x_362_;
}
#[no_mangle] pub unsafe extern "C" fn l_qsort___redArg___boxed(mut v_inst_363_: *mut lean_object, mut v_as_364_: *mut lean_object, mut v_lt_365_: *mut lean_object) -> *mut lean_object{
let mut v_res_366_: *mut lean_object = core::ptr::null_mut(); 
v_res_366_ = l_qsort___redArg(v_inst_363_, v_as_364_, v_lt_365_);
lean_dec(v_inst_363_);
return v_res_366_;
}
#[no_mangle] pub unsafe extern "C" fn l_qsort(mut v_00_u03b1_367_: *mut lean_object, mut v_inst_368_: *mut lean_object, mut v_as_369_: *mut lean_object, mut v_lt_370_: *mut lean_object) -> *mut lean_object{
let mut v___x_371_: u32 = 0; let mut v___x_372_: *mut lean_object = core::ptr::null_mut(); let mut v___x_373_: *mut lean_object = core::ptr::null_mut(); let mut v___x_374_: *mut lean_object = core::ptr::null_mut(); let mut v___x_375_: u32 = 0; let mut v___x_376_: *mut lean_object = core::ptr::null_mut(); 
v___x_371_ = 0;
v___x_372_ = lean_array_get_size(v_as_369_);
v___x_373_ = lean_unsigned_to_nat(1);
v___x_374_ = lean_nat_sub(v___x_372_, v___x_373_);
v___x_375_ = lean_uint32_of_nat(v___x_374_);
lean_dec(v___x_374_);
v___x_376_ = l_qsortAux___redArg(v_inst_368_, v_lt_370_, v_as_369_, v___x_371_, v___x_375_);
return v___x_376_;
}
#[no_mangle] pub unsafe extern "C" fn l_qsort___boxed(mut v_00_u03b1_377_: *mut lean_object, mut v_inst_378_: *mut lean_object, mut v_as_379_: *mut lean_object, mut v_lt_380_: *mut lean_object) -> *mut lean_object{
let mut v_res_381_: *mut lean_object = core::ptr::null_mut(); 
v_res_381_ = l_qsort(v_00_u03b1_377_, v_inst_378_, v_as_379_, v_lt_380_);
lean_dec(v_inst_378_);
return v_res_381_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_qsort_0__partitionAux___at___00qsortAux___at___00main_spec__0_spec__0(mut v_hi_382_: u32, mut v_pivot_383_: u32, mut v_x_384_: *mut lean_object, mut v_x_385_: u32, mut v_x_386_: u32) -> *mut lean_object{
let mut v___x_387_: u8 = 0; let mut v___x_388_: *mut lean_object = core::ptr::null_mut(); let mut v___x_389_: *mut lean_object = core::ptr::null_mut(); let mut v_as_390_: *mut lean_object = core::ptr::null_mut(); let mut v___x_391_: *mut lean_object = core::ptr::null_mut(); let mut v___x_392_: *mut lean_object = core::ptr::null_mut(); let mut v___x_393_: *mut lean_object = core::ptr::null_mut(); let mut v___x_394_: *mut lean_object = core::ptr::null_mut(); let mut v___x_395_: *mut lean_object = core::ptr::null_mut(); let mut v___x_396_: u32 = 0; let mut v___x_397_: u8 = 0; let mut v___x_398_: u32 = 0; let mut v___x_399_: u32 = 0; let mut v___x_401_: *mut lean_object = core::ptr::null_mut(); let mut v_as_402_: *mut lean_object = core::ptr::null_mut(); let mut v___x_403_: u32 = 0; let mut v___x_404_: u32 = 0; let mut v___x_405_: u32 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_387_ = lean_uint32_dec_lt(v_x_386_, v_hi_382_);
if v___x_387_ == 0 {
let mut v___x_388_: *mut lean_object = core::ptr::null_mut(); let mut v___x_389_: *mut lean_object = core::ptr::null_mut(); let mut v_as_390_: *mut lean_object = core::ptr::null_mut(); let mut v___x_391_: *mut lean_object = core::ptr::null_mut(); let mut v___x_392_: *mut lean_object = core::ptr::null_mut(); 
v___x_388_ = lean_uint32_to_nat(v_x_385_);
v___x_389_ = lean_uint32_to_nat(v_hi_382_);
v_as_390_ = lean_array_swap(v_x_384_, v___x_388_, v___x_389_);
lean_dec(v___x_389_);
lean_dec(v___x_388_);
v___x_391_ = lean_box_uint32(v_x_385_);
v___x_392_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_392_, 0, v___x_391_);
lean_ctor_set(v___x_392_, 1, v_as_390_);
return v___x_392_;
} else {
let mut v___x_393_: *mut lean_object = core::ptr::null_mut(); let mut v___x_394_: *mut lean_object = core::ptr::null_mut(); let mut v___x_395_: *mut lean_object = core::ptr::null_mut(); let mut v___x_396_: u32 = 0; let mut v___x_397_: u8 = 0; 
v___x_393_ = lean_uint32_to_nat(v_x_386_);
v___x_394_ = l_checkSortedAux___boxed__const__1;
v___x_395_ = lean_array_get_borrowed(v___x_394_, v_x_384_, v___x_393_);
v___x_396_ = lean_unbox_uint32(v___x_395_);
v___x_397_ = lean_uint32_dec_lt(v___x_396_, v_pivot_383_);
if v___x_397_ == 0 {
let mut v___x_398_: u32 = 0; let mut v___x_399_: u32 = 0; 
lean_dec(v___x_393_);
v___x_398_ = 1;
v___x_399_ = lean_uint32_add(v_x_386_, v___x_398_);
v_x_386_ = v___x_399_;
state = 0; continue;
} else {
let mut v___x_401_: *mut lean_object = core::ptr::null_mut(); let mut v_as_402_: *mut lean_object = core::ptr::null_mut(); let mut v___x_403_: u32 = 0; let mut v___x_404_: u32 = 0; let mut v___x_405_: u32 = 0; 
v___x_401_ = lean_uint32_to_nat(v_x_385_);
v_as_402_ = lean_array_swap(v_x_384_, v___x_401_, v___x_393_);
lean_dec(v___x_393_);
lean_dec(v___x_401_);
v___x_403_ = 1;
v___x_404_ = lean_uint32_add(v_x_385_, v___x_403_);
v___x_405_ = lean_uint32_add(v_x_386_, v___x_403_);
v_x_384_ = v_as_402_;
v_x_385_ = v___x_404_;
v_x_386_ = v___x_405_;
state = 0; continue;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_qsort_0__partitionAux___at___00qsortAux___at___00main_spec__0_spec__0___boxed(mut v_hi_407_: *mut lean_object, mut v_pivot_408_: *mut lean_object, mut v_x_409_: *mut lean_object, mut v_x_410_: *mut lean_object, mut v_x_411_: *mut lean_object) -> *mut lean_object{
let mut v_hi_boxed_412_: u32 = 0; let mut v_pivot_boxed_413_: u32 = 0; let mut v_x_373__boxed_414_: u32 = 0; let mut v_x_374__boxed_415_: u32 = 0; let mut v_res_416_: *mut lean_object = core::ptr::null_mut(); 
v_hi_boxed_412_ = lean_unbox_uint32(v_hi_407_);
lean_dec(v_hi_407_);
v_pivot_boxed_413_ = lean_unbox_uint32(v_pivot_408_);
lean_dec(v_pivot_408_);
v_x_373__boxed_414_ = lean_unbox_uint32(v_x_410_);
lean_dec(v_x_410_);
v_x_374__boxed_415_ = lean_unbox_uint32(v_x_411_);
lean_dec(v_x_411_);
v_res_416_ = l___private_qsort_0__partitionAux___at___00qsortAux___at___00main_spec__0_spec__0(v_hi_boxed_412_, v_pivot_boxed_413_, v_x_409_, v_x_373__boxed_414_, v_x_374__boxed_415_);
return v_res_416_;
}
#[no_mangle] pub unsafe extern "C" fn l_qsortAux___at___00main_spec__0(mut v_x_417_: *mut lean_object, mut v_x_418_: u32, mut v_x_419_: u32) -> *mut lean_object{
let mut v___x_420_: u8 = 0; let mut v___x_421_: u32 = 0; let mut v___x_422_: u32 = 0; let mut v___y_424_: *mut lean_object = core::ptr::null_mut(); let mut v___y_425_: *mut lean_object = core::ptr::null_mut(); let mut v___x_426_: *mut lean_object = core::ptr::null_mut(); let mut v_pivot_427_: *mut lean_object = core::ptr::null_mut(); let mut v___x_428_: u32 = 0; let mut v___x_429_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_430_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_431_: *mut lean_object = core::ptr::null_mut(); let mut v___x_432_: u32 = 0; let mut v_as_433_: *mut lean_object = core::ptr::null_mut(); let mut v___x_434_: u32 = 0; let mut v___x_435_: u32 = 0; let mut v_mid_437_: u32 = 0; let mut v___x_438_: *mut lean_object = core::ptr::null_mut(); let mut v___y_440_: *mut lean_object = core::ptr::null_mut(); let mut v___y_441_: *mut lean_object = core::ptr::null_mut(); let mut v___x_442_: *mut lean_object = core::ptr::null_mut(); let mut v___x_443_: *mut lean_object = core::ptr::null_mut(); let mut v___x_444_: *mut lean_object = core::ptr::null_mut(); let mut v___x_445_: *mut lean_object = core::ptr::null_mut(); let mut v___x_446_: u32 = 0; let mut v___x_447_: u32 = 0; let mut v___x_448_: u8 = 0; let mut v___x_449_: *mut lean_object = core::ptr::null_mut(); let mut v___x_450_: *mut lean_object = core::ptr::null_mut(); let mut v___x_451_: *mut lean_object = core::ptr::null_mut(); let mut v___x_452_: *mut lean_object = core::ptr::null_mut(); let mut v___y_454_: *mut lean_object = core::ptr::null_mut(); let mut v___x_455_: *mut lean_object = core::ptr::null_mut(); let mut v___x_456_: *mut lean_object = core::ptr::null_mut(); let mut v___x_457_: *mut lean_object = core::ptr::null_mut(); let mut v___x_458_: *mut lean_object = core::ptr::null_mut(); let mut v___x_459_: *mut lean_object = core::ptr::null_mut(); let mut v___x_460_: u32 = 0; let mut v___x_461_: u32 = 0; let mut v___x_462_: u8 = 0; let mut v___x_463_: *mut lean_object = core::ptr::null_mut(); let mut v___x_464_: *mut lean_object = core::ptr::null_mut(); let mut v___x_465_: *mut lean_object = core::ptr::null_mut(); let mut v___x_466_: u32 = 0; let mut v___x_467_: u32 = 0; let mut v___x_468_: u8 = 0; let mut v___x_469_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_420_ = lean_uint32_dec_lt(v_x_418_, v_x_419_);
if v___x_420_ == 0 {
return v_x_417_;
} else {
let mut v___x_421_: u32 = 0; let mut v___x_422_: u32 = 0; let mut v___y_424_: *mut lean_object = core::ptr::null_mut(); let mut v___y_425_: *mut lean_object = core::ptr::null_mut(); let mut v_mid_437_: u32 = 0; let mut v___x_438_: *mut lean_object = core::ptr::null_mut(); let mut v___y_440_: *mut lean_object = core::ptr::null_mut(); let mut v___y_441_: *mut lean_object = core::ptr::null_mut(); let mut v___x_450_: *mut lean_object = core::ptr::null_mut(); let mut v___x_451_: *mut lean_object = core::ptr::null_mut(); let mut v___x_452_: *mut lean_object = core::ptr::null_mut(); let mut v___y_454_: *mut lean_object = core::ptr::null_mut(); let mut v___x_464_: *mut lean_object = core::ptr::null_mut(); let mut v___x_465_: *mut lean_object = core::ptr::null_mut(); let mut v___x_466_: u32 = 0; let mut v___x_467_: u32 = 0; let mut v___x_468_: u8 = 0; 
v___x_421_ = lean_uint32_add(v_x_418_, v_x_419_);
v___x_422_ = 1;
v_mid_437_ = lean_uint32_shift_right(v___x_421_, v___x_422_);
v___x_438_ = lean_uint32_to_nat(v_mid_437_);
v___x_450_ = l_checkSortedAux___boxed__const__1;
v___x_451_ = lean_array_get_borrowed(v___x_450_, v_x_417_, v___x_438_);
v___x_452_ = lean_uint32_to_nat(v_x_418_);
v___x_464_ = l_checkSortedAux___boxed__const__1;
v___x_465_ = lean_array_get_borrowed(v___x_464_, v_x_417_, v___x_452_);
v___x_466_ = lean_unbox_uint32(v___x_451_);
v___x_467_ = lean_unbox_uint32(v___x_465_);
v___x_468_ = lean_uint32_dec_lt(v___x_466_, v___x_467_);
if v___x_468_ == 0 {
v___y_454_ = v_x_417_;
state = 3; continue;
} else {
let mut v___x_469_: *mut lean_object = core::ptr::null_mut(); 
v___x_469_ = lean_array_swap(v_x_417_, v___x_452_, v___x_438_);
v___y_454_ = v___x_469_;
state = 3; continue;
}
}
}
1 => {
v___x_426_ = l_checkSortedAux___boxed__const__1;
v_pivot_427_ = lean_array_get_borrowed(v___x_426_, v___y_425_, v___y_424_);
lean_dec(v___y_424_);
v___x_428_ = lean_unbox_uint32(v_pivot_427_);
v___x_429_ = l___private_qsort_0__partitionAux___at___00qsortAux___at___00main_spec__0_spec__0(v_x_419_, v___x_428_, v___y_425_, v_x_418_, v_x_418_);
v_fst_430_ = lean_ctor_get(v___x_429_, 0);
lean_inc(v_fst_430_);
v_snd_431_ = lean_ctor_get(v___x_429_, 1);
lean_inc(v_snd_431_);
lean_dec_ref(v___x_429_);
v___x_432_ = lean_unbox_uint32(v_fst_430_);
v_as_433_ = l_qsortAux___at___00main_spec__0(v_snd_431_, v_x_418_, v___x_432_);
v___x_434_ = lean_unbox_uint32(v_fst_430_);
lean_dec(v_fst_430_);
v___x_435_ = lean_uint32_add(v___x_434_, v___x_422_);
v_x_417_ = v_as_433_;
v_x_418_ = v___x_435_;
state = 0; continue;
}
2 => {
v___x_442_ = l_checkSortedAux___boxed__const__1;
v___x_443_ = lean_array_get_borrowed(v___x_442_, v___y_441_, v___x_438_);
v___x_444_ = l_checkSortedAux___boxed__const__1;
v___x_445_ = lean_array_get_borrowed(v___x_444_, v___y_441_, v___y_440_);
v___x_446_ = lean_unbox_uint32(v___x_443_);
v___x_447_ = lean_unbox_uint32(v___x_445_);
v___x_448_ = lean_uint32_dec_lt(v___x_446_, v___x_447_);
if v___x_448_ == 0 {
lean_dec(v___x_438_);
v___y_424_ = v___y_440_;
v___y_425_ = v___y_441_;
state = 1; continue;
} else {
let mut v___x_449_: *mut lean_object = core::ptr::null_mut(); 
v___x_449_ = lean_array_swap(v___y_441_, v___x_438_, v___y_440_);
lean_dec(v___x_438_);
v___y_424_ = v___y_440_;
v___y_425_ = v___x_449_;
state = 1; continue;
}
}
3 => {
v___x_455_ = lean_uint32_to_nat(v_x_419_);
v___x_456_ = l_checkSortedAux___boxed__const__1;
v___x_457_ = lean_array_get_borrowed(v___x_456_, v___y_454_, v___x_455_);
v___x_458_ = l_checkSortedAux___boxed__const__1;
v___x_459_ = lean_array_get_borrowed(v___x_458_, v___y_454_, v___x_452_);
v___x_460_ = lean_unbox_uint32(v___x_457_);
v___x_461_ = lean_unbox_uint32(v___x_459_);
v___x_462_ = lean_uint32_dec_lt(v___x_460_, v___x_461_);
if v___x_462_ == 0 {
lean_dec(v___x_452_);
v___y_440_ = v___x_455_;
v___y_441_ = v___y_454_;
state = 2; continue;
} else {
let mut v___x_463_: *mut lean_object = core::ptr::null_mut(); 
v___x_463_ = lean_array_swap(v___y_454_, v___x_452_, v___x_455_);
lean_dec(v___x_452_);
v___y_440_ = v___x_455_;
v___y_441_ = v___x_463_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_qsortAux___at___00main_spec__0___boxed(mut v_x_470_: *mut lean_object, mut v_x_471_: *mut lean_object, mut v_x_472_: *mut lean_object) -> *mut lean_object{
let mut v_x_421__boxed_473_: u32 = 0; let mut v_x_422__boxed_474_: u32 = 0; let mut v_res_475_: *mut lean_object = core::ptr::null_mut(); 
v_x_421__boxed_473_ = lean_unbox_uint32(v_x_471_);
lean_dec(v_x_471_);
v_x_422__boxed_474_ = lean_unbox_uint32(v_x_472_);
lean_dec(v_x_472_);
v_res_475_ = l_qsortAux___at___00main_spec__0(v_x_470_, v_x_421__boxed_473_, v_x_422__boxed_474_);
return v_res_475_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00main_spec__1___redArg(mut v_n_478_: *mut lean_object, mut v_i_479_: *mut lean_object) -> *mut lean_object{
let mut v_zero_481_: *mut lean_object = core::ptr::null_mut(); let mut v_isZero_482_: u8 = 0; let mut v___x_483_: *mut lean_object = core::ptr::null_mut(); let mut v___x_484_: *mut lean_object = core::ptr::null_mut(); let mut v_one_485_: *mut lean_object = core::ptr::null_mut(); let mut v_n_486_: *mut lean_object = core::ptr::null_mut(); let mut v___x_487_: *mut lean_object = core::ptr::null_mut(); let mut v___x_488_: *mut lean_object = core::ptr::null_mut(); let mut v___x_489_: u32 = 0; let mut v___x_490_: *mut lean_object = core::ptr::null_mut(); let mut v_xs_491_: *mut lean_object = core::ptr::null_mut(); let mut v___x_492_: u32 = 0; let mut v___x_493_: *mut lean_object = core::ptr::null_mut(); let mut v___x_494_: *mut lean_object = core::ptr::null_mut(); let mut v___x_495_: u32 = 0; let mut v_xs_496_: *mut lean_object = core::ptr::null_mut(); let mut v___x_497_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v_zero_481_ = lean_unsigned_to_nat(0);
v_isZero_482_ = lean_nat_dec_eq(v_i_479_, v_zero_481_);
if v_isZero_482_ == 1 {
let mut v___x_483_: *mut lean_object = core::ptr::null_mut(); let mut v___x_484_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_i_479_);
v___x_483_ = lean_box(0);
v___x_484_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_484_, 0, v___x_483_);
return v___x_484_;
} else {
let mut v_one_485_: *mut lean_object = core::ptr::null_mut(); let mut v_n_486_: *mut lean_object = core::ptr::null_mut(); let mut v___x_487_: *mut lean_object = core::ptr::null_mut(); let mut v___x_488_: *mut lean_object = core::ptr::null_mut(); let mut v___x_489_: u32 = 0; let mut v___x_490_: *mut lean_object = core::ptr::null_mut(); let mut v_xs_491_: *mut lean_object = core::ptr::null_mut(); let mut v___x_492_: u32 = 0; let mut v___x_493_: *mut lean_object = core::ptr::null_mut(); let mut v___x_494_: *mut lean_object = core::ptr::null_mut(); let mut v___x_495_: u32 = 0; let mut v_xs_496_: *mut lean_object = core::ptr::null_mut(); let mut v___x_497_: *mut lean_object = core::ptr::null_mut(); 
v_one_485_ = lean_unsigned_to_nat(1);
v_n_486_ = lean_nat_sub(v_i_479_, v_one_485_);
lean_dec(v_i_479_);
v___x_487_ = lean_nat_sub(v_n_478_, v_n_486_);
v___x_488_ = lean_nat_sub(v___x_487_, v_one_485_);
lean_dec(v___x_487_);
v___x_489_ = lean_uint32_of_nat(v___x_488_);
v___x_490_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00main_spec__1___redArg___closed__0;
v_xs_491_ = l_mkRandomArray(v___x_488_, v___x_489_, v___x_490_);
v___x_492_ = 0;
v___x_493_ = lean_array_get_size(v_xs_491_);
v___x_494_ = lean_nat_sub(v___x_493_, v_one_485_);
v___x_495_ = lean_uint32_of_nat(v___x_494_);
lean_dec(v___x_494_);
v_xs_496_ = l_qsortAux___at___00main_spec__0(v_xs_491_, v___x_492_, v___x_495_);
v___x_497_ = l_checkSortedAux(v_xs_496_, v_zero_481_);
lean_dec_ref(v_xs_496_);
if lean_obj_tag(v___x_497_) == 0 {
lean_dec_ref_known(v___x_497_, 1);
v_i_479_ = v_n_486_;
state = 0; continue;
} else {
lean_dec(v_n_486_);
return v___x_497_;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00main_spec__1___redArg___boxed(mut v_n_499_: *mut lean_object, mut v_i_500_: *mut lean_object, mut v___y_501_: *mut lean_object) -> *mut lean_object{
let mut v_res_502_: *mut lean_object = core::ptr::null_mut(); 
v_res_502_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00main_spec__1___redArg(v_n_499_, v_i_500_);
lean_dec(v_n_499_);
return v_res_502_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00main_spec__2___redArg(mut v_n_503_: *mut lean_object, mut v_i_504_: *mut lean_object) -> *mut lean_object{
let mut v_zero_506_: *mut lean_object = core::ptr::null_mut(); let mut v_isZero_507_: u8 = 0; let mut v___x_508_: *mut lean_object = core::ptr::null_mut(); let mut v___x_509_: *mut lean_object = core::ptr::null_mut(); let mut v___x_510_: *mut lean_object = core::ptr::null_mut(); let mut v_one_511_: *mut lean_object = core::ptr::null_mut(); let mut v_n_512_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v_zero_506_ = lean_unsigned_to_nat(0);
v_isZero_507_ = lean_nat_dec_eq(v_i_504_, v_zero_506_);
if v_isZero_507_ == 1 {
let mut v___x_508_: *mut lean_object = core::ptr::null_mut(); let mut v___x_509_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_i_504_);
lean_dec(v_n_503_);
v___x_508_ = lean_box(0);
v___x_509_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_509_, 0, v___x_508_);
return v___x_509_;
} else {
let mut v___x_510_: *mut lean_object = core::ptr::null_mut(); 
lean_inc(v_n_503_);
v___x_510_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00main_spec__1___redArg(v_n_503_, v_n_503_);
if lean_obj_tag(v___x_510_) == 0 {
let mut v_one_511_: *mut lean_object = core::ptr::null_mut(); let mut v_n_512_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_510_, 1);
v_one_511_ = lean_unsigned_to_nat(1);
v_n_512_ = lean_nat_sub(v_i_504_, v_one_511_);
lean_dec(v_i_504_);
v_i_504_ = v_n_512_;
state = 0; continue;
} else {
lean_dec(v_i_504_);
lean_dec(v_n_503_);
return v___x_510_;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00main_spec__2___redArg___boxed(mut v_n_514_: *mut lean_object, mut v_i_515_: *mut lean_object, mut v___y_516_: *mut lean_object) -> *mut lean_object{
let mut v_res_517_: *mut lean_object = core::ptr::null_mut(); 
v_res_517_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00main_spec__2___redArg(v_n_514_, v_i_515_);
return v_res_517_;
}
#[no_mangle] pub unsafe extern "C" fn _lean_main(mut v_xs_519_: *mut lean_object) -> *mut lean_object{
let mut v___x_521_: *mut lean_object = core::ptr::null_mut(); let mut v___x_522_: *mut lean_object = core::ptr::null_mut(); let mut v___x_523_: *mut lean_object = core::ptr::null_mut(); let mut v___x_524_: *mut lean_object = core::ptr::null_mut(); let mut v___x_525_: *mut lean_object = core::ptr::null_mut(); let mut v_n_526_: *mut lean_object = core::ptr::null_mut(); let mut v___x_527_: *mut lean_object = core::ptr::null_mut(); 
v___x_521_ = l_main___closed__0;
v___x_522_ = l_List_head_x21___redArg(v___x_521_, v_xs_519_);
lean_dec(v_xs_519_);
v___x_523_ = lean_unsigned_to_nat(0);
v___x_524_ = lean_string_utf8_byte_size(v___x_522_);
v___x_525_ = lean_alloc_ctor(0, 3, (0) as u32);
lean_ctor_set(v___x_525_, 0, v___x_522_);
lean_ctor_set(v___x_525_, 1, v___x_523_);
lean_ctor_set(v___x_525_, 2, v___x_524_);
v_n_526_ = l_String_Slice_toNat_x21(v___x_525_);
lean_dec_ref_known(v___x_525_, 3);
lean_inc(v_n_526_);
v___x_527_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00main_spec__2___redArg(v_n_526_, v_n_526_);
return v___x_527_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___boxed(mut v_xs_528_: *mut lean_object, mut v_a_529_: *mut lean_object) -> *mut lean_object{
let mut v_res_530_: *mut lean_object = core::ptr::null_mut(); 
v_res_530_ = _lean_main(v_xs_528_);
return v_res_530_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00main_spec__1(mut v_n_531_: *mut lean_object, mut v_i_532_: *mut lean_object, mut v_a_533_: *mut lean_object) -> *mut lean_object{
let mut v___x_535_: *mut lean_object = core::ptr::null_mut(); 
v___x_535_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00main_spec__1___redArg(v_n_531_, v_i_532_);
return v___x_535_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00main_spec__1___boxed(mut v_n_536_: *mut lean_object, mut v_i_537_: *mut lean_object, mut v_a_538_: *mut lean_object, mut v___y_539_: *mut lean_object) -> *mut lean_object{
let mut v_res_540_: *mut lean_object = core::ptr::null_mut(); 
v_res_540_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00main_spec__1(v_n_536_, v_i_537_, v_a_538_);
lean_dec(v_n_536_);
return v_res_540_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00main_spec__2(mut v_n_541_: *mut lean_object, mut v_n_542_: *mut lean_object, mut v_i_543_: *mut lean_object, mut v_a_544_: *mut lean_object) -> *mut lean_object{
let mut v___x_546_: *mut lean_object = core::ptr::null_mut(); 
v___x_546_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00main_spec__2___redArg(v_n_541_, v_i_543_);
return v___x_546_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00main_spec__2___boxed(mut v_n_547_: *mut lean_object, mut v_n_548_: *mut lean_object, mut v_i_549_: *mut lean_object, mut v_a_550_: *mut lean_object, mut v___y_551_: *mut lean_object) -> *mut lean_object{
let mut v_res_552_: *mut lean_object = core::ptr::null_mut(); 
v_res_552_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00main_spec__2(v_n_547_, v_n_548_, v_i_549_, v_a_550_);
lean_dec(v_n_548_);
return v_res_552_;
}
extern "C" { fn initialize_Init(builtin: u8) -> *mut lean_object; }
static mut _G_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn initialize_qsort(builtin: u8) -> *mut lean_object {
let mut res: *mut lean_object = core::ptr::null_mut();
if _G_initialized { return lean_io_result_mk_ok(lean_box(0)); }
_G_initialized = true;
res = initialize_Init(builtin);
if lean_io_result_is_error(res) { return res; }
lean_dec_ref(res);
l_checkSortedAux___boxed__const__1 = _init_l_checkSortedAux___boxed__const__1();
lean_mark_persistent(l_checkSortedAux___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
unsafe extern "C" fn run_main(argc: core::ffi::c_int, argv: *mut *mut core::ffi::c_char) -> *mut lean_object {
    let mut args_list = lean_box(0);
            let mut i = argc;
            while i > 1 {
                i -= 1;
                let arg_str = lean_mk_string(*argv.add(i as usize));
                let mut fields = [arg_str, args_list];
                args_list = lean_alloc_ctor(1, 2, 0);
                lean_ctor_set(args_list, 0, arg_str);
                lean_ctor_set(args_list, 1, fields[1]);
            }
            return _lean_main(args_list);
}
#[no_mangle]
pub unsafe extern "C" fn main(argc: core::ffi::c_int, mut argv: *mut *mut core::ffi::c_char) -> core::ffi::c_int {
  argv = lean_setup_args(argc, argv);
  lean_initialize_runtime_module();
  let res = initialize_qsort(1 /* builtin */);
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
