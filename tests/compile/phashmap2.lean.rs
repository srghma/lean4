// Lean compiler output
// Module: phashmap2
// Imports: Init Init Lean.Data.PersistentHashMap Lean.Data.Format
use lean_runtime::generated_abi::*;
use lean_init::Init::*;
use lean_lean::Lean::Data::PersistentHashMap::*;
use lean_lean::Lean::Data::Format::*;
use lean_init::Init::Data::UInt::BasicAux::*;
use lean_init::Init::Data::UInt::Basic::*;
use lean_init::Init::Prelude::*;
use lean_init::Init::Data::Array::Set::*;
use lean_init::Init::Data::Array::Basic::*;
use lean_init::Init::Data::Repr::*;
use lean_init::Init::Data::String::Bootstrap::*;
use lean_init::Init::Data::Int::Basic::*;
use lean_init::Init::System::IO::*;
use lean_init::Init::Data::ToString::Basic::*;
extern "C" {
    fn lean_array_push(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_string_push(_: *mut lean_object, _: u32) -> *mut lean_object;
    fn lean_get_stdout() -> *mut lean_object;
    fn lean_string_append(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
}
pub static l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__0_value: lean_string_object<3> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [99, 64, 0]};
static mut l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__0: *mut lean_object = core::ptr::addr_of!(l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__0_value) as *mut lean_object;
pub static l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__1_value: lean_ctor_object<1> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*1 + 0) as u16, m_other: 1, m_tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__0_value) as *mut lean_object] };
static mut l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__1: *mut lean_object = core::ptr::addr_of!(l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__1_value) as *mut lean_object;
pub static l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__2_value: lean_string_object<5> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [32, 61, 62, 32, 0]};
static mut l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__2: *mut lean_object = core::ptr::addr_of!(l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__2_value) as *mut lean_object;
pub static l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__3_value: lean_ctor_object<1> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*1 + 0) as u16, m_other: 1, m_tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__2_value) as *mut lean_object] };
static mut l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__3: *mut lean_object = core::ptr::addr_of!(l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__3_value) as *mut lean_object;
pub static l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__4_value: lean_string_object<2> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__4: *mut lean_object = core::ptr::addr_of!(l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__4_value) as *mut lean_object;
pub static l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__5_value: lean_string_object<2> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__5: *mut lean_object = core::ptr::addr_of!(l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__5_value) as *mut lean_object;
static mut l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__6_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__6: *mut lean_object = core::ptr::null_mut();
static mut l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__7_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__7: *mut lean_object = core::ptr::null_mut();
pub static l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__8_value: lean_ctor_object<1> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*1 + 0) as u16, m_other: 1, m_tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__4_value) as *mut lean_object] };
static mut l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__8: *mut lean_object = core::ptr::addr_of!(l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__8_value) as *mut lean_object;
pub static l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__9_value: lean_ctor_object<1> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*1 + 0) as u16, m_other: 1, m_tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__5_value) as *mut lean_object] };
static mut l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__9: *mut lean_object = core::ptr::addr_of!(l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__9_value) as *mut lean_object;
pub static l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__10_value: lean_string_object<2> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [44, 0]};
static mut l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__10: *mut lean_object = core::ptr::addr_of!(l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__10_value) as *mut lean_object;
pub static l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__11_value: lean_ctor_object<1> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*1 + 0) as u16, m_other: 1, m_tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__10_value) as *mut lean_object] };
static mut l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__11: *mut lean_object = core::ptr::addr_of!(l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__11_value) as *mut lean_object;
pub static l_formatMap___closed__0_value: lean_string_object<2> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [91, 0]};
static mut l_formatMap___closed__0: *mut lean_object = core::ptr::addr_of!(l_formatMap___closed__0_value) as *mut lean_object;
pub static l_formatMap___closed__1_value: lean_string_object<2> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l_formatMap___closed__1: *mut lean_object = core::ptr::addr_of!(l_formatMap___closed__1_value) as *mut lean_object;
static mut l_formatMap___closed__2_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_formatMap___closed__2: *mut lean_object = core::ptr::null_mut();
static mut l_formatMap___closed__3_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_formatMap___closed__3: *mut lean_object = core::ptr::null_mut();
pub static l_formatMap___closed__4_value: lean_ctor_object<1> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*1 + 0) as u16, m_other: 1, m_tag: 3 }, m_objs: [core::ptr::addr_of!(l_formatMap___closed__0_value) as *mut lean_object] };
static mut l_formatMap___closed__4: *mut lean_object = core::ptr::addr_of!(l_formatMap___closed__4_value) as *mut lean_object;
pub static l_formatMap___closed__5_value: lean_ctor_object<1> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*1 + 0) as u16, m_other: 1, m_tag: 3 }, m_objs: [core::ptr::addr_of!(l_formatMap___closed__1_value) as *mut lean_object] };
static mut l_formatMap___closed__5: *mut lean_object = core::ptr::addr_of!(l_formatMap___closed__5_value) as *mut lean_object;
pub static l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__0_spec__0___redArg___closed__0_value: lean_string_object<7> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [60, 110, 117, 108, 108, 62, 0]};
static mut l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__0_spec__0___redArg___closed__0: *mut lean_object = core::ptr::addr_of!(l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__0_spec__0___redArg___closed__0_value) as *mut lean_object;
pub static l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__0_spec__0___redArg___closed__1_value: lean_ctor_object<1> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*1 + 0) as u16, m_other: 1, m_tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__0_spec__0___redArg___closed__0_value) as *mut lean_object] };
static mut l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__0_spec__0___redArg___closed__1: *mut lean_object = core::ptr::addr_of!(l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__0_spec__0___redArg___closed__1_value) as *mut lean_object;
static mut l_Lean_PersistentHashMap_empty___at___00main_spec__2___closed__0_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_PersistentHashMap_empty___at___00main_spec__2___closed__0: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_empty___at___00main_spec__2___closed__1_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_PersistentHashMap_empty___at___00main_spec__2___closed__1: *mut lean_object = core::ptr::null_mut();
pub static l_Lean_PersistentHashMap_stats___at___00main_spec__4___redArg___closed__0_value: lean_ctor_object<4> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*4 + 0) as u16, m_other: 4, m_tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut lean_object,((( 0 as usize) << 1) | 1) as *mut lean_object,((( 0 as usize) << 1) | 1) as *mut lean_object,((( 0 as usize) << 1) | 1) as *mut lean_object] };
static mut l_Lean_PersistentHashMap_stats___at___00main_spec__4___redArg___closed__0: *mut lean_object = core::ptr::addr_of!(l_Lean_PersistentHashMap_stats___at___00main_spec__4___redArg___closed__0_value) as *mut lean_object;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00main_spec__7_spec__11___redArg___closed__0_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00main_spec__7_spec__11___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00main_spec__7_spec__11___redArg___closed__1_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00main_spec__7_spec__11___redArg___closed__1: usize = 0;
pub static l_IO_println___at___00main_spec__1___closed__0_value: lean_string_object<5> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 111, 110, 101, 0]};
static mut l_IO_println___at___00main_spec__1___closed__0: *mut lean_object = core::ptr::addr_of!(l_IO_println___at___00main_spec__1___closed__0_value) as *mut lean_object;
pub static l_IO_println___at___00main_spec__1___closed__1_value: lean_string_object<7> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [40, 115, 111, 109, 101, 32, 0]};
static mut l_IO_println___at___00main_spec__1___closed__1: *mut lean_object = core::ptr::addr_of!(l_IO_println___at___00main_spec__1___closed__1_value) as *mut lean_object;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__3_spec__5___redArg___closed__0_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__3_spec__5___redArg___closed__0: *mut lean_object = core::ptr::null_mut();
pub static l_main___closed__0_value: lean_array_object<3> = lean_array_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut lean_object>()*3) as u16, m_other: 0, m_tag: 246 }, m_size: 3, m_capacity: 3, m_data: [((( 1 as usize) << 1) | 1) as *mut lean_object,((( 2 as usize) << 1) | 1) as *mut lean_object,((( 3 as usize) << 1) | 1) as *mut lean_object] };
static mut l_main___closed__0: *mut lean_object = core::ptr::addr_of!(l_main___closed__0_value) as *mut lean_object;
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
static mut l_main___closed__11_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__11: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__12_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__12: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__13_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__13: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__14_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__14: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__15_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__15: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__16_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__16: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__17_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__17: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__18_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__18: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__19_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__19: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__20_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__20: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__21_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__21: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__22_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__22: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__23_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__23: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__24_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__24: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__25_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__25: *mut lean_object = core::ptr::null_mut();
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
2 => {
v___x_138_ = l_Nat_reprFast(v_key_133_);
v___x_139_ = lean_alloc_ctor(3, 1, (0) as u32);
lean_ctor_set(v___x_139_, 0, v___x_138_);
v___x_140_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__3;
if v_isShared_137_ == 0 {
lean_ctor_set_tag(v___x_136_, 5);
lean_ctor_set(v___x_136_, 1, v___x_140_);
lean_ctor_set(v___x_136_, 0, v___x_139_);
v___x_142_ = v___x_136_;
state = 3; continue;
} else {
v_reuseFailAlloc_156_ = lean_alloc_ctor(5, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v___x_139_);
lean_ctor_set(v_reuseFailAlloc_156_, 1, v___x_140_);
v___x_142_ = v_reuseFailAlloc_156_;
state = 3; continue;
}
}
3 => {
v___x_143_ = l_Nat_reprFast(v_val_134_);
v___x_144_ = lean_alloc_ctor(3, 1, (0) as u32);
lean_ctor_set(v___x_144_, 0, v___x_143_);
v___x_145_ = lean_alloc_ctor(5, 2, (0) as u32);
lean_ctor_set(v___x_145_, 0, v___x_142_);
lean_ctor_set(v___x_145_, 1, v___x_144_);
v___x_146_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__7), core::ptr::addr_of_mut!(l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__7_once), _init_l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__7);
v___x_147_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__8;
v___x_148_ = lean_alloc_ctor(5, 2, (0) as u32);
lean_ctor_set(v___x_148_, 0, v___x_147_);
lean_ctor_set(v___x_148_, 1, v___x_145_);
v___x_149_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__9;
v___x_150_ = lean_alloc_ctor(5, 2, (0) as u32);
lean_ctor_set(v___x_150_, 0, v___x_148_);
lean_ctor_set(v___x_150_, 1, v___x_149_);
v___x_151_ = lean_alloc_ctor(4, 2, (0) as u32);
lean_ctor_set(v___x_151_, 0, v___x_146_);
lean_ctor_set(v___x_151_, 1, v___x_150_);
v___x_152_ = 0;
v___x_153_ = lean_alloc_ctor(6, 1, (1) as u32);
lean_ctor_set(v___x_153_, 0, v___x_151_);
lean_ctor_set_uint8(v___x_153_, (core::mem::size_of::<*mut lean_object>()*1) as u32, v___x_152_);
v___x_154_ = lean_alloc_ctor(5, 2, (0) as u32);
lean_ctor_set(v___x_154_, 0, v___y_132_);
lean_ctor_set(v___x_154_, 1, v___x_153_);
v_j_123_ = v_n_128_;
v_a_124_ = v___x_154_;
state = 0; continue;
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
v___x_211_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__0_spec__0___redArg___closed__1;
v___x_212_ = lean_alloc_ctor(5, 2, (0) as u32);
lean_ctor_set(v___x_212_, 0, v___y_181_);
lean_ctor_set(v___x_212_, 1, v___x_211_);
v___x_213_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__0_spec__0___redArg(v_es_170_, v_n_171_, v_n_177_, v___x_212_);
return v___x_213_;
}
}
}
2 => {
v___x_187_ = l_Nat_reprFast(v_key_182_);
v___x_188_ = lean_alloc_ctor(3, 1, (0) as u32);
lean_ctor_set(v___x_188_, 0, v___x_187_);
v___x_189_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__3;
if v_isShared_186_ == 0 {
lean_ctor_set_tag(v___x_185_, 5);
lean_ctor_set(v___x_185_, 1, v___x_189_);
lean_ctor_set(v___x_185_, 0, v___x_188_);
v___x_191_ = v___x_185_;
state = 3; continue;
} else {
v_reuseFailAlloc_205_ = lean_alloc_ctor(5, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v___x_188_);
lean_ctor_set(v_reuseFailAlloc_205_, 1, v___x_189_);
v___x_191_ = v_reuseFailAlloc_205_;
state = 3; continue;
}
}
3 => {
v___x_192_ = l_Nat_reprFast(v_val_183_);
v___x_193_ = lean_alloc_ctor(3, 1, (0) as u32);
lean_ctor_set(v___x_193_, 0, v___x_192_);
v___x_194_ = lean_alloc_ctor(5, 2, (0) as u32);
lean_ctor_set(v___x_194_, 0, v___x_191_);
lean_ctor_set(v___x_194_, 1, v___x_193_);
v___x_195_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__7), core::ptr::addr_of_mut!(l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__7_once), _init_l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__7);
v___x_196_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__8;
v___x_197_ = lean_alloc_ctor(5, 2, (0) as u32);
lean_ctor_set(v___x_197_, 0, v___x_196_);
lean_ctor_set(v___x_197_, 1, v___x_194_);
v___x_198_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__9;
v___x_199_ = lean_alloc_ctor(5, 2, (0) as u32);
lean_ctor_set(v___x_199_, 0, v___x_197_);
lean_ctor_set(v___x_199_, 1, v___x_198_);
v___x_200_ = lean_alloc_ctor(4, 2, (0) as u32);
lean_ctor_set(v___x_200_, 0, v___x_195_);
lean_ctor_set(v___x_200_, 1, v___x_199_);
v___x_201_ = 0;
v___x_202_ = lean_alloc_ctor(6, 1, (1) as u32);
lean_ctor_set(v___x_202_, 0, v___x_200_);
lean_ctor_set_uint8(v___x_202_, (core::mem::size_of::<*mut lean_object>()*1) as u32, v___x_201_);
v___x_203_ = lean_alloc_ctor(5, 2, (0) as u32);
lean_ctor_set(v___x_203_, 0, v___y_181_);
lean_ctor_set(v___x_203_, 1, v___x_202_);
v___x_204_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__0_spec__0___redArg(v_es_170_, v_n_171_, v_n_177_, v___x_203_);
return v___x_204_;
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
v_reuseFailAlloc_249_ = lean_alloc_ctor(5, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v___x_241_);
lean_ctor_set(v_reuseFailAlloc_249_, 1, v___x_239_);
v___x_243_ = v_reuseFailAlloc_249_;
state = 2; continue;
}
}
2 => {
v___x_244_ = l_formatMap___closed__5;
v___x_245_ = lean_alloc_ctor(5, 2, (0) as u32);
lean_ctor_set(v___x_245_, 0, v___x_243_);
lean_ctor_set(v___x_245_, 1, v___x_244_);
v___x_246_ = lean_alloc_ctor(4, 2, (0) as u32);
lean_ctor_set(v___x_246_, 0, v___x_240_);
lean_ctor_set(v___x_246_, 1, v___x_245_);
v___x_247_ = 0;
v___x_248_ = lean_alloc_ctor(6, 1, (1) as u32);
lean_ctor_set(v___x_248_, 0, v___x_246_);
lean_ctor_set_uint8(v___x_248_, (core::mem::size_of::<*mut lean_object>()*1) as u32, v___x_247_);
return v___x_248_;
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
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_PersistentHashMap_empty___at___00main_spec__2___closed__0() -> *mut lean_object{
let mut v___x_313_: *mut lean_object = core::ptr::null_mut(); 
v___x_313_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_313_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_PersistentHashMap_empty___at___00main_spec__2___closed__1() -> *mut lean_object{
let mut v___x_314_: *mut lean_object = core::ptr::null_mut(); let mut v___x_315_: *mut lean_object = core::ptr::null_mut(); 
v___x_314_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00main_spec__2___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00main_spec__2___closed__0_once), _init_l_Lean_PersistentHashMap_empty___at___00main_spec__2___closed__0);
v___x_315_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_315_, 0, v___x_314_);
return v___x_315_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_empty___at___00main_spec__2(mut v_00_u03b2_316_: *mut lean_object) -> *mut lean_object{
let mut v___x_317_: *mut lean_object = core::ptr::null_mut(); 
v___x_317_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00main_spec__2___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00main_spec__2___closed__1_once), _init_l_Lean_PersistentHashMap_empty___at___00main_spec__2___closed__1);
return v___x_317_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_stats___at___00main_spec__4___redArg(mut v_m_320_: *mut lean_object) -> *mut lean_object{
let mut v___x_321_: *mut lean_object = core::ptr::null_mut(); let mut v___x_322_: *mut lean_object = core::ptr::null_mut(); let mut v___x_323_: *mut lean_object = core::ptr::null_mut(); 
v___x_321_ = l_Lean_PersistentHashMap_stats___at___00main_spec__4___redArg___closed__0;
v___x_322_ = lean_unsigned_to_nat(1);
v___x_323_ = l_Lean_PersistentHashMap_collectStats___redArg(v_m_320_, v___x_321_, v___x_322_);
return v___x_323_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_stats___at___00main_spec__4___redArg___boxed(mut v_m_324_: *mut lean_object) -> *mut lean_object{
let mut v_res_325_: *mut lean_object = core::ptr::null_mut(); 
v_res_325_ = l_Lean_PersistentHashMap_stats___at___00main_spec__4___redArg(v_m_324_);
lean_dec_ref(v_m_324_);
return v_res_325_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_stats___at___00main_spec__4(mut v_00_u03b2_326_: *mut lean_object, mut v_m_327_: *mut lean_object) -> *mut lean_object{
let mut v___x_328_: *mut lean_object = core::ptr::null_mut(); 
v___x_328_ = l_Lean_PersistentHashMap_stats___at___00main_spec__4___redArg(v_m_327_);
return v___x_328_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_stats___at___00main_spec__4___boxed(mut v_00_u03b2_329_: *mut lean_object, mut v_m_330_: *mut lean_object) -> *mut lean_object{
let mut v_res_331_: *mut lean_object = core::ptr::null_mut(); 
v_res_331_ = l_Lean_PersistentHashMap_stats___at___00main_spec__4(v_00_u03b2_329_, v_m_330_);
lean_dec_ref(v_m_330_);
return v_res_331_;
}
#[no_mangle] pub unsafe extern "C" fn l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00main_spec__0_spec__0_spec__3(mut v_xs_332_: *mut lean_object, mut v_v_333_: *mut lean_object, mut v_i_334_: *mut lean_object) -> *mut lean_object{
let mut v___x_335_: *mut lean_object = core::ptr::null_mut(); let mut v___x_336_: u8 = 0; let mut v___x_337_: *mut lean_object = core::ptr::null_mut(); let mut v___x_338_: *mut lean_object = core::ptr::null_mut(); let mut v___x_339_: u8 = 0; let mut v___x_340_: *mut lean_object = core::ptr::null_mut(); let mut v___x_341_: *mut lean_object = core::ptr::null_mut(); let mut v___x_343_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_335_ = lean_array_get_size(v_xs_332_);
v___x_336_ = lean_nat_dec_lt(v_i_334_, v___x_335_);
if v___x_336_ == 0 {
lean_dec(v_i_334_);
v___x_337_ = lean_box(0);
return v___x_337_;
} else {
v___x_338_ = lean_array_fget_borrowed(v_xs_332_, v_i_334_);
v___x_339_ = lean_nat_dec_eq(v___x_338_, v_v_333_);
if v___x_339_ == 0 {
v___x_340_ = lean_unsigned_to_nat(1);
v___x_341_ = lean_nat_add(v_i_334_, v___x_340_);
lean_dec(v_i_334_);
v_i_334_ = v___x_341_;
state = 0; continue;
} else {
v___x_343_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v___x_343_, 0, v_i_334_);
return v___x_343_;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00main_spec__0_spec__0_spec__3___boxed(mut v_xs_344_: *mut lean_object, mut v_v_345_: *mut lean_object, mut v_i_346_: *mut lean_object) -> *mut lean_object{
let mut v_res_347_: *mut lean_object = core::ptr::null_mut(); 
v_res_347_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00main_spec__0_spec__0_spec__3(v_xs_344_, v_v_345_, v_i_346_);
lean_dec(v_v_345_);
lean_dec_ref(v_xs_344_);
return v_res_347_;
}
#[no_mangle] pub unsafe extern "C" fn l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00main_spec__0_spec__0(mut v_xs_348_: *mut lean_object, mut v_v_349_: *mut lean_object) -> *mut lean_object{
let mut v___x_350_: *mut lean_object = core::ptr::null_mut(); let mut v___x_351_: *mut lean_object = core::ptr::null_mut(); 
v___x_350_ = lean_unsigned_to_nat(0);
v___x_351_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00main_spec__0_spec__0_spec__3(v_xs_348_, v_v_349_, v___x_350_);
return v___x_351_;
}
#[no_mangle] pub unsafe extern "C" fn l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00main_spec__0_spec__0___boxed(mut v_xs_352_: *mut lean_object, mut v_v_353_: *mut lean_object) -> *mut lean_object{
let mut v_res_354_: *mut lean_object = core::ptr::null_mut(); 
v_res_354_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00main_spec__0_spec__0(v_xs_352_, v_v_353_);
lean_dec(v_v_353_);
lean_dec_ref(v_xs_352_);
return v_res_354_;
}
#[no_mangle] pub unsafe extern "C" fn l_Array_idxOf_x3f___at___00main_spec__0(mut v_xs_355_: *mut lean_object, mut v_v_356_: *mut lean_object) -> *mut lean_object{
let mut v___x_357_: *mut lean_object = core::ptr::null_mut(); let mut v___x_358_: *mut lean_object = core::ptr::null_mut(); let mut v_val_359_: *mut lean_object = core::ptr::null_mut(); let mut v___x_361_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_362_: u8 = 0; let mut v___x_364_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_365_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_366_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_357_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00main_spec__0_spec__0(v_xs_355_, v_v_356_);
if lean_obj_tag(v___x_357_) == 0 {
v___x_358_ = lean_box(0);
return v___x_358_;
} else {
v_val_359_ = lean_ctor_get(v___x_357_, 0);
v_isSharedCheck_366_ = (!lean_is_exclusive(v___x_357_)) as u8;
if v_isSharedCheck_366_ == 0 {
v___x_361_ = v___x_357_;
v_isShared_362_ = v_isSharedCheck_366_;
state = 1; continue;
} else {
lean_inc(v_val_359_);
lean_dec(v___x_357_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_366_;
state = 1; continue;
}
}
}
1 => {
if v_isShared_362_ == 0 {
v___x_364_ = v___x_361_;
state = 2; continue;
} else {
v_reuseFailAlloc_365_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_val_359_);
v___x_364_ = v_reuseFailAlloc_365_;
state = 2; continue;
}
}
2 => {
return v___x_364_;
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Array_idxOf_x3f___at___00main_spec__0___boxed(mut v_xs_367_: *mut lean_object, mut v_v_368_: *mut lean_object) -> *mut lean_object{
let mut v_res_369_: *mut lean_object = core::ptr::null_mut(); 
v_res_369_ = l_Array_idxOf_x3f___at___00main_spec__0(v_xs_367_, v_v_368_);
lean_dec(v_v_368_);
lean_dec_ref(v_xs_367_);
return v_res_369_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00main_spec__7_spec__11_spec__15___redArg(mut v_keys_370_: *mut lean_object, mut v_vals_371_: *mut lean_object, mut v_i_372_: *mut lean_object, mut v_k_373_: *mut lean_object) -> *mut lean_object{
let mut v___x_374_: *mut lean_object = core::ptr::null_mut(); let mut v___x_375_: u8 = 0; let mut v___x_376_: *mut lean_object = core::ptr::null_mut(); let mut v_k_x27_377_: *mut lean_object = core::ptr::null_mut(); let mut v___x_378_: u8 = 0; let mut v___x_379_: *mut lean_object = core::ptr::null_mut(); let mut v___x_380_: *mut lean_object = core::ptr::null_mut(); let mut v___x_382_: *mut lean_object = core::ptr::null_mut(); let mut v___x_383_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_374_ = lean_array_get_size(v_keys_370_);
v___x_375_ = lean_nat_dec_lt(v_i_372_, v___x_374_);
if v___x_375_ == 0 {
lean_dec(v_i_372_);
v___x_376_ = lean_box(0);
return v___x_376_;
} else {
v_k_x27_377_ = lean_array_fget_borrowed(v_keys_370_, v_i_372_);
v___x_378_ = lean_nat_dec_eq(v_k_373_, v_k_x27_377_);
if v___x_378_ == 0 {
v___x_379_ = lean_unsigned_to_nat(1);
v___x_380_ = lean_nat_add(v_i_372_, v___x_379_);
lean_dec(v_i_372_);
v_i_372_ = v___x_380_;
state = 0; continue;
} else {
v___x_382_ = lean_array_fget_borrowed(v_vals_371_, v_i_372_);
lean_dec(v_i_372_);
lean_inc(v___x_382_);
v___x_383_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v___x_383_, 0, v___x_382_);
return v___x_383_;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00main_spec__7_spec__11_spec__15___redArg___boxed(mut v_keys_384_: *mut lean_object, mut v_vals_385_: *mut lean_object, mut v_i_386_: *mut lean_object, mut v_k_387_: *mut lean_object) -> *mut lean_object{
let mut v_res_388_: *mut lean_object = core::ptr::null_mut(); 
v_res_388_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00main_spec__7_spec__11_spec__15___redArg(v_keys_384_, v_vals_385_, v_i_386_, v_k_387_);
lean_dec(v_k_387_);
lean_dec_ref(v_vals_385_);
lean_dec_ref(v_keys_384_);
return v_res_388_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00main_spec__7_spec__11___redArg___closed__0() -> usize{
let mut v___x_389_: usize = 0; let mut v___x_390_: usize = 0; let mut v___x_391_: usize = 0; 
v___x_389_ = 5usize;
v___x_390_ = 1usize;
v___x_391_ = lean_usize_shift_left(v___x_390_, v___x_389_);
return v___x_391_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00main_spec__7_spec__11___redArg___closed__1() -> usize{
let mut v___x_392_: usize = 0; let mut v___x_393_: usize = 0; let mut v___x_394_: usize = 0; 
v___x_392_ = 1usize;
v___x_393_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00main_spec__7_spec__11___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00main_spec__7_spec__11___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00main_spec__7_spec__11___redArg___closed__0);
v___x_394_ = lean_usize_sub(v___x_393_, v___x_392_);
return v___x_394_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00main_spec__7_spec__11___redArg(mut v_x_395_: *mut lean_object, mut v_x_396_: usize, mut v_x_397_: *mut lean_object) -> *mut lean_object{
let mut v_es_398_: *mut lean_object = core::ptr::null_mut(); let mut v___x_399_: *mut lean_object = core::ptr::null_mut(); let mut v___x_400_: usize = 0; let mut v___x_401_: usize = 0; let mut v___x_402_: usize = 0; let mut v_j_403_: *mut lean_object = core::ptr::null_mut(); let mut v___x_404_: *mut lean_object = core::ptr::null_mut(); let mut v_key_405_: *mut lean_object = core::ptr::null_mut(); let mut v_val_406_: *mut lean_object = core::ptr::null_mut(); let mut v___x_407_: u8 = 0; let mut v___x_408_: *mut lean_object = core::ptr::null_mut(); let mut v___x_409_: *mut lean_object = core::ptr::null_mut(); let mut v_node_410_: *mut lean_object = core::ptr::null_mut(); let mut v___x_411_: usize = 0; let mut v___x_413_: *mut lean_object = core::ptr::null_mut(); let mut v_ks_414_: *mut lean_object = core::ptr::null_mut(); let mut v_vs_415_: *mut lean_object = core::ptr::null_mut(); let mut v___x_416_: *mut lean_object = core::ptr::null_mut(); let mut v___x_417_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_x_395_) == 0 {
v_es_398_ = lean_ctor_get(v_x_395_, 0);
v___x_399_ = lean_box(2);
v___x_400_ = 5usize;
v___x_401_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00main_spec__7_spec__11___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00main_spec__7_spec__11___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00main_spec__7_spec__11___redArg___closed__1);
v___x_402_ = lean_usize_land(v_x_396_, v___x_401_);
v_j_403_ = lean_usize_to_nat(v___x_402_);
v___x_404_ = lean_array_get_borrowed(v___x_399_, v_es_398_, v_j_403_);
lean_dec(v_j_403_);
match lean_obj_tag(v___x_404_)
{
0 => {
v_key_405_ = lean_ctor_get(v___x_404_, 0);
v_val_406_ = lean_ctor_get(v___x_404_, 1);
v___x_407_ = lean_nat_dec_eq(v_x_397_, v_key_405_);
if v___x_407_ == 0 {
v___x_408_ = lean_box(0);
return v___x_408_;
} else {
lean_inc(v_val_406_);
v___x_409_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v___x_409_, 0, v_val_406_);
return v___x_409_;
}
}
1 => {
v_node_410_ = lean_ctor_get(v___x_404_, 0);
v___x_411_ = lean_usize_shift_right(v_x_396_, v___x_400_);
v_x_395_ = v_node_410_;
v_x_396_ = v___x_411_;
state = 0; continue;
}
_ => {
v___x_413_ = lean_box(0);
return v___x_413_;
}
}
} else {
v_ks_414_ = lean_ctor_get(v_x_395_, 0);
v_vs_415_ = lean_ctor_get(v_x_395_, 1);
v___x_416_ = lean_unsigned_to_nat(0);
v___x_417_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00main_spec__7_spec__11_spec__15___redArg(v_ks_414_, v_vs_415_, v___x_416_, v_x_397_);
return v___x_417_;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00main_spec__7_spec__11___redArg___boxed(mut v_x_418_: *mut lean_object, mut v_x_419_: *mut lean_object, mut v_x_420_: *mut lean_object) -> *mut lean_object{
let mut v_x_1896__boxed_421_: usize = 0; let mut v_res_422_: *mut lean_object = core::ptr::null_mut(); 
v_x_1896__boxed_421_ = lean_unbox_usize(v_x_419_);
lean_dec(v_x_419_);
v_res_422_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00main_spec__7_spec__11___redArg(v_x_418_, v_x_1896__boxed_421_, v_x_420_);
lean_dec(v_x_420_);
lean_dec_ref(v_x_418_);
return v_res_422_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_find_x3f___at___00main_spec__7___redArg(mut v_x_423_: *mut lean_object, mut v_x_424_: *mut lean_object) -> *mut lean_object{
let mut v___x_425_: u64 = 0; let mut v___x_426_: usize = 0; let mut v___x_427_: *mut lean_object = core::ptr::null_mut(); 
v___x_425_ = lean_uint64_of_nat(v_x_424_);
v___x_426_ = lean_uint64_to_usize(v___x_425_);
v___x_427_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00main_spec__7_spec__11___redArg(v_x_423_, v___x_426_, v_x_424_);
return v___x_427_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_find_x3f___at___00main_spec__7___redArg___boxed(mut v_x_428_: *mut lean_object, mut v_x_429_: *mut lean_object) -> *mut lean_object{
let mut v_res_430_: *mut lean_object = core::ptr::null_mut(); 
v_res_430_ = l_Lean_PersistentHashMap_find_x3f___at___00main_spec__7___redArg(v_x_428_, v_x_429_);
lean_dec(v_x_429_);
lean_dec_ref(v_x_428_);
return v_res_430_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00main_spec__1_spec__2(mut v_s_431_: *mut lean_object) -> *mut lean_object{
let mut v___x_433_: *mut lean_object = core::ptr::null_mut(); let mut v_putStr_434_: *mut lean_object = core::ptr::null_mut(); let mut v___x_435_: *mut lean_object = core::ptr::null_mut(); 
v___x_433_ = lean_get_stdout();
v_putStr_434_ = lean_ctor_get(v___x_433_, 4);
lean_inc_ref(v_putStr_434_);
lean_dec_ref(v___x_433_);
v___x_435_ = lean_apply_2(v_putStr_434_, v_s_431_, lean_box(0));
return v___x_435_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00main_spec__1_spec__2___boxed(mut v_s_436_: *mut lean_object, mut v_a_437_: *mut lean_object) -> *mut lean_object{
let mut v_res_438_: *mut lean_object = core::ptr::null_mut(); 
v_res_438_ = l_IO_print___at___00IO_println___at___00main_spec__1_spec__2(v_s_436_);
return v_res_438_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__1(mut v_s_441_: *mut lean_object) -> *mut lean_object{
let mut v___y_444_: *mut lean_object = core::ptr::null_mut(); let mut v___x_445_: u32 = 0; let mut v___x_446_: *mut lean_object = core::ptr::null_mut(); let mut v___x_447_: *mut lean_object = core::ptr::null_mut(); let mut v___x_448_: *mut lean_object = core::ptr::null_mut(); let mut v_val_449_: *mut lean_object = core::ptr::null_mut(); let mut v___x_450_: *mut lean_object = core::ptr::null_mut(); let mut v___x_451_: *mut lean_object = core::ptr::null_mut(); let mut v___x_452_: *mut lean_object = core::ptr::null_mut(); let mut v___x_453_: *mut lean_object = core::ptr::null_mut(); let mut v___x_454_: *mut lean_object = core::ptr::null_mut(); let mut v___x_455_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_s_441_) == 0 {
v___x_448_ = l_IO_println___at___00main_spec__1___closed__0;
v___y_444_ = v___x_448_;
state = 1; continue;
} else {
v_val_449_ = lean_ctor_get(v_s_441_, 0);
lean_inc(v_val_449_);
lean_dec_ref_known(v_s_441_, 1);
v___x_450_ = l_IO_println___at___00main_spec__1___closed__1;
v___x_451_ = l_Nat_reprFast(v_val_449_);
v___x_452_ = l_addParenHeuristic(v___x_451_);
v___x_453_ = lean_string_append(v___x_450_, v___x_452_);
lean_dec_ref(v___x_452_);
v___x_454_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__5;
v___x_455_ = lean_string_append(v___x_453_, v___x_454_);
v___y_444_ = v___x_455_;
state = 1; continue;
}
}
1 => {
v___x_445_ = 10;
v___x_446_ = lean_string_push(v___y_444_, v___x_445_);
v___x_447_ = l_IO_print___at___00IO_println___at___00main_spec__1_spec__2(v___x_446_);
return v___x_447_;
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__1___boxed(mut v_s_456_: *mut lean_object, mut v_a_457_: *mut lean_object) -> *mut lean_object{
let mut v_res_458_: *mut lean_object = core::ptr::null_mut(); 
v_res_458_ = l_IO_println___at___00main_spec__1(v_s_456_);
return v_res_458_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00main_spec__6_spec__9___redArg(mut v_x_459_: *mut lean_object, mut v_x_460_: usize, mut v_x_461_: *mut lean_object) -> *mut lean_object{
let mut v_es_462_: *mut lean_object = core::ptr::null_mut(); let mut v___x_463_: *mut lean_object = core::ptr::null_mut(); let mut v___x_464_: usize = 0; let mut v___x_465_: usize = 0; let mut v___x_466_: usize = 0; let mut v_j_467_: *mut lean_object = core::ptr::null_mut(); let mut v_entry_468_: *mut lean_object = core::ptr::null_mut(); let mut v_key_469_: *mut lean_object = core::ptr::null_mut(); let mut v___x_470_: u8 = 0; let mut v___x_472_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_473_: u8 = 0; let mut v___x_474_: *mut lean_object = core::ptr::null_mut(); let mut v___x_476_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_477_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_478_: u8 = 0; let mut v_unused_479_: *mut lean_object = core::ptr::null_mut(); let mut v___x_481_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_482_: u8 = 0; let mut v_node_483_: *mut lean_object = core::ptr::null_mut(); let mut v___x_485_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_486_: u8 = 0; let mut v_entries_487_: *mut lean_object = core::ptr::null_mut(); let mut v___x_488_: usize = 0; let mut v_newNode_489_: *mut lean_object = core::ptr::null_mut(); let mut v___x_490_: *mut lean_object = core::ptr::null_mut(); let mut v___x_492_: *mut lean_object = core::ptr::null_mut(); let mut v___x_493_: *mut lean_object = core::ptr::null_mut(); let mut v___x_495_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_496_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_497_: *mut lean_object = core::ptr::null_mut(); let mut v_val_498_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_499_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_500_: *mut lean_object = core::ptr::null_mut(); let mut v___x_502_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_503_: u8 = 0; let mut v___x_505_: *mut lean_object = core::ptr::null_mut(); let mut v___x_506_: *mut lean_object = core::ptr::null_mut(); let mut v___x_508_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_509_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_510_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_511_: u8 = 0; let mut v_isSharedCheck_512_: u8 = 0; let mut v_isSharedCheck_513_: u8 = 0; let mut v_unused_514_: *mut lean_object = core::ptr::null_mut(); let mut v_ks_515_: *mut lean_object = core::ptr::null_mut(); let mut v_vs_516_: *mut lean_object = core::ptr::null_mut(); let mut v___x_518_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_519_: u8 = 0; let mut v___x_520_: *mut lean_object = core::ptr::null_mut(); let mut v___x_522_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_523_: *mut lean_object = core::ptr::null_mut(); let mut v_val_524_: *mut lean_object = core::ptr::null_mut(); let mut v_keys_x27_525_: *mut lean_object = core::ptr::null_mut(); let mut v_vals_x27_526_: *mut lean_object = core::ptr::null_mut(); let mut v___x_528_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_529_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_530_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_x_459_) == 0 {
v_es_462_ = lean_ctor_get(v_x_459_, 0);
v___x_463_ = lean_box(2);
v___x_464_ = 5usize;
v___x_465_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00main_spec__7_spec__11___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00main_spec__7_spec__11___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00main_spec__7_spec__11___redArg___closed__1);
v___x_466_ = lean_usize_land(v_x_460_, v___x_465_);
v_j_467_ = lean_usize_to_nat(v___x_466_);
v_entry_468_ = lean_array_get(v___x_463_, v_es_462_, v_j_467_);
match lean_obj_tag(v_entry_468_)
{
0 => {
v_key_469_ = lean_ctor_get(v_entry_468_, 0);
lean_inc(v_key_469_);
lean_dec_ref_known(v_entry_468_, 2);
v___x_470_ = lean_nat_dec_eq(v_x_461_, v_key_469_);
lean_dec(v_key_469_);
if v___x_470_ == 0 {
lean_dec(v_j_467_);
return v_x_459_;
} else {
lean_inc_ref(v_es_462_);
v_isSharedCheck_478_ = (!lean_is_exclusive(v_x_459_)) as u8;
if v_isSharedCheck_478_ == 0 {
v_unused_479_ = lean_ctor_get(v_x_459_, 0);
lean_dec(v_unused_479_);
v___x_472_ = v_x_459_;
v_isShared_473_ = v_isSharedCheck_478_;
state = 1; continue;
} else {
lean_dec(v_x_459_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_478_;
state = 1; continue;
}
}
}
1 => {
lean_inc_ref(v_es_462_);
v_isSharedCheck_513_ = (!lean_is_exclusive(v_x_459_)) as u8;
if v_isSharedCheck_513_ == 0 {
v_unused_514_ = lean_ctor_get(v_x_459_, 0);
lean_dec(v_unused_514_);
v___x_481_ = v_x_459_;
v_isShared_482_ = v_isSharedCheck_513_;
state = 3; continue;
} else {
lean_dec(v_x_459_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_513_;
state = 3; continue;
}
}
_ => {
lean_dec(v_j_467_);
return v_x_459_;
}
}
} else {
v_ks_515_ = lean_ctor_get(v_x_459_, 0);
v_vs_516_ = lean_ctor_get(v_x_459_, 1);
v_isSharedCheck_530_ = (!lean_is_exclusive(v_x_459_)) as u8;
if v_isSharedCheck_530_ == 0 {
v___x_518_ = v_x_459_;
v_isShared_519_ = v_isSharedCheck_530_;
state = 10; continue;
} else {
lean_inc(v_vs_516_);
lean_inc(v_ks_515_);
lean_dec(v_x_459_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_530_;
state = 10; continue;
}
}
}
1 => {
v___x_474_ = lean_array_set(v_es_462_, v_j_467_, v___x_463_);
lean_dec(v_j_467_);
if v_isShared_473_ == 0 {
lean_ctor_set(v___x_472_, 0, v___x_474_);
v___x_476_ = v___x_472_;
state = 2; continue;
} else {
v_reuseFailAlloc_477_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v___x_474_);
v___x_476_ = v_reuseFailAlloc_477_;
state = 2; continue;
}
}
2 => {
return v___x_476_;
}
3 => {
v_node_483_ = lean_ctor_get(v_entry_468_, 0);
v_isSharedCheck_512_ = (!lean_is_exclusive(v_entry_468_)) as u8;
if v_isSharedCheck_512_ == 0 {
v___x_485_ = v_entry_468_;
v_isShared_486_ = v_isSharedCheck_512_;
state = 4; continue;
} else {
lean_inc(v_node_483_);
lean_dec(v_entry_468_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_512_;
state = 4; continue;
}
}
4 => {
v_entries_487_ = lean_array_set(v_es_462_, v_j_467_, v___x_463_);
v___x_488_ = lean_usize_shift_right(v_x_460_, v___x_464_);
v_newNode_489_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00main_spec__6_spec__9___redArg(v_node_483_, v___x_488_, v_x_461_);
lean_inc_ref(v_newNode_489_);
v___x_490_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_489_);
if lean_obj_tag(v___x_490_) == 0 {
if v_isShared_486_ == 0 {
lean_ctor_set(v___x_485_, 0, v_newNode_489_);
v___x_492_ = v___x_485_;
state = 5; continue;
} else {
v_reuseFailAlloc_497_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_newNode_489_);
v___x_492_ = v_reuseFailAlloc_497_;
state = 5; continue;
}
} else {
lean_dec_ref(v_newNode_489_);
lean_del_object(v___x_485_);
v_val_498_ = lean_ctor_get(v___x_490_, 0);
lean_inc(v_val_498_);
lean_dec_ref_known(v___x_490_, 1);
v_fst_499_ = lean_ctor_get(v_val_498_, 0);
v_snd_500_ = lean_ctor_get(v_val_498_, 1);
v_isSharedCheck_511_ = (!lean_is_exclusive(v_val_498_)) as u8;
if v_isSharedCheck_511_ == 0 {
v___x_502_ = v_val_498_;
v_isShared_503_ = v_isSharedCheck_511_;
state = 7; continue;
} else {
lean_inc(v_snd_500_);
lean_inc(v_fst_499_);
lean_dec(v_val_498_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_511_;
state = 7; continue;
}
}
}
5 => {
v___x_493_ = lean_array_set(v_entries_487_, v_j_467_, v___x_492_);
lean_dec(v_j_467_);
if v_isShared_482_ == 0 {
lean_ctor_set(v___x_481_, 0, v___x_493_);
v___x_495_ = v___x_481_;
state = 6; continue;
} else {
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v___x_493_);
v___x_495_ = v_reuseFailAlloc_496_;
state = 6; continue;
}
}
6 => {
return v___x_495_;
}
7 => {
if v_isShared_503_ == 0 {
v___x_505_ = v___x_502_;
state = 8; continue;
} else {
v_reuseFailAlloc_510_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v_fst_499_);
lean_ctor_set(v_reuseFailAlloc_510_, 1, v_snd_500_);
v___x_505_ = v_reuseFailAlloc_510_;
state = 8; continue;
}
}
8 => {
v___x_506_ = lean_array_set(v_entries_487_, v_j_467_, v___x_505_);
lean_dec(v_j_467_);
if v_isShared_482_ == 0 {
lean_ctor_set(v___x_481_, 0, v___x_506_);
v___x_508_ = v___x_481_;
state = 9; continue;
} else {
v_reuseFailAlloc_509_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v___x_506_);
v___x_508_ = v_reuseFailAlloc_509_;
state = 9; continue;
}
}
9 => {
return v___x_508_;
}
10 => {
v___x_520_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00main_spec__0_spec__0(v_ks_515_, v_x_461_);
if lean_obj_tag(v___x_520_) == 0 {
if v_isShared_519_ == 0 {
v___x_522_ = v___x_518_;
state = 11; continue;
} else {
v_reuseFailAlloc_523_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v_ks_515_);
lean_ctor_set(v_reuseFailAlloc_523_, 1, v_vs_516_);
v___x_522_ = v_reuseFailAlloc_523_;
state = 11; continue;
}
} else {
v_val_524_ = lean_ctor_get(v___x_520_, 0);
lean_inc_n(v_val_524_, 2);
lean_dec_ref_known(v___x_520_, 1);
v_keys_x27_525_ = l_Array_eraseIdx___redArg(v_ks_515_, v_val_524_);
v_vals_x27_526_ = l_Array_eraseIdx___redArg(v_vs_516_, v_val_524_);
if v_isShared_519_ == 0 {
lean_ctor_set(v___x_518_, 1, v_vals_x27_526_);
lean_ctor_set(v___x_518_, 0, v_keys_x27_525_);
v___x_528_ = v___x_518_;
state = 12; continue;
} else {
v_reuseFailAlloc_529_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_keys_x27_525_);
lean_ctor_set(v_reuseFailAlloc_529_, 1, v_vals_x27_526_);
v___x_528_ = v_reuseFailAlloc_529_;
state = 12; continue;
}
}
}
11 => {
return v___x_522_;
}
12 => {
return v___x_528_;
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00main_spec__6_spec__9___redArg___boxed(mut v_x_531_: *mut lean_object, mut v_x_532_: *mut lean_object, mut v_x_533_: *mut lean_object) -> *mut lean_object{
let mut v_x_2010__boxed_534_: usize = 0; let mut v_res_535_: *mut lean_object = core::ptr::null_mut(); 
v_x_2010__boxed_534_ = lean_unbox_usize(v_x_532_);
lean_dec(v_x_532_);
v_res_535_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00main_spec__6_spec__9___redArg(v_x_531_, v_x_2010__boxed_534_, v_x_533_);
lean_dec(v_x_533_);
return v_res_535_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_erase___at___00main_spec__6___redArg(mut v_x_536_: *mut lean_object, mut v_x_537_: *mut lean_object) -> *mut lean_object{
let mut v___x_538_: u64 = 0; let mut v_h_539_: usize = 0; let mut v___x_540_: *mut lean_object = core::ptr::null_mut(); 
v___x_538_ = lean_uint64_of_nat(v_x_537_);
v_h_539_ = lean_uint64_to_usize(v___x_538_);
v___x_540_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00main_spec__6_spec__9___redArg(v_x_536_, v_h_539_, v_x_537_);
return v___x_540_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_erase___at___00main_spec__6___redArg___boxed(mut v_x_541_: *mut lean_object, mut v_x_542_: *mut lean_object) -> *mut lean_object{
let mut v_res_543_: *mut lean_object = core::ptr::null_mut(); 
v_res_543_ = l_Lean_PersistentHashMap_erase___at___00main_spec__6___redArg(v_x_541_, v_x_542_);
lean_dec(v_x_542_);
return v_res_543_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__5(mut v_s_544_: *mut lean_object) -> *mut lean_object{
let mut v___x_546_: *mut lean_object = core::ptr::null_mut(); let mut v___x_547_: u32 = 0; let mut v___x_548_: *mut lean_object = core::ptr::null_mut(); let mut v___x_549_: *mut lean_object = core::ptr::null_mut(); 
v___x_546_ = l_Lean_PersistentHashMap_Stats_toString(v_s_544_);
v___x_547_ = 10;
v___x_548_ = lean_string_push(v___x_546_, v___x_547_);
v___x_549_ = l_IO_print___at___00IO_println___at___00main_spec__1_spec__2(v___x_548_);
return v___x_549_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__5___boxed(mut v_s_550_: *mut lean_object, mut v_a_551_: *mut lean_object) -> *mut lean_object{
let mut v_res_552_: *mut lean_object = core::ptr::null_mut(); 
v_res_552_ = l_IO_println___at___00main_spec__5(v_s_550_);
return v_res_552_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__3_spec__5_spec__8_spec__12___redArg(mut v_x_553_: *mut lean_object, mut v_x_554_: *mut lean_object, mut v_x_555_: *mut lean_object, mut v_x_556_: *mut lean_object) -> *mut lean_object{
let mut v_ks_557_: *mut lean_object = core::ptr::null_mut(); let mut v_vs_558_: *mut lean_object = core::ptr::null_mut(); let mut v___x_560_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_561_: u8 = 0; let mut v___x_562_: *mut lean_object = core::ptr::null_mut(); let mut v___x_563_: u8 = 0; let mut v___x_564_: *mut lean_object = core::ptr::null_mut(); let mut v___x_565_: *mut lean_object = core::ptr::null_mut(); let mut v___x_567_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_568_: *mut lean_object = core::ptr::null_mut(); let mut v_k_x27_569_: *mut lean_object = core::ptr::null_mut(); let mut v___x_570_: u8 = 0; let mut v___x_572_: *mut lean_object = core::ptr::null_mut(); let mut v___x_573_: *mut lean_object = core::ptr::null_mut(); let mut v___x_574_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_576_: *mut lean_object = core::ptr::null_mut(); let mut v___x_577_: *mut lean_object = core::ptr::null_mut(); let mut v___x_578_: *mut lean_object = core::ptr::null_mut(); let mut v___x_580_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_581_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_582_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v_ks_557_ = lean_ctor_get(v_x_553_, 0);
v_vs_558_ = lean_ctor_get(v_x_553_, 1);
v_isSharedCheck_582_ = (!lean_is_exclusive(v_x_553_)) as u8;
if v_isSharedCheck_582_ == 0 {
v___x_560_ = v_x_553_;
v_isShared_561_ = v_isSharedCheck_582_;
state = 1; continue;
} else {
lean_inc(v_vs_558_);
lean_inc(v_ks_557_);
lean_dec(v_x_553_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_582_;
state = 1; continue;
}
}
1 => {
v___x_562_ = lean_array_get_size(v_ks_557_);
v___x_563_ = lean_nat_dec_lt(v_x_554_, v___x_562_);
if v___x_563_ == 0 {
lean_dec(v_x_554_);
v___x_564_ = lean_array_push(v_ks_557_, v_x_555_);
v___x_565_ = lean_array_push(v_vs_558_, v_x_556_);
if v_isShared_561_ == 0 {
lean_ctor_set(v___x_560_, 1, v___x_565_);
lean_ctor_set(v___x_560_, 0, v___x_564_);
v___x_567_ = v___x_560_;
state = 2; continue;
} else {
v_reuseFailAlloc_568_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v___x_564_);
lean_ctor_set(v_reuseFailAlloc_568_, 1, v___x_565_);
v___x_567_ = v_reuseFailAlloc_568_;
state = 2; continue;
}
} else {
v_k_x27_569_ = lean_array_fget_borrowed(v_ks_557_, v_x_554_);
v___x_570_ = lean_nat_dec_eq(v_x_555_, v_k_x27_569_);
if v___x_570_ == 0 {
if v_isShared_561_ == 0 {
v___x_572_ = v___x_560_;
state = 3; continue;
} else {
v_reuseFailAlloc_576_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v_ks_557_);
lean_ctor_set(v_reuseFailAlloc_576_, 1, v_vs_558_);
v___x_572_ = v_reuseFailAlloc_576_;
state = 3; continue;
}
} else {
v___x_577_ = lean_array_fset(v_ks_557_, v_x_554_, v_x_555_);
v___x_578_ = lean_array_fset(v_vs_558_, v_x_554_, v_x_556_);
lean_dec(v_x_554_);
if v_isShared_561_ == 0 {
lean_ctor_set(v___x_560_, 1, v___x_578_);
lean_ctor_set(v___x_560_, 0, v___x_577_);
v___x_580_ = v___x_560_;
state = 4; continue;
} else {
v_reuseFailAlloc_581_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v___x_577_);
lean_ctor_set(v_reuseFailAlloc_581_, 1, v___x_578_);
v___x_580_ = v_reuseFailAlloc_581_;
state = 4; continue;
}
}
}
}
2 => {
return v___x_567_;
}
3 => {
v___x_573_ = lean_unsigned_to_nat(1);
v___x_574_ = lean_nat_add(v_x_554_, v___x_573_);
lean_dec(v_x_554_);
v_x_553_ = v___x_572_;
v_x_554_ = v___x_574_;
state = 0; continue;
}
4 => {
return v___x_580_;
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__3_spec__5_spec__8___redArg(mut v_n_583_: *mut lean_object, mut v_k_584_: *mut lean_object, mut v_v_585_: *mut lean_object) -> *mut lean_object{
let mut v___x_586_: *mut lean_object = core::ptr::null_mut(); let mut v___x_587_: *mut lean_object = core::ptr::null_mut(); 
v___x_586_ = lean_unsigned_to_nat(0);
v___x_587_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__3_spec__5_spec__8_spec__12___redArg(v_n_583_, v___x_586_, v_k_584_, v_v_585_);
return v___x_587_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__3_spec__5___redArg___closed__0() -> *mut lean_object{
let mut v___x_588_: *mut lean_object = core::ptr::null_mut(); 
v___x_588_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_588_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__3_spec__5___redArg(mut v_x_589_: *mut lean_object, mut v_x_590_: usize, mut v_x_591_: usize, mut v_x_592_: *mut lean_object, mut v_x_593_: *mut lean_object) -> *mut lean_object{
let mut v_es_594_: *mut lean_object = core::ptr::null_mut(); let mut v___x_595_: usize = 0; let mut v___x_596_: usize = 0; let mut v___x_597_: usize = 0; let mut v___x_598_: usize = 0; let mut v_j_599_: *mut lean_object = core::ptr::null_mut(); let mut v___x_600_: *mut lean_object = core::ptr::null_mut(); let mut v___x_601_: u8 = 0; let mut v___x_603_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_604_: u8 = 0; let mut v_v_605_: *mut lean_object = core::ptr::null_mut(); let mut v___x_606_: *mut lean_object = core::ptr::null_mut(); let mut v_xs_x27_607_: *mut lean_object = core::ptr::null_mut(); let mut v___y_609_: *mut lean_object = core::ptr::null_mut(); let mut v___x_610_: *mut lean_object = core::ptr::null_mut(); let mut v___x_612_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_613_: *mut lean_object = core::ptr::null_mut(); let mut v_key_614_: *mut lean_object = core::ptr::null_mut(); let mut v_val_615_: *mut lean_object = core::ptr::null_mut(); let mut v___x_617_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_618_: u8 = 0; let mut v___x_619_: u8 = 0; let mut v___x_620_: *mut lean_object = core::ptr::null_mut(); let mut v___x_621_: *mut lean_object = core::ptr::null_mut(); let mut v___x_623_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_624_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_625_: u8 = 0; let mut v_node_626_: *mut lean_object = core::ptr::null_mut(); let mut v___x_628_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_629_: u8 = 0; let mut v___x_630_: usize = 0; let mut v___x_631_: usize = 0; let mut v___x_632_: *mut lean_object = core::ptr::null_mut(); let mut v___x_634_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_635_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_636_: u8 = 0; let mut v___x_637_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_638_: u8 = 0; let mut v_unused_639_: *mut lean_object = core::ptr::null_mut(); let mut v_ks_640_: *mut lean_object = core::ptr::null_mut(); let mut v_vs_641_: *mut lean_object = core::ptr::null_mut(); let mut v___x_643_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_644_: u8 = 0; let mut v___x_646_: *mut lean_object = core::ptr::null_mut(); let mut v_newNode_647_: *mut lean_object = core::ptr::null_mut(); let mut v___y_649_: u8 = 0; let mut v_ks_650_: *mut lean_object = core::ptr::null_mut(); let mut v_vs_651_: *mut lean_object = core::ptr::null_mut(); let mut v___x_652_: *mut lean_object = core::ptr::null_mut(); let mut v___x_653_: *mut lean_object = core::ptr::null_mut(); let mut v___x_654_: *mut lean_object = core::ptr::null_mut(); let mut v___x_655_: usize = 0; let mut v___x_656_: u8 = 0; let mut v___x_657_: *mut lean_object = core::ptr::null_mut(); let mut v___x_658_: *mut lean_object = core::ptr::null_mut(); let mut v___x_659_: u8 = 0; let mut v_reuseFailAlloc_660_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_661_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_x_589_) == 0 {
v_es_594_ = lean_ctor_get(v_x_589_, 0);
v___x_595_ = 5usize;
v___x_596_ = 1usize;
v___x_597_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00main_spec__7_spec__11___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00main_spec__7_spec__11___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00main_spec__7_spec__11___redArg___closed__1);
v___x_598_ = lean_usize_land(v_x_590_, v___x_597_);
v_j_599_ = lean_usize_to_nat(v___x_598_);
v___x_600_ = lean_array_get_size(v_es_594_);
v___x_601_ = lean_nat_dec_lt(v_j_599_, v___x_600_);
if v___x_601_ == 0 {
lean_dec(v_j_599_);
lean_dec(v_x_593_);
lean_dec(v_x_592_);
return v_x_589_;
} else {
lean_inc_ref(v_es_594_);
v_isSharedCheck_638_ = (!lean_is_exclusive(v_x_589_)) as u8;
if v_isSharedCheck_638_ == 0 {
v_unused_639_ = lean_ctor_get(v_x_589_, 0);
lean_dec(v_unused_639_);
v___x_603_ = v_x_589_;
v_isShared_604_ = v_isSharedCheck_638_;
state = 1; continue;
} else {
lean_dec(v_x_589_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_638_;
state = 1; continue;
}
}
} else {
v_ks_640_ = lean_ctor_get(v_x_589_, 0);
v_vs_641_ = lean_ctor_get(v_x_589_, 1);
v_isSharedCheck_661_ = (!lean_is_exclusive(v_x_589_)) as u8;
if v_isSharedCheck_661_ == 0 {
v___x_643_ = v_x_589_;
v_isShared_644_ = v_isSharedCheck_661_;
state = 8; continue;
} else {
lean_inc(v_vs_641_);
lean_inc(v_ks_640_);
lean_dec(v_x_589_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_661_;
state = 8; continue;
}
}
}
1 => {
v_v_605_ = lean_array_fget(v_es_594_, v_j_599_);
v___x_606_ = lean_box(0);
v_xs_x27_607_ = lean_array_fset(v_es_594_, v_j_599_, v___x_606_);
match lean_obj_tag(v_v_605_)
{
0 => {
v_key_614_ = lean_ctor_get(v_v_605_, 0);
v_val_615_ = lean_ctor_get(v_v_605_, 1);
v_isSharedCheck_625_ = (!lean_is_exclusive(v_v_605_)) as u8;
if v_isSharedCheck_625_ == 0 {
v___x_617_ = v_v_605_;
v_isShared_618_ = v_isSharedCheck_625_;
state = 4; continue;
} else {
lean_inc(v_val_615_);
lean_inc(v_key_614_);
lean_dec(v_v_605_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_625_;
state = 4; continue;
}
}
1 => {
v_node_626_ = lean_ctor_get(v_v_605_, 0);
v_isSharedCheck_636_ = (!lean_is_exclusive(v_v_605_)) as u8;
if v_isSharedCheck_636_ == 0 {
v___x_628_ = v_v_605_;
v_isShared_629_ = v_isSharedCheck_636_;
state = 6; continue;
} else {
lean_inc(v_node_626_);
lean_dec(v_v_605_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_636_;
state = 6; continue;
}
}
_ => {
v___x_637_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_637_, 0, v_x_592_);
lean_ctor_set(v___x_637_, 1, v_x_593_);
v___y_609_ = v___x_637_;
state = 2; continue;
}
}
}
2 => {
v___x_610_ = lean_array_fset(v_xs_x27_607_, v_j_599_, v___y_609_);
lean_dec(v_j_599_);
if v_isShared_604_ == 0 {
lean_ctor_set(v___x_603_, 0, v___x_610_);
v___x_612_ = v___x_603_;
state = 3; continue;
} else {
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v___x_610_);
v___x_612_ = v_reuseFailAlloc_613_;
state = 3; continue;
}
}
3 => {
return v___x_612_;
}
4 => {
v___x_619_ = lean_nat_dec_eq(v_x_592_, v_key_614_);
if v___x_619_ == 0 {
lean_del_object(v___x_617_);
v___x_620_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_614_, v_val_615_, v_x_592_, v_x_593_);
v___x_621_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v___x_621_, 0, v___x_620_);
v___y_609_ = v___x_621_;
state = 2; continue;
} else {
lean_dec(v_val_615_);
lean_dec(v_key_614_);
if v_isShared_618_ == 0 {
lean_ctor_set(v___x_617_, 1, v_x_593_);
lean_ctor_set(v___x_617_, 0, v_x_592_);
v___x_623_ = v___x_617_;
state = 5; continue;
} else {
v_reuseFailAlloc_624_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_x_592_);
lean_ctor_set(v_reuseFailAlloc_624_, 1, v_x_593_);
v___x_623_ = v_reuseFailAlloc_624_;
state = 5; continue;
}
}
}
5 => {
v___y_609_ = v___x_623_;
state = 2; continue;
}
6 => {
v___x_630_ = lean_usize_shift_right(v_x_590_, v___x_595_);
v___x_631_ = lean_usize_add(v_x_591_, v___x_596_);
v___x_632_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__3_spec__5___redArg(v_node_626_, v___x_630_, v___x_631_, v_x_592_, v_x_593_);
if v_isShared_629_ == 0 {
lean_ctor_set(v___x_628_, 0, v___x_632_);
v___x_634_ = v___x_628_;
state = 7; continue;
} else {
v_reuseFailAlloc_635_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v___x_632_);
v___x_634_ = v_reuseFailAlloc_635_;
state = 7; continue;
}
}
7 => {
v___y_609_ = v___x_634_;
state = 2; continue;
}
8 => {
if v_isShared_644_ == 0 {
v___x_646_ = v___x_643_;
state = 9; continue;
} else {
v_reuseFailAlloc_660_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v_ks_640_);
lean_ctor_set(v_reuseFailAlloc_660_, 1, v_vs_641_);
v___x_646_ = v_reuseFailAlloc_660_;
state = 9; continue;
}
}
9 => {
v_newNode_647_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__3_spec__5_spec__8___redArg(v___x_646_, v_x_592_, v_x_593_);
v___x_655_ = 7usize;
v___x_656_ = lean_usize_dec_le(v___x_655_, v_x_591_);
if v___x_656_ == 0 {
v___x_657_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_647_);
v___x_658_ = lean_unsigned_to_nat(4);
v___x_659_ = lean_nat_dec_lt(v___x_657_, v___x_658_);
lean_dec(v___x_657_);
v___y_649_ = v___x_659_;
state = 10; continue;
} else {
v___y_649_ = v___x_656_;
state = 10; continue;
}
}
10 => {
if v___y_649_ == 0 {
v_ks_650_ = lean_ctor_get(v_newNode_647_, 0);
lean_inc_ref(v_ks_650_);
v_vs_651_ = lean_ctor_get(v_newNode_647_, 1);
lean_inc_ref(v_vs_651_);
lean_dec_ref(v_newNode_647_);
v___x_652_ = lean_unsigned_to_nat(0);
v___x_653_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__3_spec__5___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__3_spec__5___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__3_spec__5___redArg___closed__0);
v___x_654_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__3_spec__5_spec__9___redArg(v_x_591_, v_ks_650_, v_vs_651_, v___x_652_, v___x_653_);
lean_dec_ref(v_vs_651_);
lean_dec_ref(v_ks_650_);
return v___x_654_;
} else {
return v_newNode_647_;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__3_spec__5_spec__9___redArg(mut v_depth_662_: usize, mut v_keys_663_: *mut lean_object, mut v_vals_664_: *mut lean_object, mut v_i_665_: *mut lean_object, mut v_entries_666_: *mut lean_object) -> *mut lean_object{
let mut v___x_667_: *mut lean_object = core::ptr::null_mut(); let mut v___x_668_: u8 = 0; let mut v_k_669_: *mut lean_object = core::ptr::null_mut(); let mut v_v_670_: *mut lean_object = core::ptr::null_mut(); let mut v___x_671_: u64 = 0; let mut v_h_672_: usize = 0; let mut v___x_673_: usize = 0; let mut v___x_674_: *mut lean_object = core::ptr::null_mut(); let mut v___x_675_: usize = 0; let mut v___x_676_: usize = 0; let mut v___x_677_: usize = 0; let mut v_h_678_: usize = 0; let mut v___x_679_: *mut lean_object = core::ptr::null_mut(); let mut v___x_680_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_667_ = lean_array_get_size(v_keys_663_);
v___x_668_ = lean_nat_dec_lt(v_i_665_, v___x_667_);
if v___x_668_ == 0 {
lean_dec(v_i_665_);
return v_entries_666_;
} else {
v_k_669_ = lean_array_fget_borrowed(v_keys_663_, v_i_665_);
v_v_670_ = lean_array_fget_borrowed(v_vals_664_, v_i_665_);
v___x_671_ = lean_uint64_of_nat(v_k_669_);
v_h_672_ = lean_uint64_to_usize(v___x_671_);
v___x_673_ = 5usize;
v___x_674_ = lean_unsigned_to_nat(1);
v___x_675_ = 1usize;
v___x_676_ = lean_usize_sub(v_depth_662_, v___x_675_);
v___x_677_ = lean_usize_mul(v___x_673_, v___x_676_);
v_h_678_ = lean_usize_shift_right(v_h_672_, v___x_677_);
v___x_679_ = lean_nat_add(v_i_665_, v___x_674_);
lean_dec(v_i_665_);
lean_inc(v_v_670_);
lean_inc(v_k_669_);
v___x_680_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__3_spec__5___redArg(v_entries_666_, v_h_678_, v_depth_662_, v_k_669_, v_v_670_);
v_i_665_ = v___x_679_;
v_entries_666_ = v___x_680_;
state = 0; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__3_spec__5_spec__9___redArg___boxed(mut v_depth_682_: *mut lean_object, mut v_keys_683_: *mut lean_object, mut v_vals_684_: *mut lean_object, mut v_i_685_: *mut lean_object, mut v_entries_686_: *mut lean_object) -> *mut lean_object{
let mut v_depth_boxed_687_: usize = 0; let mut v_res_688_: *mut lean_object = core::ptr::null_mut(); 
v_depth_boxed_687_ = lean_unbox_usize(v_depth_682_);
lean_dec(v_depth_682_);
v_res_688_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__3_spec__5_spec__9___redArg(v_depth_boxed_687_, v_keys_683_, v_vals_684_, v_i_685_, v_entries_686_);
lean_dec_ref(v_vals_684_);
lean_dec_ref(v_keys_683_);
return v_res_688_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__3_spec__5___redArg___boxed(mut v_x_689_: *mut lean_object, mut v_x_690_: *mut lean_object, mut v_x_691_: *mut lean_object, mut v_x_692_: *mut lean_object, mut v_x_693_: *mut lean_object) -> *mut lean_object{
let mut v_x_2251__boxed_694_: usize = 0; let mut v_x_2252__boxed_695_: usize = 0; let mut v_res_696_: *mut lean_object = core::ptr::null_mut(); 
v_x_2251__boxed_694_ = lean_unbox_usize(v_x_690_);
lean_dec(v_x_690_);
v_x_2252__boxed_695_ = lean_unbox_usize(v_x_691_);
lean_dec(v_x_691_);
v_res_696_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__3_spec__5___redArg(v_x_689_, v_x_2251__boxed_694_, v_x_2252__boxed_695_, v_x_692_, v_x_693_);
return v_res_696_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_insert___at___00main_spec__3___redArg(mut v_x_697_: *mut lean_object, mut v_x_698_: *mut lean_object, mut v_x_699_: *mut lean_object) -> *mut lean_object{
let mut v___x_700_: u64 = 0; let mut v___x_701_: usize = 0; let mut v___x_702_: usize = 0; let mut v___x_703_: *mut lean_object = core::ptr::null_mut(); 
v___x_700_ = lean_uint64_of_nat(v_x_698_);
v___x_701_ = lean_uint64_to_usize(v___x_700_);
v___x_702_ = 1usize;
v___x_703_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__3_spec__5___redArg(v_x_697_, v___x_701_, v___x_702_, v_x_698_, v_x_699_);
return v___x_703_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__1() -> *mut lean_object{
let mut v___x_711_: *mut lean_object = core::ptr::null_mut(); let mut v_a_712_: *mut lean_object = core::ptr::null_mut(); let mut v___x_713_: *mut lean_object = core::ptr::null_mut(); 
v___x_711_ = lean_unsigned_to_nat(2);
v_a_712_ = l_main___closed__0;
v___x_713_ = l_Array_idxOf_x3f___at___00main_spec__0(v_a_712_, v___x_711_);
return v___x_713_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__2() -> *mut lean_object{
let mut v___x_714_: *mut lean_object = core::ptr::null_mut(); 
v___x_714_ = l_Lean_PersistentHashMap_empty___at___00main_spec__2(lean_box(0));
return v___x_714_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__3() -> *mut lean_object{
let mut v___x_715_: *mut lean_object = core::ptr::null_mut(); let mut v___x_716_: *mut lean_object = core::ptr::null_mut(); let mut v___x_717_: *mut lean_object = core::ptr::null_mut(); 
v___x_715_ = lean_unsigned_to_nat(1);
v___x_716_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__2), core::ptr::addr_of_mut!(l_main___closed__2_once), _init_l_main___closed__2);
v___x_717_ = l_Lean_PersistentHashMap_insert___at___00main_spec__3___redArg(v___x_716_, v___x_715_, v___x_715_);
return v___x_717_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__4() -> *mut lean_object{
let mut v___x_718_: *mut lean_object = core::ptr::null_mut(); let mut v___x_719_: *mut lean_object = core::ptr::null_mut(); let mut v___x_720_: *mut lean_object = core::ptr::null_mut(); let mut v___x_721_: *mut lean_object = core::ptr::null_mut(); 
v___x_718_ = lean_unsigned_to_nat(2);
v___x_719_ = lean_unsigned_to_nat(33);
v___x_720_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__3), core::ptr::addr_of_mut!(l_main___closed__3_once), _init_l_main___closed__3);
v___x_721_ = l_Lean_PersistentHashMap_insert___at___00main_spec__3___redArg(v___x_720_, v___x_719_, v___x_718_);
return v___x_721_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__5() -> *mut lean_object{
let mut v___x_722_: *mut lean_object = core::ptr::null_mut(); let mut v___x_723_: *mut lean_object = core::ptr::null_mut(); let mut v___x_724_: *mut lean_object = core::ptr::null_mut(); let mut v___x_725_: *mut lean_object = core::ptr::null_mut(); 
v___x_722_ = lean_unsigned_to_nat(3);
v___x_723_ = lean_unsigned_to_nat(65);
v___x_724_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__4), core::ptr::addr_of_mut!(l_main___closed__4_once), _init_l_main___closed__4);
v___x_725_ = l_Lean_PersistentHashMap_insert___at___00main_spec__3___redArg(v___x_724_, v___x_723_, v___x_722_);
return v___x_725_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__6() -> *mut lean_object{
let mut v___x_726_: *mut lean_object = core::ptr::null_mut(); let mut v___x_727_: *mut lean_object = core::ptr::null_mut(); 
v___x_726_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__5), core::ptr::addr_of_mut!(l_main___closed__5_once), _init_l_main___closed__5);
v___x_727_ = l_Lean_PersistentHashMap_stats___at___00main_spec__4___redArg(v___x_726_);
return v___x_727_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__7() -> *mut lean_object{
let mut v___x_728_: *mut lean_object = core::ptr::null_mut(); let mut v___x_729_: *mut lean_object = core::ptr::null_mut(); let mut v___x_730_: *mut lean_object = core::ptr::null_mut(); 
v___x_728_ = lean_unsigned_to_nat(33);
v___x_729_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__5), core::ptr::addr_of_mut!(l_main___closed__5_once), _init_l_main___closed__5);
v___x_730_ = l_Lean_PersistentHashMap_erase___at___00main_spec__6___redArg(v___x_729_, v___x_728_);
return v___x_730_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__8() -> *mut lean_object{
let mut v___x_731_: *mut lean_object = core::ptr::null_mut(); let mut v___x_732_: *mut lean_object = core::ptr::null_mut(); let mut v___x_733_: *mut lean_object = core::ptr::null_mut(); 
v___x_731_ = lean_unsigned_to_nat(1);
v___x_732_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__7), core::ptr::addr_of_mut!(l_main___closed__7_once), _init_l_main___closed__7);
v___x_733_ = l_Lean_PersistentHashMap_find_x3f___at___00main_spec__7___redArg(v___x_732_, v___x_731_);
return v___x_733_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__9() -> *mut lean_object{
let mut v___x_734_: *mut lean_object = core::ptr::null_mut(); let mut v___x_735_: *mut lean_object = core::ptr::null_mut(); let mut v___x_736_: *mut lean_object = core::ptr::null_mut(); 
v___x_734_ = lean_unsigned_to_nat(33);
v___x_735_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__7), core::ptr::addr_of_mut!(l_main___closed__7_once), _init_l_main___closed__7);
v___x_736_ = l_Lean_PersistentHashMap_find_x3f___at___00main_spec__7___redArg(v___x_735_, v___x_734_);
return v___x_736_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__10() -> *mut lean_object{
let mut v___x_737_: *mut lean_object = core::ptr::null_mut(); let mut v___x_738_: *mut lean_object = core::ptr::null_mut(); let mut v___x_739_: *mut lean_object = core::ptr::null_mut(); 
v___x_737_ = lean_unsigned_to_nat(65);
v___x_738_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__7), core::ptr::addr_of_mut!(l_main___closed__7_once), _init_l_main___closed__7);
v___x_739_ = l_Lean_PersistentHashMap_find_x3f___at___00main_spec__7___redArg(v___x_738_, v___x_737_);
return v___x_739_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__11() -> *mut lean_object{
let mut v___x_740_: *mut lean_object = core::ptr::null_mut(); let mut v___x_741_: *mut lean_object = core::ptr::null_mut(); 
v___x_740_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__7), core::ptr::addr_of_mut!(l_main___closed__7_once), _init_l_main___closed__7);
v___x_741_ = l_Lean_PersistentHashMap_stats___at___00main_spec__4___redArg(v___x_740_);
return v___x_741_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__12() -> *mut lean_object{
let mut v___x_742_: *mut lean_object = core::ptr::null_mut(); let mut v___x_743_: *mut lean_object = core::ptr::null_mut(); let mut v___x_744_: *mut lean_object = core::ptr::null_mut(); 
v___x_742_ = lean_unsigned_to_nat(1);
v___x_743_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__7), core::ptr::addr_of_mut!(l_main___closed__7_once), _init_l_main___closed__7);
v___x_744_ = l_Lean_PersistentHashMap_erase___at___00main_spec__6___redArg(v___x_743_, v___x_742_);
return v___x_744_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__13() -> *mut lean_object{
let mut v___x_745_: *mut lean_object = core::ptr::null_mut(); let mut v___x_746_: *mut lean_object = core::ptr::null_mut(); let mut v___x_747_: *mut lean_object = core::ptr::null_mut(); 
v___x_745_ = lean_unsigned_to_nat(1);
v___x_746_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__12), core::ptr::addr_of_mut!(l_main___closed__12_once), _init_l_main___closed__12);
v___x_747_ = l_Lean_PersistentHashMap_find_x3f___at___00main_spec__7___redArg(v___x_746_, v___x_745_);
return v___x_747_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__14() -> *mut lean_object{
let mut v___x_748_: *mut lean_object = core::ptr::null_mut(); let mut v___x_749_: *mut lean_object = core::ptr::null_mut(); let mut v___x_750_: *mut lean_object = core::ptr::null_mut(); 
v___x_748_ = lean_unsigned_to_nat(33);
v___x_749_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__12), core::ptr::addr_of_mut!(l_main___closed__12_once), _init_l_main___closed__12);
v___x_750_ = l_Lean_PersistentHashMap_find_x3f___at___00main_spec__7___redArg(v___x_749_, v___x_748_);
return v___x_750_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__15() -> *mut lean_object{
let mut v___x_751_: *mut lean_object = core::ptr::null_mut(); let mut v___x_752_: *mut lean_object = core::ptr::null_mut(); let mut v___x_753_: *mut lean_object = core::ptr::null_mut(); 
v___x_751_ = lean_unsigned_to_nat(65);
v___x_752_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__12), core::ptr::addr_of_mut!(l_main___closed__12_once), _init_l_main___closed__12);
v___x_753_ = l_Lean_PersistentHashMap_find_x3f___at___00main_spec__7___redArg(v___x_752_, v___x_751_);
return v___x_753_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__16() -> *mut lean_object{
let mut v___x_754_: *mut lean_object = core::ptr::null_mut(); let mut v___x_755_: *mut lean_object = core::ptr::null_mut(); 
v___x_754_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__12), core::ptr::addr_of_mut!(l_main___closed__12_once), _init_l_main___closed__12);
v___x_755_ = l_Lean_PersistentHashMap_stats___at___00main_spec__4___redArg(v___x_754_);
return v___x_755_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__17() -> *mut lean_object{
let mut v___x_756_: *mut lean_object = core::ptr::null_mut(); let mut v___x_757_: *mut lean_object = core::ptr::null_mut(); let mut v___x_758_: *mut lean_object = core::ptr::null_mut(); 
v___x_756_ = lean_unsigned_to_nat(1);
v___x_757_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__12), core::ptr::addr_of_mut!(l_main___closed__12_once), _init_l_main___closed__12);
v___x_758_ = l_Lean_PersistentHashMap_erase___at___00main_spec__6___redArg(v___x_757_, v___x_756_);
return v___x_758_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__18() -> *mut lean_object{
let mut v___x_759_: *mut lean_object = core::ptr::null_mut(); let mut v___x_760_: *mut lean_object = core::ptr::null_mut(); let mut v___x_761_: *mut lean_object = core::ptr::null_mut(); 
v___x_759_ = lean_unsigned_to_nat(1);
v___x_760_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__17), core::ptr::addr_of_mut!(l_main___closed__17_once), _init_l_main___closed__17);
v___x_761_ = l_Lean_PersistentHashMap_find_x3f___at___00main_spec__7___redArg(v___x_760_, v___x_759_);
return v___x_761_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__19() -> *mut lean_object{
let mut v___x_762_: *mut lean_object = core::ptr::null_mut(); let mut v___x_763_: *mut lean_object = core::ptr::null_mut(); let mut v___x_764_: *mut lean_object = core::ptr::null_mut(); 
v___x_762_ = lean_unsigned_to_nat(33);
v___x_763_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__17), core::ptr::addr_of_mut!(l_main___closed__17_once), _init_l_main___closed__17);
v___x_764_ = l_Lean_PersistentHashMap_find_x3f___at___00main_spec__7___redArg(v___x_763_, v___x_762_);
return v___x_764_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__20() -> *mut lean_object{
let mut v___x_765_: *mut lean_object = core::ptr::null_mut(); let mut v___x_766_: *mut lean_object = core::ptr::null_mut(); let mut v___x_767_: *mut lean_object = core::ptr::null_mut(); 
v___x_765_ = lean_unsigned_to_nat(65);
v___x_766_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__17), core::ptr::addr_of_mut!(l_main___closed__17_once), _init_l_main___closed__17);
v___x_767_ = l_Lean_PersistentHashMap_find_x3f___at___00main_spec__7___redArg(v___x_766_, v___x_765_);
return v___x_767_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__21() -> *mut lean_object{
let mut v___x_768_: *mut lean_object = core::ptr::null_mut(); let mut v___x_769_: *mut lean_object = core::ptr::null_mut(); let mut v___x_770_: *mut lean_object = core::ptr::null_mut(); 
v___x_768_ = lean_unsigned_to_nat(65);
v___x_769_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__17), core::ptr::addr_of_mut!(l_main___closed__17_once), _init_l_main___closed__17);
v___x_770_ = l_Lean_PersistentHashMap_erase___at___00main_spec__6___redArg(v___x_769_, v___x_768_);
return v___x_770_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__22() -> *mut lean_object{
let mut v___x_771_: *mut lean_object = core::ptr::null_mut(); let mut v___x_772_: *mut lean_object = core::ptr::null_mut(); let mut v___x_773_: *mut lean_object = core::ptr::null_mut(); 
v___x_771_ = lean_unsigned_to_nat(1);
v___x_772_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__21), core::ptr::addr_of_mut!(l_main___closed__21_once), _init_l_main___closed__21);
v___x_773_ = l_Lean_PersistentHashMap_find_x3f___at___00main_spec__7___redArg(v___x_772_, v___x_771_);
return v___x_773_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__23() -> *mut lean_object{
let mut v___x_774_: *mut lean_object = core::ptr::null_mut(); let mut v___x_775_: *mut lean_object = core::ptr::null_mut(); let mut v___x_776_: *mut lean_object = core::ptr::null_mut(); 
v___x_774_ = lean_unsigned_to_nat(33);
v___x_775_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__21), core::ptr::addr_of_mut!(l_main___closed__21_once), _init_l_main___closed__21);
v___x_776_ = l_Lean_PersistentHashMap_find_x3f___at___00main_spec__7___redArg(v___x_775_, v___x_774_);
return v___x_776_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__24() -> *mut lean_object{
let mut v___x_777_: *mut lean_object = core::ptr::null_mut(); let mut v___x_778_: *mut lean_object = core::ptr::null_mut(); let mut v___x_779_: *mut lean_object = core::ptr::null_mut(); 
v___x_777_ = lean_unsigned_to_nat(65);
v___x_778_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__21), core::ptr::addr_of_mut!(l_main___closed__21_once), _init_l_main___closed__21);
v___x_779_ = l_Lean_PersistentHashMap_find_x3f___at___00main_spec__7___redArg(v___x_778_, v___x_777_);
return v___x_779_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__25() -> *mut lean_object{
let mut v___x_780_: *mut lean_object = core::ptr::null_mut(); let mut v___x_781_: *mut lean_object = core::ptr::null_mut(); 
v___x_780_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__21), core::ptr::addr_of_mut!(l_main___closed__21_once), _init_l_main___closed__21);
v___x_781_ = l_Lean_PersistentHashMap_stats___at___00main_spec__4___redArg(v___x_780_);
return v___x_781_;
}
#[no_mangle] pub unsafe extern "C" fn _lean_main() -> *mut lean_object{
let mut v___x_783_: *mut lean_object = core::ptr::null_mut(); let mut v___x_784_: *mut lean_object = core::ptr::null_mut(); 
v___x_783_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__1), core::ptr::addr_of_mut!(l_main___closed__1_once), _init_l_main___closed__1);
v___x_784_ = l_IO_println___at___00main_spec__1(v___x_783_);
if lean_obj_tag(v___x_784_) == 0 {
let mut v___x_785_: *mut lean_object = core::ptr::null_mut(); let mut v___x_786_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_784_, 1);
v___x_785_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__6), core::ptr::addr_of_mut!(l_main___closed__6_once), _init_l_main___closed__6);
v___x_786_ = l_IO_println___at___00main_spec__5(v___x_785_);
if lean_obj_tag(v___x_786_) == 0 {
let mut v___x_787_: *mut lean_object = core::ptr::null_mut(); let mut v___x_788_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_786_, 1);
v___x_787_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__8), core::ptr::addr_of_mut!(l_main___closed__8_once), _init_l_main___closed__8);
v___x_788_ = l_IO_println___at___00main_spec__1(v___x_787_);
if lean_obj_tag(v___x_788_) == 0 {
let mut v___x_789_: *mut lean_object = core::ptr::null_mut(); let mut v___x_790_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_788_, 1);
v___x_789_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__9), core::ptr::addr_of_mut!(l_main___closed__9_once), _init_l_main___closed__9);
v___x_790_ = l_IO_println___at___00main_spec__1(v___x_789_);
if lean_obj_tag(v___x_790_) == 0 {
let mut v___x_791_: *mut lean_object = core::ptr::null_mut(); let mut v___x_792_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_790_, 1);
v___x_791_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__10), core::ptr::addr_of_mut!(l_main___closed__10_once), _init_l_main___closed__10);
v___x_792_ = l_IO_println___at___00main_spec__1(v___x_791_);
if lean_obj_tag(v___x_792_) == 0 {
let mut v___x_793_: *mut lean_object = core::ptr::null_mut(); let mut v___x_794_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_792_, 1);
v___x_793_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__11), core::ptr::addr_of_mut!(l_main___closed__11_once), _init_l_main___closed__11);
v___x_794_ = l_IO_println___at___00main_spec__5(v___x_793_);
if lean_obj_tag(v___x_794_) == 0 {
let mut v___x_795_: *mut lean_object = core::ptr::null_mut(); let mut v___x_796_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_794_, 1);
v___x_795_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__13), core::ptr::addr_of_mut!(l_main___closed__13_once), _init_l_main___closed__13);
v___x_796_ = l_IO_println___at___00main_spec__1(v___x_795_);
if lean_obj_tag(v___x_796_) == 0 {
let mut v___x_797_: *mut lean_object = core::ptr::null_mut(); let mut v___x_798_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_796_, 1);
v___x_797_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__14), core::ptr::addr_of_mut!(l_main___closed__14_once), _init_l_main___closed__14);
v___x_798_ = l_IO_println___at___00main_spec__1(v___x_797_);
if lean_obj_tag(v___x_798_) == 0 {
let mut v___x_799_: *mut lean_object = core::ptr::null_mut(); let mut v___x_800_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_798_, 1);
v___x_799_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__15), core::ptr::addr_of_mut!(l_main___closed__15_once), _init_l_main___closed__15);
v___x_800_ = l_IO_println___at___00main_spec__1(v___x_799_);
if lean_obj_tag(v___x_800_) == 0 {
let mut v___x_801_: *mut lean_object = core::ptr::null_mut(); let mut v___x_802_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_800_, 1);
v___x_801_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__16), core::ptr::addr_of_mut!(l_main___closed__16_once), _init_l_main___closed__16);
v___x_802_ = l_IO_println___at___00main_spec__5(v___x_801_);
if lean_obj_tag(v___x_802_) == 0 {
let mut v___x_803_: *mut lean_object = core::ptr::null_mut(); let mut v___x_804_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_802_, 1);
v___x_803_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__18), core::ptr::addr_of_mut!(l_main___closed__18_once), _init_l_main___closed__18);
v___x_804_ = l_IO_println___at___00main_spec__1(v___x_803_);
if lean_obj_tag(v___x_804_) == 0 {
let mut v___x_805_: *mut lean_object = core::ptr::null_mut(); let mut v___x_806_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_804_, 1);
v___x_805_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__19), core::ptr::addr_of_mut!(l_main___closed__19_once), _init_l_main___closed__19);
v___x_806_ = l_IO_println___at___00main_spec__1(v___x_805_);
if lean_obj_tag(v___x_806_) == 0 {
let mut v___x_807_: *mut lean_object = core::ptr::null_mut(); let mut v___x_808_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_806_, 1);
v___x_807_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__20), core::ptr::addr_of_mut!(l_main___closed__20_once), _init_l_main___closed__20);
v___x_808_ = l_IO_println___at___00main_spec__1(v___x_807_);
if lean_obj_tag(v___x_808_) == 0 {
let mut v___x_809_: *mut lean_object = core::ptr::null_mut(); let mut v___x_810_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_808_, 1);
v___x_809_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__22), core::ptr::addr_of_mut!(l_main___closed__22_once), _init_l_main___closed__22);
v___x_810_ = l_IO_println___at___00main_spec__1(v___x_809_);
if lean_obj_tag(v___x_810_) == 0 {
let mut v___x_811_: *mut lean_object = core::ptr::null_mut(); let mut v___x_812_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_810_, 1);
v___x_811_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__23), core::ptr::addr_of_mut!(l_main___closed__23_once), _init_l_main___closed__23);
v___x_812_ = l_IO_println___at___00main_spec__1(v___x_811_);
if lean_obj_tag(v___x_812_) == 0 {
let mut v___x_813_: *mut lean_object = core::ptr::null_mut(); let mut v___x_814_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_812_, 1);
v___x_813_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__24), core::ptr::addr_of_mut!(l_main___closed__24_once), _init_l_main___closed__24);
v___x_814_ = l_IO_println___at___00main_spec__1(v___x_813_);
if lean_obj_tag(v___x_814_) == 0 {
let mut v___x_815_: *mut lean_object = core::ptr::null_mut(); let mut v___x_816_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_814_, 1);
v___x_815_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__25), core::ptr::addr_of_mut!(l_main___closed__25_once), _init_l_main___closed__25);
v___x_816_ = l_IO_println___at___00main_spec__5(v___x_815_);
return v___x_816_;
} else {
return v___x_814_;
}
} else {
return v___x_812_;
}
} else {
return v___x_810_;
}
} else {
return v___x_808_;
}
} else {
return v___x_806_;
}
} else {
return v___x_804_;
}
} else {
return v___x_802_;
}
} else {
return v___x_800_;
}
} else {
return v___x_798_;
}
} else {
return v___x_796_;
}
} else {
return v___x_794_;
}
} else {
return v___x_792_;
}
} else {
return v___x_790_;
}
} else {
return v___x_788_;
}
} else {
return v___x_786_;
}
} else {
return v___x_784_;
}
}
#[no_mangle] pub unsafe extern "C" fn l_main___boxed(mut v_a_817_: *mut lean_object) -> *mut lean_object{
let mut v_res_818_: *mut lean_object = core::ptr::null_mut(); 
v_res_818_ = _lean_main();
return v_res_818_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_insert___at___00main_spec__3(mut v_00_u03b2_819_: *mut lean_object, mut v_x_820_: *mut lean_object, mut v_x_821_: *mut lean_object, mut v_x_822_: *mut lean_object) -> *mut lean_object{
let mut v___x_823_: *mut lean_object = core::ptr::null_mut(); 
v___x_823_ = l_Lean_PersistentHashMap_insert___at___00main_spec__3___redArg(v_x_820_, v_x_821_, v_x_822_);
return v___x_823_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_erase___at___00main_spec__6(mut v_00_u03b2_824_: *mut lean_object, mut v_x_825_: *mut lean_object, mut v_x_826_: *mut lean_object) -> *mut lean_object{
let mut v___x_827_: *mut lean_object = core::ptr::null_mut(); 
v___x_827_ = l_Lean_PersistentHashMap_erase___at___00main_spec__6___redArg(v_x_825_, v_x_826_);
return v___x_827_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_erase___at___00main_spec__6___boxed(mut v_00_u03b2_828_: *mut lean_object, mut v_x_829_: *mut lean_object, mut v_x_830_: *mut lean_object) -> *mut lean_object{
let mut v_res_831_: *mut lean_object = core::ptr::null_mut(); 
v_res_831_ = l_Lean_PersistentHashMap_erase___at___00main_spec__6(v_00_u03b2_828_, v_x_829_, v_x_830_);
lean_dec(v_x_830_);
return v_res_831_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_find_x3f___at___00main_spec__7(mut v_00_u03b2_832_: *mut lean_object, mut v_x_833_: *mut lean_object, mut v_x_834_: *mut lean_object) -> *mut lean_object{
let mut v___x_835_: *mut lean_object = core::ptr::null_mut(); 
v___x_835_ = l_Lean_PersistentHashMap_find_x3f___at___00main_spec__7___redArg(v_x_833_, v_x_834_);
return v___x_835_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_find_x3f___at___00main_spec__7___boxed(mut v_00_u03b2_836_: *mut lean_object, mut v_x_837_: *mut lean_object, mut v_x_838_: *mut lean_object) -> *mut lean_object{
let mut v_res_839_: *mut lean_object = core::ptr::null_mut(); 
v_res_839_ = l_Lean_PersistentHashMap_find_x3f___at___00main_spec__7(v_00_u03b2_836_, v_x_837_, v_x_838_);
lean_dec(v_x_838_);
lean_dec_ref(v_x_837_);
return v_res_839_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__3_spec__5(mut v_00_u03b2_840_: *mut lean_object, mut v_x_841_: *mut lean_object, mut v_x_842_: usize, mut v_x_843_: usize, mut v_x_844_: *mut lean_object, mut v_x_845_: *mut lean_object) -> *mut lean_object{
let mut v___x_846_: *mut lean_object = core::ptr::null_mut(); 
v___x_846_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__3_spec__5___redArg(v_x_841_, v_x_842_, v_x_843_, v_x_844_, v_x_845_);
return v___x_846_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__3_spec__5___boxed(mut v_00_u03b2_847_: *mut lean_object, mut v_x_848_: *mut lean_object, mut v_x_849_: *mut lean_object, mut v_x_850_: *mut lean_object, mut v_x_851_: *mut lean_object, mut v_x_852_: *mut lean_object) -> *mut lean_object{
let mut v_x_2780__boxed_853_: usize = 0; let mut v_x_2781__boxed_854_: usize = 0; let mut v_res_855_: *mut lean_object = core::ptr::null_mut(); 
v_x_2780__boxed_853_ = lean_unbox_usize(v_x_849_);
lean_dec(v_x_849_);
v_x_2781__boxed_854_ = lean_unbox_usize(v_x_850_);
lean_dec(v_x_850_);
v_res_855_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__3_spec__5(v_00_u03b2_847_, v_x_848_, v_x_2780__boxed_853_, v_x_2781__boxed_854_, v_x_851_, v_x_852_);
return v_res_855_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00main_spec__6_spec__9(mut v_00_u03b2_856_: *mut lean_object, mut v_x_857_: *mut lean_object, mut v_x_858_: usize, mut v_x_859_: *mut lean_object) -> *mut lean_object{
let mut v___x_860_: *mut lean_object = core::ptr::null_mut(); 
v___x_860_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00main_spec__6_spec__9___redArg(v_x_857_, v_x_858_, v_x_859_);
return v___x_860_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00main_spec__6_spec__9___boxed(mut v_00_u03b2_861_: *mut lean_object, mut v_x_862_: *mut lean_object, mut v_x_863_: *mut lean_object, mut v_x_864_: *mut lean_object) -> *mut lean_object{
let mut v_x_2797__boxed_865_: usize = 0; let mut v_res_866_: *mut lean_object = core::ptr::null_mut(); 
v_x_2797__boxed_865_ = lean_unbox_usize(v_x_863_);
lean_dec(v_x_863_);
v_res_866_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00main_spec__6_spec__9(v_00_u03b2_861_, v_x_862_, v_x_2797__boxed_865_, v_x_864_);
lean_dec(v_x_864_);
return v_res_866_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00main_spec__7_spec__11(mut v_00_u03b2_867_: *mut lean_object, mut v_x_868_: *mut lean_object, mut v_x_869_: usize, mut v_x_870_: *mut lean_object) -> *mut lean_object{
let mut v___x_871_: *mut lean_object = core::ptr::null_mut(); 
v___x_871_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00main_spec__7_spec__11___redArg(v_x_868_, v_x_869_, v_x_870_);
return v___x_871_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00main_spec__7_spec__11___boxed(mut v_00_u03b2_872_: *mut lean_object, mut v_x_873_: *mut lean_object, mut v_x_874_: *mut lean_object, mut v_x_875_: *mut lean_object) -> *mut lean_object{
let mut v_x_2808__boxed_876_: usize = 0; let mut v_res_877_: *mut lean_object = core::ptr::null_mut(); 
v_x_2808__boxed_876_ = lean_unbox_usize(v_x_874_);
lean_dec(v_x_874_);
v_res_877_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00main_spec__7_spec__11(v_00_u03b2_872_, v_x_873_, v_x_2808__boxed_876_, v_x_875_);
lean_dec(v_x_875_);
lean_dec_ref(v_x_873_);
return v_res_877_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__3_spec__5_spec__8(mut v_00_u03b2_878_: *mut lean_object, mut v_n_879_: *mut lean_object, mut v_k_880_: *mut lean_object, mut v_v_881_: *mut lean_object) -> *mut lean_object{
let mut v___x_882_: *mut lean_object = core::ptr::null_mut(); 
v___x_882_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__3_spec__5_spec__8___redArg(v_n_879_, v_k_880_, v_v_881_);
return v___x_882_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__3_spec__5_spec__9(mut v_00_u03b2_883_: *mut lean_object, mut v_depth_884_: usize, mut v_keys_885_: *mut lean_object, mut v_vals_886_: *mut lean_object, mut v_heq_887_: *mut lean_object, mut v_i_888_: *mut lean_object, mut v_entries_889_: *mut lean_object) -> *mut lean_object{
let mut v___x_890_: *mut lean_object = core::ptr::null_mut(); 
v___x_890_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__3_spec__5_spec__9___redArg(v_depth_884_, v_keys_885_, v_vals_886_, v_i_888_, v_entries_889_);
return v___x_890_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__3_spec__5_spec__9___boxed(mut v_00_u03b2_891_: *mut lean_object, mut v_depth_892_: *mut lean_object, mut v_keys_893_: *mut lean_object, mut v_vals_894_: *mut lean_object, mut v_heq_895_: *mut lean_object, mut v_i_896_: *mut lean_object, mut v_entries_897_: *mut lean_object) -> *mut lean_object{
let mut v_depth_boxed_898_: usize = 0; let mut v_res_899_: *mut lean_object = core::ptr::null_mut(); 
v_depth_boxed_898_ = lean_unbox_usize(v_depth_892_);
lean_dec(v_depth_892_);
v_res_899_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__3_spec__5_spec__9(v_00_u03b2_891_, v_depth_boxed_898_, v_keys_893_, v_vals_894_, v_heq_895_, v_i_896_, v_entries_897_);
lean_dec_ref(v_vals_894_);
lean_dec_ref(v_keys_893_);
return v_res_899_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00main_spec__7_spec__11_spec__15(mut v_00_u03b2_900_: *mut lean_object, mut v_keys_901_: *mut lean_object, mut v_vals_902_: *mut lean_object, mut v_heq_903_: *mut lean_object, mut v_i_904_: *mut lean_object, mut v_k_905_: *mut lean_object) -> *mut lean_object{
let mut v___x_906_: *mut lean_object = core::ptr::null_mut(); 
v___x_906_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00main_spec__7_spec__11_spec__15___redArg(v_keys_901_, v_vals_902_, v_i_904_, v_k_905_);
return v___x_906_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00main_spec__7_spec__11_spec__15___boxed(mut v_00_u03b2_907_: *mut lean_object, mut v_keys_908_: *mut lean_object, mut v_vals_909_: *mut lean_object, mut v_heq_910_: *mut lean_object, mut v_i_911_: *mut lean_object, mut v_k_912_: *mut lean_object) -> *mut lean_object{
let mut v_res_913_: *mut lean_object = core::ptr::null_mut(); 
v_res_913_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00main_spec__7_spec__11_spec__15(v_00_u03b2_907_, v_keys_908_, v_vals_909_, v_heq_910_, v_i_911_, v_k_912_);
lean_dec(v_k_912_);
lean_dec_ref(v_vals_909_);
lean_dec_ref(v_keys_908_);
return v_res_913_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__3_spec__5_spec__8_spec__12(mut v_00_u03b2_914_: *mut lean_object, mut v_x_915_: *mut lean_object, mut v_x_916_: *mut lean_object, mut v_x_917_: *mut lean_object, mut v_x_918_: *mut lean_object) -> *mut lean_object{
let mut v___x_919_: *mut lean_object = core::ptr::null_mut(); 
v___x_919_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00main_spec__3_spec__5_spec__8_spec__12___redArg(v_x_915_, v_x_916_, v_x_917_, v_x_918_);
return v___x_919_;
}
static mut _G_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn initialize_phashmap2(builtin: u8) -> *mut lean_object {
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
  let res = initialize_phashmap2(1 /* builtin */);
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
