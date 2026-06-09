// Lean compiler output
// Module: phashmap
// Imports: Init Init Lean.Data.PersistentHashMap Lean.Data.Format
use lean_runtime::generated_abi::*;
use lean_init::Init::*;
use lean_lean::Lean::Data::PersistentHashMap::*;
use lean_lean::Lean::Data::Format::*;
use lean_init::Init::Prelude::*;
use lean_init::Init::Data::UInt::BasicAux::*;
use lean_init::Init::Data::UInt::Basic::*;
use lean_init::Init::Data::Repr::*;
use lean_init::Init::Data::String::Defs::*;
use lean_init::Init::Data::String::Bootstrap::*;
use lean_init::Init::System::IO::*;
use lean_init::Init::Data::Int::Basic::*;
use lean_init::Init::Data::Array::Set::*;
use lean_init::Init::Data::Array::Basic::*;
extern "C" {
    fn lean_string_append(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_string_push(_: *mut lean_object, _: u32) -> *mut lean_object;
    fn lean_get_stdout() -> *mut lean_object;
    fn lean_array_push(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
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
static mut l_Lean_PersistentHashMap_empty___at___00mkMap_spec__1___closed__0_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_PersistentHashMap_empty___at___00mkMap_spec__1___closed__0: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_empty___at___00mkMap_spec__1___closed__1_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_PersistentHashMap_empty___at___00mkMap_spec__1___closed__1: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMap_spec__0_spec__0___redArg___closed__0_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMap_spec__0_spec__0___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMap_spec__0_spec__0___redArg___closed__1_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMap_spec__0_spec__0___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMap_spec__0_spec__0___redArg___closed__2_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMap_spec__0_spec__0___redArg___closed__2: *mut lean_object = core::ptr::null_mut();
static mut l_mkMap___closed__0_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_mkMap___closed__0: *mut lean_object = core::ptr::null_mut();
pub static l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00check_spec__2___redArg___closed__0_value: lean_string_object<16> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 102, 105, 110, 100, 32, 0]};
static mut l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00check_spec__2___redArg___closed__0: *mut lean_object = core::ptr::addr_of!(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00check_spec__2___redArg___closed__0_value) as *mut lean_object;
pub static l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00check_spec__2___redArg___closed__1_value: lean_string_object<18> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 118, 97, 108, 117, 101, 32, 0]};
static mut l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00check_spec__2___redArg___closed__1: *mut lean_object = core::ptr::addr_of!(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00check_spec__2___redArg___closed__1_value) as *mut lean_object;
pub static l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00check2_spec__1___redArg___closed__0_value: lean_string_object<24> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [109, 97, 112, 112, 105, 110, 103, 32, 115, 116, 105, 108, 108, 32, 99, 111, 110, 116, 97, 105, 110, 115, 32, 0]};
static mut l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00check2_spec__1___redArg___closed__0: *mut lean_object = core::ptr::addr_of!(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00check2_spec__1___redArg___closed__0_value) as *mut lean_object;
pub static l_Lean_PersistentHashMap_stats___at___00main_spec__0___redArg___closed__0_value: lean_ctor_object<4> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*4 + 0) as u16, m_other: 4, m_tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut lean_object,((( 0 as usize) << 1) | 1) as *mut lean_object,((( 0 as usize) << 1) | 1) as *mut lean_object,((( 0 as usize) << 1) | 1) as *mut lean_object] };
static mut l_Lean_PersistentHashMap_stats___at___00main_spec__0___redArg___closed__0: *mut lean_object = core::ptr::addr_of!(l_Lean_PersistentHashMap_stats___at___00main_spec__0___redArg___closed__0_value) as *mut lean_object;
static mut l_main___redArg___closed__0_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___redArg___closed__0: *mut lean_object = core::ptr::null_mut();
static mut l_main___redArg___closed__1_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___redArg___closed__1: *mut lean_object = core::ptr::null_mut();
static mut l_main___redArg___closed__2_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___redArg___closed__2: *mut lean_object = core::ptr::null_mut();
static mut l_main___redArg___closed__3_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___redArg___closed__3: *mut lean_object = core::ptr::null_mut();
static mut l_main___redArg___closed__4_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___redArg___closed__4: *mut lean_object = core::ptr::null_mut();
static mut l_main___redArg___closed__5_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___redArg___closed__5: *mut lean_object = core::ptr::null_mut();
static mut l_main___redArg___closed__6_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___redArg___closed__6: *mut lean_object = core::ptr::null_mut();
static mut l_main___redArg___closed__7_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___redArg___closed__7: *mut lean_object = core::ptr::null_mut();
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
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_PersistentHashMap_empty___at___00mkMap_spec__1___closed__0() -> *mut lean_object{
let mut v___x_313_: *mut lean_object = core::ptr::null_mut(); 
v___x_313_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_313_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_PersistentHashMap_empty___at___00mkMap_spec__1___closed__1() -> *mut lean_object{
let mut v___x_314_: *mut lean_object = core::ptr::null_mut(); let mut v___x_315_: *mut lean_object = core::ptr::null_mut(); 
v___x_314_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00mkMap_spec__1___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00mkMap_spec__1___closed__0_once), _init_l_Lean_PersistentHashMap_empty___at___00mkMap_spec__1___closed__0);
v___x_315_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_315_, 0, v___x_314_);
return v___x_315_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_empty___at___00mkMap_spec__1(mut v_00_u03b2_316_: *mut lean_object) -> *mut lean_object{
let mut v___x_317_: *mut lean_object = core::ptr::null_mut(); 
v___x_317_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00mkMap_spec__1___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00mkMap_spec__1___closed__1_once), _init_l_Lean_PersistentHashMap_empty___at___00mkMap_spec__1___closed__1);
return v___x_317_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMap_spec__0_spec__0_spec__2_spec__4___redArg(mut v_x_318_: *mut lean_object, mut v_x_319_: *mut lean_object, mut v_x_320_: *mut lean_object, mut v_x_321_: *mut lean_object) -> *mut lean_object{
let mut v_ks_322_: *mut lean_object = core::ptr::null_mut(); let mut v_vs_323_: *mut lean_object = core::ptr::null_mut(); let mut v___x_325_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_326_: u8 = 0; let mut v___x_327_: *mut lean_object = core::ptr::null_mut(); let mut v___x_328_: u8 = 0; let mut v___x_329_: *mut lean_object = core::ptr::null_mut(); let mut v___x_330_: *mut lean_object = core::ptr::null_mut(); let mut v___x_332_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_333_: *mut lean_object = core::ptr::null_mut(); let mut v_k_x27_334_: *mut lean_object = core::ptr::null_mut(); let mut v___x_335_: u8 = 0; let mut v___x_337_: *mut lean_object = core::ptr::null_mut(); let mut v___x_338_: *mut lean_object = core::ptr::null_mut(); let mut v___x_339_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_341_: *mut lean_object = core::ptr::null_mut(); let mut v___x_342_: *mut lean_object = core::ptr::null_mut(); let mut v___x_343_: *mut lean_object = core::ptr::null_mut(); let mut v___x_345_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_346_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_347_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v_ks_322_ = lean_ctor_get(v_x_318_, 0);
v_vs_323_ = lean_ctor_get(v_x_318_, 1);
v_isSharedCheck_347_ = (!lean_is_exclusive(v_x_318_)) as u8;
if v_isSharedCheck_347_ == 0 {
v___x_325_ = v_x_318_;
v_isShared_326_ = v_isSharedCheck_347_;
state = 1; continue;
} else {
lean_inc(v_vs_323_);
lean_inc(v_ks_322_);
lean_dec(v_x_318_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_347_;
state = 1; continue;
}
}
1 => {
v___x_327_ = lean_array_get_size(v_ks_322_);
v___x_328_ = lean_nat_dec_lt(v_x_319_, v___x_327_);
if v___x_328_ == 0 {
lean_dec(v_x_319_);
v___x_329_ = lean_array_push(v_ks_322_, v_x_320_);
v___x_330_ = lean_array_push(v_vs_323_, v_x_321_);
if v_isShared_326_ == 0 {
lean_ctor_set(v___x_325_, 1, v___x_330_);
lean_ctor_set(v___x_325_, 0, v___x_329_);
v___x_332_ = v___x_325_;
state = 2; continue;
} else {
v_reuseFailAlloc_333_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v___x_329_);
lean_ctor_set(v_reuseFailAlloc_333_, 1, v___x_330_);
v___x_332_ = v_reuseFailAlloc_333_;
state = 2; continue;
}
} else {
v_k_x27_334_ = lean_array_fget_borrowed(v_ks_322_, v_x_319_);
v___x_335_ = lean_nat_dec_eq(v_x_320_, v_k_x27_334_);
if v___x_335_ == 0 {
if v_isShared_326_ == 0 {
v___x_337_ = v___x_325_;
state = 3; continue;
} else {
v_reuseFailAlloc_341_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v_ks_322_);
lean_ctor_set(v_reuseFailAlloc_341_, 1, v_vs_323_);
v___x_337_ = v_reuseFailAlloc_341_;
state = 3; continue;
}
} else {
v___x_342_ = lean_array_fset(v_ks_322_, v_x_319_, v_x_320_);
v___x_343_ = lean_array_fset(v_vs_323_, v_x_319_, v_x_321_);
lean_dec(v_x_319_);
if v_isShared_326_ == 0 {
lean_ctor_set(v___x_325_, 1, v___x_343_);
lean_ctor_set(v___x_325_, 0, v___x_342_);
v___x_345_ = v___x_325_;
state = 4; continue;
} else {
v_reuseFailAlloc_346_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v___x_342_);
lean_ctor_set(v_reuseFailAlloc_346_, 1, v___x_343_);
v___x_345_ = v_reuseFailAlloc_346_;
state = 4; continue;
}
}
}
}
2 => {
return v___x_332_;
}
3 => {
v___x_338_ = lean_unsigned_to_nat(1);
v___x_339_ = lean_nat_add(v_x_319_, v___x_338_);
lean_dec(v_x_319_);
v_x_318_ = v___x_337_;
v_x_319_ = v___x_339_;
state = 0; continue;
}
4 => {
return v___x_345_;
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMap_spec__0_spec__0_spec__2___redArg(mut v_n_348_: *mut lean_object, mut v_k_349_: *mut lean_object, mut v_v_350_: *mut lean_object) -> *mut lean_object{
let mut v___x_351_: *mut lean_object = core::ptr::null_mut(); let mut v___x_352_: *mut lean_object = core::ptr::null_mut(); 
v___x_351_ = lean_unsigned_to_nat(0);
v___x_352_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMap_spec__0_spec__0_spec__2_spec__4___redArg(v_n_348_, v___x_351_, v_k_349_, v_v_350_);
return v___x_352_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMap_spec__0_spec__0___redArg___closed__0() -> usize{
let mut v___x_353_: usize = 0; let mut v___x_354_: usize = 0; let mut v___x_355_: usize = 0; 
v___x_353_ = 5usize;
v___x_354_ = 1usize;
v___x_355_ = lean_usize_shift_left(v___x_354_, v___x_353_);
return v___x_355_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMap_spec__0_spec__0___redArg___closed__1() -> usize{
let mut v___x_356_: usize = 0; let mut v___x_357_: usize = 0; let mut v___x_358_: usize = 0; 
v___x_356_ = 1usize;
v___x_357_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMap_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMap_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMap_spec__0_spec__0___redArg___closed__0);
v___x_358_ = lean_usize_sub(v___x_357_, v___x_356_);
return v___x_358_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMap_spec__0_spec__0___redArg___closed__2() -> *mut lean_object{
let mut v___x_359_: *mut lean_object = core::ptr::null_mut(); 
v___x_359_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_359_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMap_spec__0_spec__0___redArg(mut v_x_360_: *mut lean_object, mut v_x_361_: usize, mut v_x_362_: usize, mut v_x_363_: *mut lean_object, mut v_x_364_: *mut lean_object) -> *mut lean_object{
let mut v_es_365_: *mut lean_object = core::ptr::null_mut(); let mut v___x_366_: usize = 0; let mut v___x_367_: usize = 0; let mut v___x_368_: usize = 0; let mut v___x_369_: usize = 0; let mut v_j_370_: *mut lean_object = core::ptr::null_mut(); let mut v___x_371_: *mut lean_object = core::ptr::null_mut(); let mut v___x_372_: u8 = 0; let mut v___x_374_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_375_: u8 = 0; let mut v_v_376_: *mut lean_object = core::ptr::null_mut(); let mut v___x_377_: *mut lean_object = core::ptr::null_mut(); let mut v_xs_x27_378_: *mut lean_object = core::ptr::null_mut(); let mut v___y_380_: *mut lean_object = core::ptr::null_mut(); let mut v___x_381_: *mut lean_object = core::ptr::null_mut(); let mut v___x_383_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_384_: *mut lean_object = core::ptr::null_mut(); let mut v_key_385_: *mut lean_object = core::ptr::null_mut(); let mut v_val_386_: *mut lean_object = core::ptr::null_mut(); let mut v___x_388_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_389_: u8 = 0; let mut v___x_390_: u8 = 0; let mut v___x_391_: *mut lean_object = core::ptr::null_mut(); let mut v___x_392_: *mut lean_object = core::ptr::null_mut(); let mut v___x_394_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_395_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_396_: u8 = 0; let mut v_node_397_: *mut lean_object = core::ptr::null_mut(); let mut v___x_399_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_400_: u8 = 0; let mut v___x_401_: usize = 0; let mut v___x_402_: usize = 0; let mut v___x_403_: *mut lean_object = core::ptr::null_mut(); let mut v___x_405_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_406_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_407_: u8 = 0; let mut v___x_408_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_409_: u8 = 0; let mut v_unused_410_: *mut lean_object = core::ptr::null_mut(); let mut v_ks_411_: *mut lean_object = core::ptr::null_mut(); let mut v_vs_412_: *mut lean_object = core::ptr::null_mut(); let mut v___x_414_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_415_: u8 = 0; let mut v___x_417_: *mut lean_object = core::ptr::null_mut(); let mut v_newNode_418_: *mut lean_object = core::ptr::null_mut(); let mut v___y_420_: u8 = 0; let mut v_ks_421_: *mut lean_object = core::ptr::null_mut(); let mut v_vs_422_: *mut lean_object = core::ptr::null_mut(); let mut v___x_423_: *mut lean_object = core::ptr::null_mut(); let mut v___x_424_: *mut lean_object = core::ptr::null_mut(); let mut v___x_425_: *mut lean_object = core::ptr::null_mut(); let mut v___x_426_: usize = 0; let mut v___x_427_: u8 = 0; let mut v___x_428_: *mut lean_object = core::ptr::null_mut(); let mut v___x_429_: *mut lean_object = core::ptr::null_mut(); let mut v___x_430_: u8 = 0; let mut v_reuseFailAlloc_431_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_432_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_x_360_) == 0 {
v_es_365_ = lean_ctor_get(v_x_360_, 0);
v___x_366_ = 5usize;
v___x_367_ = 1usize;
v___x_368_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMap_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMap_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMap_spec__0_spec__0___redArg___closed__1);
v___x_369_ = lean_usize_land(v_x_361_, v___x_368_);
v_j_370_ = lean_usize_to_nat(v___x_369_);
v___x_371_ = lean_array_get_size(v_es_365_);
v___x_372_ = lean_nat_dec_lt(v_j_370_, v___x_371_);
if v___x_372_ == 0 {
lean_dec(v_j_370_);
lean_dec(v_x_364_);
lean_dec(v_x_363_);
return v_x_360_;
} else {
lean_inc_ref(v_es_365_);
v_isSharedCheck_409_ = (!lean_is_exclusive(v_x_360_)) as u8;
if v_isSharedCheck_409_ == 0 {
v_unused_410_ = lean_ctor_get(v_x_360_, 0);
lean_dec(v_unused_410_);
v___x_374_ = v_x_360_;
v_isShared_375_ = v_isSharedCheck_409_;
state = 1; continue;
} else {
lean_dec(v_x_360_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_409_;
state = 1; continue;
}
}
} else {
v_ks_411_ = lean_ctor_get(v_x_360_, 0);
v_vs_412_ = lean_ctor_get(v_x_360_, 1);
v_isSharedCheck_432_ = (!lean_is_exclusive(v_x_360_)) as u8;
if v_isSharedCheck_432_ == 0 {
v___x_414_ = v_x_360_;
v_isShared_415_ = v_isSharedCheck_432_;
state = 8; continue;
} else {
lean_inc(v_vs_412_);
lean_inc(v_ks_411_);
lean_dec(v_x_360_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_432_;
state = 8; continue;
}
}
}
1 => {
v_v_376_ = lean_array_fget(v_es_365_, v_j_370_);
v___x_377_ = lean_box(0);
v_xs_x27_378_ = lean_array_fset(v_es_365_, v_j_370_, v___x_377_);
match lean_obj_tag(v_v_376_)
{
0 => {
v_key_385_ = lean_ctor_get(v_v_376_, 0);
v_val_386_ = lean_ctor_get(v_v_376_, 1);
v_isSharedCheck_396_ = (!lean_is_exclusive(v_v_376_)) as u8;
if v_isSharedCheck_396_ == 0 {
v___x_388_ = v_v_376_;
v_isShared_389_ = v_isSharedCheck_396_;
state = 4; continue;
} else {
lean_inc(v_val_386_);
lean_inc(v_key_385_);
lean_dec(v_v_376_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_396_;
state = 4; continue;
}
}
1 => {
v_node_397_ = lean_ctor_get(v_v_376_, 0);
v_isSharedCheck_407_ = (!lean_is_exclusive(v_v_376_)) as u8;
if v_isSharedCheck_407_ == 0 {
v___x_399_ = v_v_376_;
v_isShared_400_ = v_isSharedCheck_407_;
state = 6; continue;
} else {
lean_inc(v_node_397_);
lean_dec(v_v_376_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_407_;
state = 6; continue;
}
}
_ => {
v___x_408_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_408_, 0, v_x_363_);
lean_ctor_set(v___x_408_, 1, v_x_364_);
v___y_380_ = v___x_408_;
state = 2; continue;
}
}
}
2 => {
v___x_381_ = lean_array_fset(v_xs_x27_378_, v_j_370_, v___y_380_);
lean_dec(v_j_370_);
if v_isShared_375_ == 0 {
lean_ctor_set(v___x_374_, 0, v___x_381_);
v___x_383_ = v___x_374_;
state = 3; continue;
} else {
v_reuseFailAlloc_384_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v___x_381_);
v___x_383_ = v_reuseFailAlloc_384_;
state = 3; continue;
}
}
3 => {
return v___x_383_;
}
4 => {
v___x_390_ = lean_nat_dec_eq(v_x_363_, v_key_385_);
if v___x_390_ == 0 {
lean_del_object(v___x_388_);
v___x_391_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_385_, v_val_386_, v_x_363_, v_x_364_);
v___x_392_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v___x_392_, 0, v___x_391_);
v___y_380_ = v___x_392_;
state = 2; continue;
} else {
lean_dec(v_val_386_);
lean_dec(v_key_385_);
if v_isShared_389_ == 0 {
lean_ctor_set(v___x_388_, 1, v_x_364_);
lean_ctor_set(v___x_388_, 0, v_x_363_);
v___x_394_ = v___x_388_;
state = 5; continue;
} else {
v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v_x_363_);
lean_ctor_set(v_reuseFailAlloc_395_, 1, v_x_364_);
v___x_394_ = v_reuseFailAlloc_395_;
state = 5; continue;
}
}
}
5 => {
v___y_380_ = v___x_394_;
state = 2; continue;
}
6 => {
v___x_401_ = lean_usize_shift_right(v_x_361_, v___x_366_);
v___x_402_ = lean_usize_add(v_x_362_, v___x_367_);
v___x_403_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMap_spec__0_spec__0___redArg(v_node_397_, v___x_401_, v___x_402_, v_x_363_, v_x_364_);
if v_isShared_400_ == 0 {
lean_ctor_set(v___x_399_, 0, v___x_403_);
v___x_405_ = v___x_399_;
state = 7; continue;
} else {
v_reuseFailAlloc_406_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v___x_403_);
v___x_405_ = v_reuseFailAlloc_406_;
state = 7; continue;
}
}
7 => {
v___y_380_ = v___x_405_;
state = 2; continue;
}
8 => {
if v_isShared_415_ == 0 {
v___x_417_ = v___x_414_;
state = 9; continue;
} else {
v_reuseFailAlloc_431_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_ks_411_);
lean_ctor_set(v_reuseFailAlloc_431_, 1, v_vs_412_);
v___x_417_ = v_reuseFailAlloc_431_;
state = 9; continue;
}
}
9 => {
v_newNode_418_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMap_spec__0_spec__0_spec__2___redArg(v___x_417_, v_x_363_, v_x_364_);
v___x_426_ = 7usize;
v___x_427_ = lean_usize_dec_le(v___x_426_, v_x_362_);
if v___x_427_ == 0 {
v___x_428_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_418_);
v___x_429_ = lean_unsigned_to_nat(4);
v___x_430_ = lean_nat_dec_lt(v___x_428_, v___x_429_);
lean_dec(v___x_428_);
v___y_420_ = v___x_430_;
state = 10; continue;
} else {
v___y_420_ = v___x_427_;
state = 10; continue;
}
}
10 => {
if v___y_420_ == 0 {
v_ks_421_ = lean_ctor_get(v_newNode_418_, 0);
lean_inc_ref(v_ks_421_);
v_vs_422_ = lean_ctor_get(v_newNode_418_, 1);
lean_inc_ref(v_vs_422_);
lean_dec_ref(v_newNode_418_);
v___x_423_ = lean_unsigned_to_nat(0);
v___x_424_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMap_spec__0_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMap_spec__0_spec__0___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMap_spec__0_spec__0___redArg___closed__2);
v___x_425_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMap_spec__0_spec__0_spec__3___redArg(v_x_362_, v_ks_421_, v_vs_422_, v___x_423_, v___x_424_);
lean_dec_ref(v_vs_422_);
lean_dec_ref(v_ks_421_);
return v___x_425_;
} else {
return v_newNode_418_;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMap_spec__0_spec__0_spec__3___redArg(mut v_depth_433_: usize, mut v_keys_434_: *mut lean_object, mut v_vals_435_: *mut lean_object, mut v_i_436_: *mut lean_object, mut v_entries_437_: *mut lean_object) -> *mut lean_object{
let mut v___x_438_: *mut lean_object = core::ptr::null_mut(); let mut v___x_439_: u8 = 0; let mut v_k_440_: *mut lean_object = core::ptr::null_mut(); let mut v_v_441_: *mut lean_object = core::ptr::null_mut(); let mut v___x_442_: u64 = 0; let mut v_h_443_: usize = 0; let mut v___x_444_: usize = 0; let mut v___x_445_: *mut lean_object = core::ptr::null_mut(); let mut v___x_446_: usize = 0; let mut v___x_447_: usize = 0; let mut v___x_448_: usize = 0; let mut v_h_449_: usize = 0; let mut v___x_450_: *mut lean_object = core::ptr::null_mut(); let mut v___x_451_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_438_ = lean_array_get_size(v_keys_434_);
v___x_439_ = lean_nat_dec_lt(v_i_436_, v___x_438_);
if v___x_439_ == 0 {
lean_dec(v_i_436_);
return v_entries_437_;
} else {
v_k_440_ = lean_array_fget_borrowed(v_keys_434_, v_i_436_);
v_v_441_ = lean_array_fget_borrowed(v_vals_435_, v_i_436_);
v___x_442_ = lean_uint64_of_nat(v_k_440_);
v_h_443_ = lean_uint64_to_usize(v___x_442_);
v___x_444_ = 5usize;
v___x_445_ = lean_unsigned_to_nat(1);
v___x_446_ = 1usize;
v___x_447_ = lean_usize_sub(v_depth_433_, v___x_446_);
v___x_448_ = lean_usize_mul(v___x_444_, v___x_447_);
v_h_449_ = lean_usize_shift_right(v_h_443_, v___x_448_);
v___x_450_ = lean_nat_add(v_i_436_, v___x_445_);
lean_dec(v_i_436_);
lean_inc(v_v_441_);
lean_inc(v_k_440_);
v___x_451_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMap_spec__0_spec__0___redArg(v_entries_437_, v_h_449_, v_depth_433_, v_k_440_, v_v_441_);
v_i_436_ = v___x_450_;
v_entries_437_ = v___x_451_;
state = 0; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMap_spec__0_spec__0_spec__3___redArg___boxed(mut v_depth_453_: *mut lean_object, mut v_keys_454_: *mut lean_object, mut v_vals_455_: *mut lean_object, mut v_i_456_: *mut lean_object, mut v_entries_457_: *mut lean_object) -> *mut lean_object{
let mut v_depth_boxed_458_: usize = 0; let mut v_res_459_: *mut lean_object = core::ptr::null_mut(); 
v_depth_boxed_458_ = lean_unbox_usize(v_depth_453_);
lean_dec(v_depth_453_);
v_res_459_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMap_spec__0_spec__0_spec__3___redArg(v_depth_boxed_458_, v_keys_454_, v_vals_455_, v_i_456_, v_entries_457_);
lean_dec_ref(v_vals_455_);
lean_dec_ref(v_keys_454_);
return v_res_459_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMap_spec__0_spec__0___redArg___boxed(mut v_x_460_: *mut lean_object, mut v_x_461_: *mut lean_object, mut v_x_462_: *mut lean_object, mut v_x_463_: *mut lean_object, mut v_x_464_: *mut lean_object) -> *mut lean_object{
let mut v_x_449__boxed_465_: usize = 0; let mut v_x_450__boxed_466_: usize = 0; let mut v_res_467_: *mut lean_object = core::ptr::null_mut(); 
v_x_449__boxed_465_ = lean_unbox_usize(v_x_461_);
lean_dec(v_x_461_);
v_x_450__boxed_466_ = lean_unbox_usize(v_x_462_);
lean_dec(v_x_462_);
v_res_467_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMap_spec__0_spec__0___redArg(v_x_460_, v_x_449__boxed_465_, v_x_450__boxed_466_, v_x_463_, v_x_464_);
return v_res_467_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_insert___at___00mkMap_spec__0___redArg(mut v_x_468_: *mut lean_object, mut v_x_469_: *mut lean_object, mut v_x_470_: *mut lean_object) -> *mut lean_object{
let mut v___x_471_: u64 = 0; let mut v___x_472_: usize = 0; let mut v___x_473_: usize = 0; let mut v___x_474_: *mut lean_object = core::ptr::null_mut(); 
v___x_471_ = lean_uint64_of_nat(v_x_469_);
v___x_472_ = lean_uint64_to_usize(v___x_471_);
v___x_473_ = 1usize;
v___x_474_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMap_spec__0_spec__0___redArg(v_x_468_, v___x_472_, v___x_473_, v_x_469_, v_x_470_);
return v___x_474_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00mkMap_spec__2___redArg(mut v_n_475_: *mut lean_object, mut v_j_476_: *mut lean_object, mut v_a_477_: *mut lean_object) -> *mut lean_object{
let mut v_zero_478_: *mut lean_object = core::ptr::null_mut(); let mut v_isZero_479_: u8 = 0; let mut v_one_480_: *mut lean_object = core::ptr::null_mut(); let mut v_n_481_: *mut lean_object = core::ptr::null_mut(); let mut v___x_482_: *mut lean_object = core::ptr::null_mut(); let mut v___x_483_: *mut lean_object = core::ptr::null_mut(); let mut v___x_484_: *mut lean_object = core::ptr::null_mut(); let mut v___x_485_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v_zero_478_ = lean_unsigned_to_nat(0);
v_isZero_479_ = lean_nat_dec_eq(v_j_476_, v_zero_478_);
if v_isZero_479_ == 1 {
lean_dec(v_j_476_);
return v_a_477_;
} else {
v_one_480_ = lean_unsigned_to_nat(1);
v_n_481_ = lean_nat_sub(v_j_476_, v_one_480_);
v___x_482_ = lean_nat_sub(v_n_475_, v_j_476_);
lean_dec(v_j_476_);
v___x_483_ = lean_unsigned_to_nat(10);
v___x_484_ = lean_nat_mul(v___x_482_, v___x_483_);
v___x_485_ = l_Lean_PersistentHashMap_insert___at___00mkMap_spec__0___redArg(v_a_477_, v___x_482_, v___x_484_);
v_j_476_ = v_n_481_;
v_a_477_ = v___x_485_;
state = 0; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00mkMap_spec__2___redArg___boxed(mut v_n_487_: *mut lean_object, mut v_j_488_: *mut lean_object, mut v_a_489_: *mut lean_object) -> *mut lean_object{
let mut v_res_490_: *mut lean_object = core::ptr::null_mut(); 
v_res_490_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00mkMap_spec__2___redArg(v_n_487_, v_j_488_, v_a_489_);
lean_dec(v_n_487_);
return v_res_490_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_mkMap___closed__0() -> *mut lean_object{
let mut v___x_491_: *mut lean_object = core::ptr::null_mut(); 
v___x_491_ = l_Lean_PersistentHashMap_empty___at___00mkMap_spec__1(lean_box(0));
return v___x_491_;
}
#[no_mangle] pub unsafe extern "C" fn l_mkMap(mut v_n_492_: *mut lean_object) -> *mut lean_object{
let mut v___x_493_: *mut lean_object = core::ptr::null_mut(); let mut v___x_494_: *mut lean_object = core::ptr::null_mut(); 
v___x_493_ = lean_obj_once(core::ptr::addr_of_mut!(l_mkMap___closed__0), core::ptr::addr_of_mut!(l_mkMap___closed__0_once), _init_l_mkMap___closed__0);
lean_inc(v_n_492_);
v___x_494_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00mkMap_spec__2___redArg(v_n_492_, v_n_492_, v___x_493_);
lean_dec(v_n_492_);
return v___x_494_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_insert___at___00mkMap_spec__0(mut v_00_u03b2_495_: *mut lean_object, mut v_x_496_: *mut lean_object, mut v_x_497_: *mut lean_object, mut v_x_498_: *mut lean_object) -> *mut lean_object{
let mut v___x_499_: *mut lean_object = core::ptr::null_mut(); 
v___x_499_ = l_Lean_PersistentHashMap_insert___at___00mkMap_spec__0___redArg(v_x_496_, v_x_497_, v_x_498_);
return v___x_499_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00mkMap_spec__2(mut v_n_500_: *mut lean_object, mut v_j_501_: *mut lean_object, mut v_a_502_: *mut lean_object, mut v_a_503_: *mut lean_object) -> *mut lean_object{
let mut v___x_504_: *mut lean_object = core::ptr::null_mut(); 
v___x_504_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00mkMap_spec__2___redArg(v_n_500_, v_j_501_, v_a_503_);
return v___x_504_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00mkMap_spec__2___boxed(mut v_n_505_: *mut lean_object, mut v_j_506_: *mut lean_object, mut v_a_507_: *mut lean_object, mut v_a_508_: *mut lean_object) -> *mut lean_object{
let mut v_res_509_: *mut lean_object = core::ptr::null_mut(); 
v_res_509_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00mkMap_spec__2(v_n_505_, v_j_506_, v_a_507_, v_a_508_);
lean_dec(v_n_505_);
return v_res_509_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMap_spec__0_spec__0(mut v_00_u03b2_510_: *mut lean_object, mut v_x_511_: *mut lean_object, mut v_x_512_: usize, mut v_x_513_: usize, mut v_x_514_: *mut lean_object, mut v_x_515_: *mut lean_object) -> *mut lean_object{
let mut v___x_516_: *mut lean_object = core::ptr::null_mut(); 
v___x_516_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMap_spec__0_spec__0___redArg(v_x_511_, v_x_512_, v_x_513_, v_x_514_, v_x_515_);
return v___x_516_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMap_spec__0_spec__0___boxed(mut v_00_u03b2_517_: *mut lean_object, mut v_x_518_: *mut lean_object, mut v_x_519_: *mut lean_object, mut v_x_520_: *mut lean_object, mut v_x_521_: *mut lean_object, mut v_x_522_: *mut lean_object) -> *mut lean_object{
let mut v_x_663__boxed_523_: usize = 0; let mut v_x_664__boxed_524_: usize = 0; let mut v_res_525_: *mut lean_object = core::ptr::null_mut(); 
v_x_663__boxed_523_ = lean_unbox_usize(v_x_519_);
lean_dec(v_x_519_);
v_x_664__boxed_524_ = lean_unbox_usize(v_x_520_);
lean_dec(v_x_520_);
v_res_525_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMap_spec__0_spec__0(v_00_u03b2_517_, v_x_518_, v_x_663__boxed_523_, v_x_664__boxed_524_, v_x_521_, v_x_522_);
return v_res_525_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMap_spec__0_spec__0_spec__2(mut v_00_u03b2_526_: *mut lean_object, mut v_n_527_: *mut lean_object, mut v_k_528_: *mut lean_object, mut v_v_529_: *mut lean_object) -> *mut lean_object{
let mut v___x_530_: *mut lean_object = core::ptr::null_mut(); 
v___x_530_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMap_spec__0_spec__0_spec__2___redArg(v_n_527_, v_k_528_, v_v_529_);
return v___x_530_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMap_spec__0_spec__0_spec__3(mut v_00_u03b2_531_: *mut lean_object, mut v_depth_532_: usize, mut v_keys_533_: *mut lean_object, mut v_vals_534_: *mut lean_object, mut v_heq_535_: *mut lean_object, mut v_i_536_: *mut lean_object, mut v_entries_537_: *mut lean_object) -> *mut lean_object{
let mut v___x_538_: *mut lean_object = core::ptr::null_mut(); 
v___x_538_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMap_spec__0_spec__0_spec__3___redArg(v_depth_532_, v_keys_533_, v_vals_534_, v_i_536_, v_entries_537_);
return v___x_538_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMap_spec__0_spec__0_spec__3___boxed(mut v_00_u03b2_539_: *mut lean_object, mut v_depth_540_: *mut lean_object, mut v_keys_541_: *mut lean_object, mut v_vals_542_: *mut lean_object, mut v_heq_543_: *mut lean_object, mut v_i_544_: *mut lean_object, mut v_entries_545_: *mut lean_object) -> *mut lean_object{
let mut v_depth_boxed_546_: usize = 0; let mut v_res_547_: *mut lean_object = core::ptr::null_mut(); 
v_depth_boxed_546_ = lean_unbox_usize(v_depth_540_);
lean_dec(v_depth_540_);
v_res_547_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMap_spec__0_spec__0_spec__3(v_00_u03b2_539_, v_depth_boxed_546_, v_keys_541_, v_vals_542_, v_heq_543_, v_i_544_, v_entries_545_);
lean_dec_ref(v_vals_542_);
lean_dec_ref(v_keys_541_);
return v_res_547_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMap_spec__0_spec__0_spec__2_spec__4(mut v_00_u03b2_548_: *mut lean_object, mut v_x_549_: *mut lean_object, mut v_x_550_: *mut lean_object, mut v_x_551_: *mut lean_object, mut v_x_552_: *mut lean_object) -> *mut lean_object{
let mut v___x_553_: *mut lean_object = core::ptr::null_mut(); 
v___x_553_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMap_spec__0_spec__0_spec__2_spec__4___redArg(v_x_549_, v_x_550_, v_x_551_, v_x_552_);
return v___x_553_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00check_spec__0_spec__0_spec__1___redArg(mut v_keys_554_: *mut lean_object, mut v_vals_555_: *mut lean_object, mut v_i_556_: *mut lean_object, mut v_k_557_: *mut lean_object) -> *mut lean_object{
let mut v___x_558_: *mut lean_object = core::ptr::null_mut(); let mut v___x_559_: u8 = 0; let mut v___x_560_: *mut lean_object = core::ptr::null_mut(); let mut v_k_x27_561_: *mut lean_object = core::ptr::null_mut(); let mut v___x_562_: u8 = 0; let mut v___x_563_: *mut lean_object = core::ptr::null_mut(); let mut v___x_564_: *mut lean_object = core::ptr::null_mut(); let mut v___x_566_: *mut lean_object = core::ptr::null_mut(); let mut v___x_567_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_558_ = lean_array_get_size(v_keys_554_);
v___x_559_ = lean_nat_dec_lt(v_i_556_, v___x_558_);
if v___x_559_ == 0 {
lean_dec(v_i_556_);
v___x_560_ = lean_box(0);
return v___x_560_;
} else {
v_k_x27_561_ = lean_array_fget_borrowed(v_keys_554_, v_i_556_);
v___x_562_ = lean_nat_dec_eq(v_k_557_, v_k_x27_561_);
if v___x_562_ == 0 {
v___x_563_ = lean_unsigned_to_nat(1);
v___x_564_ = lean_nat_add(v_i_556_, v___x_563_);
lean_dec(v_i_556_);
v_i_556_ = v___x_564_;
state = 0; continue;
} else {
v___x_566_ = lean_array_fget_borrowed(v_vals_555_, v_i_556_);
lean_dec(v_i_556_);
lean_inc(v___x_566_);
v___x_567_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v___x_567_, 0, v___x_566_);
return v___x_567_;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00check_spec__0_spec__0_spec__1___redArg___boxed(mut v_keys_568_: *mut lean_object, mut v_vals_569_: *mut lean_object, mut v_i_570_: *mut lean_object, mut v_k_571_: *mut lean_object) -> *mut lean_object{
let mut v_res_572_: *mut lean_object = core::ptr::null_mut(); 
v_res_572_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00check_spec__0_spec__0_spec__1___redArg(v_keys_568_, v_vals_569_, v_i_570_, v_k_571_);
lean_dec(v_k_571_);
lean_dec_ref(v_vals_569_);
lean_dec_ref(v_keys_568_);
return v_res_572_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00check_spec__0_spec__0___redArg(mut v_x_573_: *mut lean_object, mut v_x_574_: usize, mut v_x_575_: *mut lean_object) -> *mut lean_object{
let mut v_es_576_: *mut lean_object = core::ptr::null_mut(); let mut v___x_577_: *mut lean_object = core::ptr::null_mut(); let mut v___x_578_: usize = 0; let mut v___x_579_: usize = 0; let mut v___x_580_: usize = 0; let mut v_j_581_: *mut lean_object = core::ptr::null_mut(); let mut v___x_582_: *mut lean_object = core::ptr::null_mut(); let mut v_key_583_: *mut lean_object = core::ptr::null_mut(); let mut v_val_584_: *mut lean_object = core::ptr::null_mut(); let mut v___x_585_: u8 = 0; let mut v___x_586_: *mut lean_object = core::ptr::null_mut(); let mut v___x_587_: *mut lean_object = core::ptr::null_mut(); let mut v_node_588_: *mut lean_object = core::ptr::null_mut(); let mut v___x_589_: usize = 0; let mut v___x_591_: *mut lean_object = core::ptr::null_mut(); let mut v_ks_592_: *mut lean_object = core::ptr::null_mut(); let mut v_vs_593_: *mut lean_object = core::ptr::null_mut(); let mut v___x_594_: *mut lean_object = core::ptr::null_mut(); let mut v___x_595_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_x_573_) == 0 {
v_es_576_ = lean_ctor_get(v_x_573_, 0);
v___x_577_ = lean_box(2);
v___x_578_ = 5usize;
v___x_579_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMap_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMap_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMap_spec__0_spec__0___redArg___closed__1);
v___x_580_ = lean_usize_land(v_x_574_, v___x_579_);
v_j_581_ = lean_usize_to_nat(v___x_580_);
v___x_582_ = lean_array_get_borrowed(v___x_577_, v_es_576_, v_j_581_);
lean_dec(v_j_581_);
match lean_obj_tag(v___x_582_)
{
0 => {
v_key_583_ = lean_ctor_get(v___x_582_, 0);
v_val_584_ = lean_ctor_get(v___x_582_, 1);
v___x_585_ = lean_nat_dec_eq(v_x_575_, v_key_583_);
if v___x_585_ == 0 {
v___x_586_ = lean_box(0);
return v___x_586_;
} else {
lean_inc(v_val_584_);
v___x_587_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v___x_587_, 0, v_val_584_);
return v___x_587_;
}
}
1 => {
v_node_588_ = lean_ctor_get(v___x_582_, 0);
v___x_589_ = lean_usize_shift_right(v_x_574_, v___x_578_);
v_x_573_ = v_node_588_;
v_x_574_ = v___x_589_;
state = 0; continue;
}
_ => {
v___x_591_ = lean_box(0);
return v___x_591_;
}
}
} else {
v_ks_592_ = lean_ctor_get(v_x_573_, 0);
v_vs_593_ = lean_ctor_get(v_x_573_, 1);
v___x_594_ = lean_unsigned_to_nat(0);
v___x_595_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00check_spec__0_spec__0_spec__1___redArg(v_ks_592_, v_vs_593_, v___x_594_, v_x_575_);
return v___x_595_;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00check_spec__0_spec__0___redArg___boxed(mut v_x_596_: *mut lean_object, mut v_x_597_: *mut lean_object, mut v_x_598_: *mut lean_object) -> *mut lean_object{
let mut v_x_542__boxed_599_: usize = 0; let mut v_res_600_: *mut lean_object = core::ptr::null_mut(); 
v_x_542__boxed_599_ = lean_unbox_usize(v_x_597_);
lean_dec(v_x_597_);
v_res_600_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00check_spec__0_spec__0___redArg(v_x_596_, v_x_542__boxed_599_, v_x_598_);
lean_dec(v_x_598_);
lean_dec_ref(v_x_596_);
return v_res_600_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_find_x3f___at___00check_spec__0___redArg(mut v_x_601_: *mut lean_object, mut v_x_602_: *mut lean_object) -> *mut lean_object{
let mut v___x_603_: u64 = 0; let mut v___x_604_: usize = 0; let mut v___x_605_: *mut lean_object = core::ptr::null_mut(); 
v___x_603_ = lean_uint64_of_nat(v_x_602_);
v___x_604_ = lean_uint64_to_usize(v___x_603_);
v___x_605_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00check_spec__0_spec__0___redArg(v_x_601_, v___x_604_, v_x_602_);
return v___x_605_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_find_x3f___at___00check_spec__0___redArg___boxed(mut v_x_606_: *mut lean_object, mut v_x_607_: *mut lean_object) -> *mut lean_object{
let mut v_res_608_: *mut lean_object = core::ptr::null_mut(); 
v_res_608_ = l_Lean_PersistentHashMap_find_x3f___at___00check_spec__0___redArg(v_x_606_, v_x_607_);
lean_dec(v_x_607_);
lean_dec_ref(v_x_606_);
return v_res_608_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00check_spec__1_spec__2(mut v_s_609_: *mut lean_object) -> *mut lean_object{
let mut v___x_611_: *mut lean_object = core::ptr::null_mut(); let mut v_putStr_612_: *mut lean_object = core::ptr::null_mut(); let mut v___x_613_: *mut lean_object = core::ptr::null_mut(); 
v___x_611_ = lean_get_stdout();
v_putStr_612_ = lean_ctor_get(v___x_611_, 4);
lean_inc_ref(v_putStr_612_);
lean_dec_ref(v___x_611_);
v___x_613_ = lean_apply_2(v_putStr_612_, v_s_609_, lean_box(0));
return v___x_613_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00check_spec__1_spec__2___boxed(mut v_s_614_: *mut lean_object, mut v_a_615_: *mut lean_object) -> *mut lean_object{
let mut v_res_616_: *mut lean_object = core::ptr::null_mut(); 
v_res_616_ = l_IO_print___at___00IO_println___at___00check_spec__1_spec__2(v_s_614_);
return v_res_616_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00check_spec__1(mut v_s_617_: *mut lean_object) -> *mut lean_object{
let mut v___x_619_: u32 = 0; let mut v___x_620_: *mut lean_object = core::ptr::null_mut(); let mut v___x_621_: *mut lean_object = core::ptr::null_mut(); 
v___x_619_ = 10;
v___x_620_ = lean_string_push(v_s_617_, v___x_619_);
v___x_621_ = l_IO_print___at___00IO_println___at___00check_spec__1_spec__2(v___x_620_);
return v___x_621_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00check_spec__1___boxed(mut v_s_622_: *mut lean_object, mut v_a_623_: *mut lean_object) -> *mut lean_object{
let mut v_res_624_: *mut lean_object = core::ptr::null_mut(); 
v_res_624_ = l_IO_println___at___00check_spec__1(v_s_622_);
return v_res_624_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00check_spec__2___redArg(mut v_m_627_: *mut lean_object, mut v_n_628_: *mut lean_object, mut v_i_629_: *mut lean_object) -> *mut lean_object{
let mut v_zero_631_: *mut lean_object = core::ptr::null_mut(); let mut v_isZero_632_: u8 = 0; let mut v___x_633_: *mut lean_object = core::ptr::null_mut(); let mut v___x_634_: *mut lean_object = core::ptr::null_mut(); let mut v_one_635_: *mut lean_object = core::ptr::null_mut(); let mut v_n_636_: *mut lean_object = core::ptr::null_mut(); let mut v___y_638_: *mut lean_object = core::ptr::null_mut(); let mut v___x_640_: *mut lean_object = core::ptr::null_mut(); let mut v___x_641_: *mut lean_object = core::ptr::null_mut(); let mut v___x_642_: *mut lean_object = core::ptr::null_mut(); let mut v___x_643_: *mut lean_object = core::ptr::null_mut(); let mut v___x_644_: *mut lean_object = core::ptr::null_mut(); let mut v___x_645_: *mut lean_object = core::ptr::null_mut(); let mut v___x_646_: *mut lean_object = core::ptr::null_mut(); let mut v_val_647_: *mut lean_object = core::ptr::null_mut(); let mut v___x_648_: *mut lean_object = core::ptr::null_mut(); let mut v___x_649_: *mut lean_object = core::ptr::null_mut(); let mut v___x_650_: u8 = 0; let mut v___x_651_: *mut lean_object = core::ptr::null_mut(); let mut v___x_652_: *mut lean_object = core::ptr::null_mut(); let mut v___x_653_: *mut lean_object = core::ptr::null_mut(); let mut v___x_654_: *mut lean_object = core::ptr::null_mut(); let mut v___x_655_: *mut lean_object = core::ptr::null_mut(); let mut v___x_656_: *mut lean_object = core::ptr::null_mut(); let mut v___x_657_: *mut lean_object = core::ptr::null_mut(); let mut v___x_658_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v_zero_631_ = lean_unsigned_to_nat(0);
v_isZero_632_ = lean_nat_dec_eq(v_i_629_, v_zero_631_);
if v_isZero_632_ == 1 {
lean_dec(v_i_629_);
v___x_633_ = lean_box(0);
v___x_634_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_634_, 0, v___x_633_);
return v___x_634_;
} else {
v_one_635_ = lean_unsigned_to_nat(1);
v_n_636_ = lean_nat_sub(v_i_629_, v_one_635_);
lean_dec(v_i_629_);
v___x_640_ = lean_nat_sub(v_n_628_, v_n_636_);
v___x_641_ = lean_nat_sub(v___x_640_, v_one_635_);
lean_dec(v___x_640_);
v___x_642_ = l_Lean_PersistentHashMap_find_x3f___at___00check_spec__0___redArg(v_m_627_, v___x_641_);
if lean_obj_tag(v___x_642_) == 0 {
v___x_643_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00check_spec__2___redArg___closed__0;
v___x_644_ = l_Nat_reprFast(v___x_641_);
v___x_645_ = lean_string_append(v___x_643_, v___x_644_);
lean_dec_ref(v___x_644_);
v___x_646_ = l_IO_println___at___00check_spec__1(v___x_645_);
v___y_638_ = v___x_646_;
state = 1; continue;
} else {
v_val_647_ = lean_ctor_get(v___x_642_, 0);
lean_inc(v_val_647_);
lean_dec_ref_known(v___x_642_, 1);
v___x_648_ = lean_unsigned_to_nat(10);
v___x_649_ = lean_nat_mul(v___x_641_, v___x_648_);
v___x_650_ = lean_nat_dec_eq(v_val_647_, v___x_649_);
lean_dec(v___x_649_);
if v___x_650_ == 0 {
v___x_651_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00check_spec__2___redArg___closed__1;
v___x_652_ = l_Nat_reprFast(v___x_641_);
v___x_653_ = lean_string_append(v___x_651_, v___x_652_);
lean_dec_ref(v___x_652_);
v___x_654_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__2;
v___x_655_ = lean_string_append(v___x_653_, v___x_654_);
v___x_656_ = l_Nat_reprFast(v_val_647_);
v___x_657_ = lean_string_append(v___x_655_, v___x_656_);
lean_dec_ref(v___x_656_);
v___x_658_ = l_IO_println___at___00check_spec__1(v___x_657_);
v___y_638_ = v___x_658_;
state = 1; continue;
} else {
lean_dec(v_val_647_);
lean_dec(v___x_641_);
v_i_629_ = v_n_636_;
state = 0; continue;
}
}
}
}
1 => {
if lean_obj_tag(v___y_638_) == 0 {
lean_dec_ref_known(v___y_638_, 1);
v_i_629_ = v_n_636_;
state = 0; continue;
} else {
lean_dec(v_n_636_);
return v___y_638_;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00check_spec__2___redArg___boxed(mut v_m_660_: *mut lean_object, mut v_n_661_: *mut lean_object, mut v_i_662_: *mut lean_object, mut v___y_663_: *mut lean_object) -> *mut lean_object{
let mut v_res_664_: *mut lean_object = core::ptr::null_mut(); 
v_res_664_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00check_spec__2___redArg(v_m_660_, v_n_661_, v_i_662_);
lean_dec(v_n_661_);
lean_dec_ref(v_m_660_);
return v_res_664_;
}
#[no_mangle] pub unsafe extern "C" fn l_check(mut v_n_665_: *mut lean_object, mut v_m_666_: *mut lean_object) -> *mut lean_object{
let mut v___x_668_: *mut lean_object = core::ptr::null_mut(); 
lean_inc(v_n_665_);
v___x_668_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00check_spec__2___redArg(v_m_666_, v_n_665_, v_n_665_);
lean_dec(v_n_665_);
return v___x_668_;
}
#[no_mangle] pub unsafe extern "C" fn l_check___boxed(mut v_n_669_: *mut lean_object, mut v_m_670_: *mut lean_object, mut v_a_671_: *mut lean_object) -> *mut lean_object{
let mut v_res_672_: *mut lean_object = core::ptr::null_mut(); 
v_res_672_ = l_check(v_n_669_, v_m_670_);
lean_dec_ref(v_m_670_);
return v_res_672_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_find_x3f___at___00check_spec__0(mut v_00_u03b2_673_: *mut lean_object, mut v_x_674_: *mut lean_object, mut v_x_675_: *mut lean_object) -> *mut lean_object{
let mut v___x_676_: *mut lean_object = core::ptr::null_mut(); 
v___x_676_ = l_Lean_PersistentHashMap_find_x3f___at___00check_spec__0___redArg(v_x_674_, v_x_675_);
return v___x_676_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_find_x3f___at___00check_spec__0___boxed(mut v_00_u03b2_677_: *mut lean_object, mut v_x_678_: *mut lean_object, mut v_x_679_: *mut lean_object) -> *mut lean_object{
let mut v_res_680_: *mut lean_object = core::ptr::null_mut(); 
v_res_680_ = l_Lean_PersistentHashMap_find_x3f___at___00check_spec__0(v_00_u03b2_677_, v_x_678_, v_x_679_);
lean_dec(v_x_679_);
lean_dec_ref(v_x_678_);
return v_res_680_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00check_spec__2(mut v_m_681_: *mut lean_object, mut v_n_682_: *mut lean_object, mut v_i_683_: *mut lean_object, mut v_a_684_: *mut lean_object) -> *mut lean_object{
let mut v___x_686_: *mut lean_object = core::ptr::null_mut(); 
v___x_686_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00check_spec__2___redArg(v_m_681_, v_n_682_, v_i_683_);
return v___x_686_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00check_spec__2___boxed(mut v_m_687_: *mut lean_object, mut v_n_688_: *mut lean_object, mut v_i_689_: *mut lean_object, mut v_a_690_: *mut lean_object, mut v___y_691_: *mut lean_object) -> *mut lean_object{
let mut v_res_692_: *mut lean_object = core::ptr::null_mut(); 
v_res_692_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00check_spec__2(v_m_687_, v_n_688_, v_i_689_, v_a_690_);
lean_dec(v_n_688_);
lean_dec_ref(v_m_687_);
return v_res_692_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00check_spec__0_spec__0(mut v_00_u03b2_693_: *mut lean_object, mut v_x_694_: *mut lean_object, mut v_x_695_: usize, mut v_x_696_: *mut lean_object) -> *mut lean_object{
let mut v___x_697_: *mut lean_object = core::ptr::null_mut(); 
v___x_697_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00check_spec__0_spec__0___redArg(v_x_694_, v_x_695_, v_x_696_);
return v___x_697_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00check_spec__0_spec__0___boxed(mut v_00_u03b2_698_: *mut lean_object, mut v_x_699_: *mut lean_object, mut v_x_700_: *mut lean_object, mut v_x_701_: *mut lean_object) -> *mut lean_object{
let mut v_x_704__boxed_702_: usize = 0; let mut v_res_703_: *mut lean_object = core::ptr::null_mut(); 
v_x_704__boxed_702_ = lean_unbox_usize(v_x_700_);
lean_dec(v_x_700_);
v_res_703_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00check_spec__0_spec__0(v_00_u03b2_698_, v_x_699_, v_x_704__boxed_702_, v_x_701_);
lean_dec(v_x_701_);
lean_dec_ref(v_x_699_);
return v_res_703_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00check_spec__0_spec__0_spec__1(mut v_00_u03b2_704_: *mut lean_object, mut v_keys_705_: *mut lean_object, mut v_vals_706_: *mut lean_object, mut v_heq_707_: *mut lean_object, mut v_i_708_: *mut lean_object, mut v_k_709_: *mut lean_object) -> *mut lean_object{
let mut v___x_710_: *mut lean_object = core::ptr::null_mut(); 
v___x_710_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00check_spec__0_spec__0_spec__1___redArg(v_keys_705_, v_vals_706_, v_i_708_, v_k_709_);
return v___x_710_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00check_spec__0_spec__0_spec__1___boxed(mut v_00_u03b2_711_: *mut lean_object, mut v_keys_712_: *mut lean_object, mut v_vals_713_: *mut lean_object, mut v_heq_714_: *mut lean_object, mut v_i_715_: *mut lean_object, mut v_k_716_: *mut lean_object) -> *mut lean_object{
let mut v_res_717_: *mut lean_object = core::ptr::null_mut(); 
v_res_717_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00check_spec__0_spec__0_spec__1(v_00_u03b2_711_, v_keys_712_, v_vals_713_, v_heq_714_, v_i_715_, v_k_716_);
lean_dec(v_k_716_);
lean_dec_ref(v_vals_713_);
lean_dec_ref(v_keys_712_);
return v_res_717_;
}
#[no_mangle] pub unsafe extern "C" fn l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00delOdd_spec__0_spec__0_spec__1_spec__3(mut v_xs_718_: *mut lean_object, mut v_v_719_: *mut lean_object, mut v_i_720_: *mut lean_object) -> *mut lean_object{
let mut v___x_721_: *mut lean_object = core::ptr::null_mut(); let mut v___x_722_: u8 = 0; let mut v___x_723_: *mut lean_object = core::ptr::null_mut(); let mut v___x_724_: *mut lean_object = core::ptr::null_mut(); let mut v___x_725_: u8 = 0; let mut v___x_726_: *mut lean_object = core::ptr::null_mut(); let mut v___x_727_: *mut lean_object = core::ptr::null_mut(); let mut v___x_729_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_721_ = lean_array_get_size(v_xs_718_);
v___x_722_ = lean_nat_dec_lt(v_i_720_, v___x_721_);
if v___x_722_ == 0 {
lean_dec(v_i_720_);
v___x_723_ = lean_box(0);
return v___x_723_;
} else {
v___x_724_ = lean_array_fget_borrowed(v_xs_718_, v_i_720_);
v___x_725_ = lean_nat_dec_eq(v___x_724_, v_v_719_);
if v___x_725_ == 0 {
v___x_726_ = lean_unsigned_to_nat(1);
v___x_727_ = lean_nat_add(v_i_720_, v___x_726_);
lean_dec(v_i_720_);
v_i_720_ = v___x_727_;
state = 0; continue;
} else {
v___x_729_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v___x_729_, 0, v_i_720_);
return v___x_729_;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00delOdd_spec__0_spec__0_spec__1_spec__3___boxed(mut v_xs_730_: *mut lean_object, mut v_v_731_: *mut lean_object, mut v_i_732_: *mut lean_object) -> *mut lean_object{
let mut v_res_733_: *mut lean_object = core::ptr::null_mut(); 
v_res_733_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00delOdd_spec__0_spec__0_spec__1_spec__3(v_xs_730_, v_v_731_, v_i_732_);
lean_dec(v_v_731_);
lean_dec_ref(v_xs_730_);
return v_res_733_;
}
#[no_mangle] pub unsafe extern "C" fn l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00delOdd_spec__0_spec__0_spec__1(mut v_xs_734_: *mut lean_object, mut v_v_735_: *mut lean_object) -> *mut lean_object{
let mut v___x_736_: *mut lean_object = core::ptr::null_mut(); let mut v___x_737_: *mut lean_object = core::ptr::null_mut(); 
v___x_736_ = lean_unsigned_to_nat(0);
v___x_737_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00delOdd_spec__0_spec__0_spec__1_spec__3(v_xs_734_, v_v_735_, v___x_736_);
return v___x_737_;
}
#[no_mangle] pub unsafe extern "C" fn l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00delOdd_spec__0_spec__0_spec__1___boxed(mut v_xs_738_: *mut lean_object, mut v_v_739_: *mut lean_object) -> *mut lean_object{
let mut v_res_740_: *mut lean_object = core::ptr::null_mut(); 
v_res_740_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00delOdd_spec__0_spec__0_spec__1(v_xs_738_, v_v_739_);
lean_dec(v_v_739_);
lean_dec_ref(v_xs_738_);
return v_res_740_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00delOdd_spec__0_spec__0___redArg(mut v_x_741_: *mut lean_object, mut v_x_742_: usize, mut v_x_743_: *mut lean_object) -> *mut lean_object{
let mut v_es_744_: *mut lean_object = core::ptr::null_mut(); let mut v___x_745_: *mut lean_object = core::ptr::null_mut(); let mut v___x_746_: usize = 0; let mut v___x_747_: usize = 0; let mut v___x_748_: usize = 0; let mut v_j_749_: *mut lean_object = core::ptr::null_mut(); let mut v_entry_750_: *mut lean_object = core::ptr::null_mut(); let mut v_key_751_: *mut lean_object = core::ptr::null_mut(); let mut v___x_752_: u8 = 0; let mut v___x_754_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_755_: u8 = 0; let mut v___x_756_: *mut lean_object = core::ptr::null_mut(); let mut v___x_758_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_759_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_760_: u8 = 0; let mut v_unused_761_: *mut lean_object = core::ptr::null_mut(); let mut v___x_763_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_764_: u8 = 0; let mut v_node_765_: *mut lean_object = core::ptr::null_mut(); let mut v___x_767_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_768_: u8 = 0; let mut v_entries_769_: *mut lean_object = core::ptr::null_mut(); let mut v___x_770_: usize = 0; let mut v_newNode_771_: *mut lean_object = core::ptr::null_mut(); let mut v___x_772_: *mut lean_object = core::ptr::null_mut(); let mut v___x_774_: *mut lean_object = core::ptr::null_mut(); let mut v___x_775_: *mut lean_object = core::ptr::null_mut(); let mut v___x_777_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_778_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_779_: *mut lean_object = core::ptr::null_mut(); let mut v_val_780_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_781_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_782_: *mut lean_object = core::ptr::null_mut(); let mut v___x_784_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_785_: u8 = 0; let mut v___x_787_: *mut lean_object = core::ptr::null_mut(); let mut v___x_788_: *mut lean_object = core::ptr::null_mut(); let mut v___x_790_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_791_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_792_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_793_: u8 = 0; let mut v_isSharedCheck_794_: u8 = 0; let mut v_isSharedCheck_795_: u8 = 0; let mut v_unused_796_: *mut lean_object = core::ptr::null_mut(); let mut v_ks_797_: *mut lean_object = core::ptr::null_mut(); let mut v_vs_798_: *mut lean_object = core::ptr::null_mut(); let mut v___x_800_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_801_: u8 = 0; let mut v___x_802_: *mut lean_object = core::ptr::null_mut(); let mut v___x_804_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_805_: *mut lean_object = core::ptr::null_mut(); let mut v_val_806_: *mut lean_object = core::ptr::null_mut(); let mut v_keys_x27_807_: *mut lean_object = core::ptr::null_mut(); let mut v_vals_x27_808_: *mut lean_object = core::ptr::null_mut(); let mut v___x_810_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_811_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_812_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_x_741_) == 0 {
v_es_744_ = lean_ctor_get(v_x_741_, 0);
v___x_745_ = lean_box(2);
v___x_746_ = 5usize;
v___x_747_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMap_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMap_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMap_spec__0_spec__0___redArg___closed__1);
v___x_748_ = lean_usize_land(v_x_742_, v___x_747_);
v_j_749_ = lean_usize_to_nat(v___x_748_);
v_entry_750_ = lean_array_get(v___x_745_, v_es_744_, v_j_749_);
match lean_obj_tag(v_entry_750_)
{
0 => {
v_key_751_ = lean_ctor_get(v_entry_750_, 0);
lean_inc(v_key_751_);
lean_dec_ref_known(v_entry_750_, 2);
v___x_752_ = lean_nat_dec_eq(v_x_743_, v_key_751_);
lean_dec(v_key_751_);
if v___x_752_ == 0 {
lean_dec(v_j_749_);
return v_x_741_;
} else {
lean_inc_ref(v_es_744_);
v_isSharedCheck_760_ = (!lean_is_exclusive(v_x_741_)) as u8;
if v_isSharedCheck_760_ == 0 {
v_unused_761_ = lean_ctor_get(v_x_741_, 0);
lean_dec(v_unused_761_);
v___x_754_ = v_x_741_;
v_isShared_755_ = v_isSharedCheck_760_;
state = 1; continue;
} else {
lean_dec(v_x_741_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_760_;
state = 1; continue;
}
}
}
1 => {
lean_inc_ref(v_es_744_);
v_isSharedCheck_795_ = (!lean_is_exclusive(v_x_741_)) as u8;
if v_isSharedCheck_795_ == 0 {
v_unused_796_ = lean_ctor_get(v_x_741_, 0);
lean_dec(v_unused_796_);
v___x_763_ = v_x_741_;
v_isShared_764_ = v_isSharedCheck_795_;
state = 3; continue;
} else {
lean_dec(v_x_741_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_795_;
state = 3; continue;
}
}
_ => {
lean_dec(v_j_749_);
return v_x_741_;
}
}
} else {
v_ks_797_ = lean_ctor_get(v_x_741_, 0);
v_vs_798_ = lean_ctor_get(v_x_741_, 1);
v_isSharedCheck_812_ = (!lean_is_exclusive(v_x_741_)) as u8;
if v_isSharedCheck_812_ == 0 {
v___x_800_ = v_x_741_;
v_isShared_801_ = v_isSharedCheck_812_;
state = 10; continue;
} else {
lean_inc(v_vs_798_);
lean_inc(v_ks_797_);
lean_dec(v_x_741_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_812_;
state = 10; continue;
}
}
}
1 => {
v___x_756_ = lean_array_set(v_es_744_, v_j_749_, v___x_745_);
lean_dec(v_j_749_);
if v_isShared_755_ == 0 {
lean_ctor_set(v___x_754_, 0, v___x_756_);
v___x_758_ = v___x_754_;
state = 2; continue;
} else {
v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v___x_756_);
v___x_758_ = v_reuseFailAlloc_759_;
state = 2; continue;
}
}
2 => {
return v___x_758_;
}
3 => {
v_node_765_ = lean_ctor_get(v_entry_750_, 0);
v_isSharedCheck_794_ = (!lean_is_exclusive(v_entry_750_)) as u8;
if v_isSharedCheck_794_ == 0 {
v___x_767_ = v_entry_750_;
v_isShared_768_ = v_isSharedCheck_794_;
state = 4; continue;
} else {
lean_inc(v_node_765_);
lean_dec(v_entry_750_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_794_;
state = 4; continue;
}
}
4 => {
v_entries_769_ = lean_array_set(v_es_744_, v_j_749_, v___x_745_);
v___x_770_ = lean_usize_shift_right(v_x_742_, v___x_746_);
v_newNode_771_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00delOdd_spec__0_spec__0___redArg(v_node_765_, v___x_770_, v_x_743_);
lean_inc_ref(v_newNode_771_);
v___x_772_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_771_);
if lean_obj_tag(v___x_772_) == 0 {
if v_isShared_768_ == 0 {
lean_ctor_set(v___x_767_, 0, v_newNode_771_);
v___x_774_ = v___x_767_;
state = 5; continue;
} else {
v_reuseFailAlloc_779_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_newNode_771_);
v___x_774_ = v_reuseFailAlloc_779_;
state = 5; continue;
}
} else {
lean_dec_ref(v_newNode_771_);
lean_del_object(v___x_767_);
v_val_780_ = lean_ctor_get(v___x_772_, 0);
lean_inc(v_val_780_);
lean_dec_ref_known(v___x_772_, 1);
v_fst_781_ = lean_ctor_get(v_val_780_, 0);
v_snd_782_ = lean_ctor_get(v_val_780_, 1);
v_isSharedCheck_793_ = (!lean_is_exclusive(v_val_780_)) as u8;
if v_isSharedCheck_793_ == 0 {
v___x_784_ = v_val_780_;
v_isShared_785_ = v_isSharedCheck_793_;
state = 7; continue;
} else {
lean_inc(v_snd_782_);
lean_inc(v_fst_781_);
lean_dec(v_val_780_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_793_;
state = 7; continue;
}
}
}
5 => {
v___x_775_ = lean_array_set(v_entries_769_, v_j_749_, v___x_774_);
lean_dec(v_j_749_);
if v_isShared_764_ == 0 {
lean_ctor_set(v___x_763_, 0, v___x_775_);
v___x_777_ = v___x_763_;
state = 6; continue;
} else {
v_reuseFailAlloc_778_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v___x_775_);
v___x_777_ = v_reuseFailAlloc_778_;
state = 6; continue;
}
}
6 => {
return v___x_777_;
}
7 => {
if v_isShared_785_ == 0 {
v___x_787_ = v___x_784_;
state = 8; continue;
} else {
v_reuseFailAlloc_792_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_fst_781_);
lean_ctor_set(v_reuseFailAlloc_792_, 1, v_snd_782_);
v___x_787_ = v_reuseFailAlloc_792_;
state = 8; continue;
}
}
8 => {
v___x_788_ = lean_array_set(v_entries_769_, v_j_749_, v___x_787_);
lean_dec(v_j_749_);
if v_isShared_764_ == 0 {
lean_ctor_set(v___x_763_, 0, v___x_788_);
v___x_790_ = v___x_763_;
state = 9; continue;
} else {
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v___x_788_);
v___x_790_ = v_reuseFailAlloc_791_;
state = 9; continue;
}
}
9 => {
return v___x_790_;
}
10 => {
v___x_802_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00delOdd_spec__0_spec__0_spec__1(v_ks_797_, v_x_743_);
if lean_obj_tag(v___x_802_) == 0 {
if v_isShared_801_ == 0 {
v___x_804_ = v___x_800_;
state = 11; continue;
} else {
v_reuseFailAlloc_805_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_ks_797_);
lean_ctor_set(v_reuseFailAlloc_805_, 1, v_vs_798_);
v___x_804_ = v_reuseFailAlloc_805_;
state = 11; continue;
}
} else {
v_val_806_ = lean_ctor_get(v___x_802_, 0);
lean_inc_n(v_val_806_, 2);
lean_dec_ref_known(v___x_802_, 1);
v_keys_x27_807_ = l_Array_eraseIdx___redArg(v_ks_797_, v_val_806_);
v_vals_x27_808_ = l_Array_eraseIdx___redArg(v_vs_798_, v_val_806_);
if v_isShared_801_ == 0 {
lean_ctor_set(v___x_800_, 1, v_vals_x27_808_);
lean_ctor_set(v___x_800_, 0, v_keys_x27_807_);
v___x_810_ = v___x_800_;
state = 12; continue;
} else {
v_reuseFailAlloc_811_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_keys_x27_807_);
lean_ctor_set(v_reuseFailAlloc_811_, 1, v_vals_x27_808_);
v___x_810_ = v_reuseFailAlloc_811_;
state = 12; continue;
}
}
}
11 => {
return v___x_804_;
}
12 => {
return v___x_810_;
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00delOdd_spec__0_spec__0___redArg___boxed(mut v_x_813_: *mut lean_object, mut v_x_814_: *mut lean_object, mut v_x_815_: *mut lean_object) -> *mut lean_object{
let mut v_x_284__boxed_816_: usize = 0; let mut v_res_817_: *mut lean_object = core::ptr::null_mut(); 
v_x_284__boxed_816_ = lean_unbox_usize(v_x_814_);
lean_dec(v_x_814_);
v_res_817_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00delOdd_spec__0_spec__0___redArg(v_x_813_, v_x_284__boxed_816_, v_x_815_);
lean_dec(v_x_815_);
return v_res_817_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_erase___at___00delOdd_spec__0___redArg(mut v_x_818_: *mut lean_object, mut v_x_819_: *mut lean_object) -> *mut lean_object{
let mut v___x_820_: u64 = 0; let mut v_h_821_: usize = 0; let mut v___x_822_: *mut lean_object = core::ptr::null_mut(); 
v___x_820_ = lean_uint64_of_nat(v_x_819_);
v_h_821_ = lean_uint64_to_usize(v___x_820_);
v___x_822_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00delOdd_spec__0_spec__0___redArg(v_x_818_, v_h_821_, v_x_819_);
return v___x_822_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_erase___at___00delOdd_spec__0___redArg___boxed(mut v_x_823_: *mut lean_object, mut v_x_824_: *mut lean_object) -> *mut lean_object{
let mut v_res_825_: *mut lean_object = core::ptr::null_mut(); 
v_res_825_ = l_Lean_PersistentHashMap_erase___at___00delOdd_spec__0___redArg(v_x_823_, v_x_824_);
lean_dec(v_x_824_);
return v_res_825_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00delOdd_spec__1___redArg(mut v_n_826_: *mut lean_object, mut v_j_827_: *mut lean_object, mut v_a_828_: *mut lean_object) -> *mut lean_object{
let mut v_zero_829_: *mut lean_object = core::ptr::null_mut(); let mut v_isZero_830_: u8 = 0; let mut v_one_831_: *mut lean_object = core::ptr::null_mut(); let mut v_n_832_: *mut lean_object = core::ptr::null_mut(); let mut v___x_833_: *mut lean_object = core::ptr::null_mut(); let mut v___x_834_: *mut lean_object = core::ptr::null_mut(); let mut v___x_835_: *mut lean_object = core::ptr::null_mut(); let mut v___x_836_: u8 = 0; let mut v___x_837_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v_zero_829_ = lean_unsigned_to_nat(0);
v_isZero_830_ = lean_nat_dec_eq(v_j_827_, v_zero_829_);
if v_isZero_830_ == 1 {
lean_dec(v_j_827_);
return v_a_828_;
} else {
v_one_831_ = lean_unsigned_to_nat(1);
v_n_832_ = lean_nat_sub(v_j_827_, v_one_831_);
v___x_833_ = lean_nat_sub(v_n_826_, v_j_827_);
lean_dec(v_j_827_);
v___x_834_ = lean_unsigned_to_nat(2);
v___x_835_ = lean_nat_mod(v___x_833_, v___x_834_);
v___x_836_ = lean_nat_dec_eq(v___x_835_, v_zero_829_);
lean_dec(v___x_835_);
if v___x_836_ == 0 {
v___x_837_ = l_Lean_PersistentHashMap_erase___at___00delOdd_spec__0___redArg(v_a_828_, v___x_833_);
lean_dec(v___x_833_);
v_j_827_ = v_n_832_;
v_a_828_ = v___x_837_;
state = 0; continue;
} else {
lean_dec(v___x_833_);
v_j_827_ = v_n_832_;
state = 0; continue;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00delOdd_spec__1___redArg___boxed(mut v_n_840_: *mut lean_object, mut v_j_841_: *mut lean_object, mut v_a_842_: *mut lean_object) -> *mut lean_object{
let mut v_res_843_: *mut lean_object = core::ptr::null_mut(); 
v_res_843_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00delOdd_spec__1___redArg(v_n_840_, v_j_841_, v_a_842_);
lean_dec(v_n_840_);
return v_res_843_;
}
#[no_mangle] pub unsafe extern "C" fn l_delOdd(mut v_n_844_: *mut lean_object, mut v_m_845_: *mut lean_object) -> *mut lean_object{
let mut v___x_846_: *mut lean_object = core::ptr::null_mut(); 
lean_inc(v_n_844_);
v___x_846_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00delOdd_spec__1___redArg(v_n_844_, v_n_844_, v_m_845_);
lean_dec(v_n_844_);
return v___x_846_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_erase___at___00delOdd_spec__0(mut v_00_u03b2_847_: *mut lean_object, mut v_x_848_: *mut lean_object, mut v_x_849_: *mut lean_object) -> *mut lean_object{
let mut v___x_850_: *mut lean_object = core::ptr::null_mut(); 
v___x_850_ = l_Lean_PersistentHashMap_erase___at___00delOdd_spec__0___redArg(v_x_848_, v_x_849_);
return v___x_850_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_erase___at___00delOdd_spec__0___boxed(mut v_00_u03b2_851_: *mut lean_object, mut v_x_852_: *mut lean_object, mut v_x_853_: *mut lean_object) -> *mut lean_object{
let mut v_res_854_: *mut lean_object = core::ptr::null_mut(); 
v_res_854_ = l_Lean_PersistentHashMap_erase___at___00delOdd_spec__0(v_00_u03b2_851_, v_x_852_, v_x_853_);
lean_dec(v_x_853_);
return v_res_854_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00delOdd_spec__1(mut v_n_855_: *mut lean_object, mut v_j_856_: *mut lean_object, mut v_a_857_: *mut lean_object, mut v_a_858_: *mut lean_object) -> *mut lean_object{
let mut v___x_859_: *mut lean_object = core::ptr::null_mut(); 
v___x_859_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00delOdd_spec__1___redArg(v_n_855_, v_j_856_, v_a_858_);
return v___x_859_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00delOdd_spec__1___boxed(mut v_n_860_: *mut lean_object, mut v_j_861_: *mut lean_object, mut v_a_862_: *mut lean_object, mut v_a_863_: *mut lean_object) -> *mut lean_object{
let mut v_res_864_: *mut lean_object = core::ptr::null_mut(); 
v_res_864_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00delOdd_spec__1(v_n_860_, v_j_861_, v_a_862_, v_a_863_);
lean_dec(v_n_860_);
return v_res_864_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00delOdd_spec__0_spec__0(mut v_00_u03b2_865_: *mut lean_object, mut v_x_866_: *mut lean_object, mut v_x_867_: usize, mut v_x_868_: *mut lean_object) -> *mut lean_object{
let mut v___x_869_: *mut lean_object = core::ptr::null_mut(); 
v___x_869_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00delOdd_spec__0_spec__0___redArg(v_x_866_, v_x_867_, v_x_868_);
return v___x_869_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00delOdd_spec__0_spec__0___boxed(mut v_00_u03b2_870_: *mut lean_object, mut v_x_871_: *mut lean_object, mut v_x_872_: *mut lean_object, mut v_x_873_: *mut lean_object) -> *mut lean_object{
let mut v_x_469__boxed_874_: usize = 0; let mut v_res_875_: *mut lean_object = core::ptr::null_mut(); 
v_x_469__boxed_874_ = lean_unbox_usize(v_x_872_);
lean_dec(v_x_872_);
v_res_875_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00delOdd_spec__0_spec__0(v_00_u03b2_870_, v_x_871_, v_x_469__boxed_874_, v_x_873_);
lean_dec(v_x_873_);
return v_res_875_;
}
#[no_mangle] pub unsafe extern "C" fn l_Option_instBEq_beq___at___00check2_spec__0(mut v_x_876_: *mut lean_object, mut v_x_877_: *mut lean_object) -> u8{
if lean_obj_tag(v_x_876_) == 0 {
if lean_obj_tag(v_x_877_) == 0 {
let mut v___x_878_: u8 = 0; 
v___x_878_ = 1;
return v___x_878_;
} else {
let mut v___x_879_: u8 = 0; 
v___x_879_ = 0;
return v___x_879_;
}
} else {
if lean_obj_tag(v_x_877_) == 0 {
let mut v___x_880_: u8 = 0; 
v___x_880_ = 0;
return v___x_880_;
} else {
let mut v_val_881_: *mut lean_object = core::ptr::null_mut(); let mut v_val_882_: *mut lean_object = core::ptr::null_mut(); let mut v___x_883_: u8 = 0; 
v_val_881_ = lean_ctor_get(v_x_876_, 0);
v_val_882_ = lean_ctor_get(v_x_877_, 0);
v___x_883_ = lean_nat_dec_eq(v_val_881_, v_val_882_);
return v___x_883_;
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Option_instBEq_beq___at___00check2_spec__0___boxed(mut v_x_884_: *mut lean_object, mut v_x_885_: *mut lean_object) -> *mut lean_object{
let mut v_res_886_: u8 = 0; let mut v_r_887_: *mut lean_object = core::ptr::null_mut(); 
v_res_886_ = l_Option_instBEq_beq___at___00check2_spec__0(v_x_884_, v_x_885_);
lean_dec(v_x_885_);
lean_dec(v_x_884_);
v_r_887_ = lean_box((v_res_886_) as usize);
return v_r_887_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00check2_spec__1___redArg(mut v_bot_889_: *mut lean_object, mut v_m_890_: *mut lean_object, mut v_n_891_: *mut lean_object, mut v_i_892_: *mut lean_object) -> *mut lean_object{
let mut v_zero_894_: *mut lean_object = core::ptr::null_mut(); let mut v_isZero_895_: u8 = 0; let mut v___x_896_: *mut lean_object = core::ptr::null_mut(); let mut v___x_897_: *mut lean_object = core::ptr::null_mut(); let mut v_one_898_: *mut lean_object = core::ptr::null_mut(); let mut v_n_899_: *mut lean_object = core::ptr::null_mut(); let mut v___y_901_: *mut lean_object = core::ptr::null_mut(); let mut v___x_903_: *mut lean_object = core::ptr::null_mut(); let mut v___x_904_: *mut lean_object = core::ptr::null_mut(); let mut v___y_906_: u8 = 0; let mut v___x_907_: *mut lean_object = core::ptr::null_mut(); let mut v___x_908_: *mut lean_object = core::ptr::null_mut(); let mut v___x_909_: u8 = 0; let mut v___x_910_: *mut lean_object = core::ptr::null_mut(); let mut v___x_911_: *mut lean_object = core::ptr::null_mut(); let mut v___x_912_: *mut lean_object = core::ptr::null_mut(); let mut v___x_913_: *mut lean_object = core::ptr::null_mut(); let mut v___x_915_: *mut lean_object = core::ptr::null_mut(); let mut v___x_916_: *mut lean_object = core::ptr::null_mut(); let mut v___x_917_: *mut lean_object = core::ptr::null_mut(); let mut v___x_918_: *mut lean_object = core::ptr::null_mut(); let mut v___x_919_: *mut lean_object = core::ptr::null_mut(); let mut v_val_920_: *mut lean_object = core::ptr::null_mut(); let mut v___x_921_: *mut lean_object = core::ptr::null_mut(); let mut v___x_922_: *mut lean_object = core::ptr::null_mut(); let mut v___x_923_: u8 = 0; let mut v___x_924_: *mut lean_object = core::ptr::null_mut(); let mut v___x_925_: *mut lean_object = core::ptr::null_mut(); let mut v___x_926_: *mut lean_object = core::ptr::null_mut(); let mut v___x_927_: *mut lean_object = core::ptr::null_mut(); let mut v___x_928_: *mut lean_object = core::ptr::null_mut(); let mut v___x_929_: *mut lean_object = core::ptr::null_mut(); let mut v___x_930_: *mut lean_object = core::ptr::null_mut(); let mut v___x_931_: *mut lean_object = core::ptr::null_mut(); let mut v___x_933_: *mut lean_object = core::ptr::null_mut(); let mut v___x_934_: *mut lean_object = core::ptr::null_mut(); let mut v___x_935_: u8 = 0; let mut v___x_936_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v_zero_894_ = lean_unsigned_to_nat(0);
v_isZero_895_ = lean_nat_dec_eq(v_i_892_, v_zero_894_);
if v_isZero_895_ == 1 {
lean_dec(v_i_892_);
v___x_896_ = lean_box(0);
v___x_897_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_897_, 0, v___x_896_);
return v___x_897_;
} else {
v_one_898_ = lean_unsigned_to_nat(1);
v_n_899_ = lean_nat_sub(v_i_892_, v_one_898_);
lean_dec(v_i_892_);
v___x_903_ = lean_nat_sub(v_n_891_, v_n_899_);
v___x_904_ = lean_nat_sub(v___x_903_, v_one_898_);
lean_dec(v___x_903_);
v___x_933_ = lean_unsigned_to_nat(2);
v___x_934_ = lean_nat_mod(v___x_904_, v___x_933_);
v___x_935_ = lean_nat_dec_eq(v___x_934_, v_zero_894_);
lean_dec(v___x_934_);
if v___x_935_ == 0 {
v___y_906_ = v___x_935_;
state = 2; continue;
} else {
v___x_936_ = lean_nat_dec_le(v_bot_889_, v___x_904_);
v___y_906_ = v___x_936_;
state = 2; continue;
}
}
}
1 => {
if lean_obj_tag(v___y_901_) == 0 {
lean_dec_ref_known(v___y_901_, 1);
v_i_892_ = v_n_899_;
state = 0; continue;
} else {
lean_dec(v_n_899_);
return v___y_901_;
}
}
2 => {
if v___y_906_ == 0 {
v___x_907_ = l_Lean_PersistentHashMap_find_x3f___at___00check_spec__0___redArg(v_m_890_, v___x_904_);
v___x_908_ = lean_box(0);
v___x_909_ = l_Option_instBEq_beq___at___00check2_spec__0(v___x_907_, v___x_908_);
lean_dec(v___x_907_);
if v___x_909_ == 0 {
v___x_910_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00check2_spec__1___redArg___closed__0;
v___x_911_ = l_Nat_reprFast(v___x_904_);
v___x_912_ = lean_string_append(v___x_910_, v___x_911_);
lean_dec_ref(v___x_911_);
v___x_913_ = l_IO_println___at___00check_spec__1(v___x_912_);
v___y_901_ = v___x_913_;
state = 1; continue;
} else {
lean_dec(v___x_904_);
v_i_892_ = v_n_899_;
state = 0; continue;
}
} else {
v___x_915_ = l_Lean_PersistentHashMap_find_x3f___at___00check_spec__0___redArg(v_m_890_, v___x_904_);
if lean_obj_tag(v___x_915_) == 0 {
v___x_916_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00check_spec__2___redArg___closed__0;
v___x_917_ = l_Nat_reprFast(v___x_904_);
v___x_918_ = lean_string_append(v___x_916_, v___x_917_);
lean_dec_ref(v___x_917_);
v___x_919_ = l_IO_println___at___00check_spec__1(v___x_918_);
v___y_901_ = v___x_919_;
state = 1; continue;
} else {
v_val_920_ = lean_ctor_get(v___x_915_, 0);
lean_inc(v_val_920_);
lean_dec_ref_known(v___x_915_, 1);
v___x_921_ = lean_unsigned_to_nat(10);
v___x_922_ = lean_nat_mul(v___x_904_, v___x_921_);
v___x_923_ = lean_nat_dec_eq(v_val_920_, v___x_922_);
lean_dec(v___x_922_);
if v___x_923_ == 0 {
v___x_924_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00check_spec__2___redArg___closed__1;
v___x_925_ = l_Nat_reprFast(v___x_904_);
v___x_926_ = lean_string_append(v___x_924_, v___x_925_);
lean_dec_ref(v___x_925_);
v___x_927_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00formatMap_spec__1_spec__2___redArg___closed__2;
v___x_928_ = lean_string_append(v___x_926_, v___x_927_);
v___x_929_ = l_Nat_reprFast(v_val_920_);
v___x_930_ = lean_string_append(v___x_928_, v___x_929_);
lean_dec_ref(v___x_929_);
v___x_931_ = l_IO_println___at___00check_spec__1(v___x_930_);
v___y_901_ = v___x_931_;
state = 1; continue;
} else {
lean_dec(v_val_920_);
lean_dec(v___x_904_);
v_i_892_ = v_n_899_;
state = 0; continue;
}
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00check2_spec__1___redArg___boxed(mut v_bot_937_: *mut lean_object, mut v_m_938_: *mut lean_object, mut v_n_939_: *mut lean_object, mut v_i_940_: *mut lean_object, mut v___y_941_: *mut lean_object) -> *mut lean_object{
let mut v_res_942_: *mut lean_object = core::ptr::null_mut(); 
v_res_942_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00check2_spec__1___redArg(v_bot_937_, v_m_938_, v_n_939_, v_i_940_);
lean_dec(v_n_939_);
lean_dec_ref(v_m_938_);
lean_dec(v_bot_937_);
return v_res_942_;
}
#[no_mangle] pub unsafe extern "C" fn l_check2(mut v_n_943_: *mut lean_object, mut v_bot_944_: *mut lean_object, mut v_m_945_: *mut lean_object) -> *mut lean_object{
let mut v___x_947_: *mut lean_object = core::ptr::null_mut(); 
lean_inc(v_n_943_);
v___x_947_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00check2_spec__1___redArg(v_bot_944_, v_m_945_, v_n_943_, v_n_943_);
lean_dec(v_n_943_);
return v___x_947_;
}
#[no_mangle] pub unsafe extern "C" fn l_check2___boxed(mut v_n_948_: *mut lean_object, mut v_bot_949_: *mut lean_object, mut v_m_950_: *mut lean_object, mut v_a_951_: *mut lean_object) -> *mut lean_object{
let mut v_res_952_: *mut lean_object = core::ptr::null_mut(); 
v_res_952_ = l_check2(v_n_948_, v_bot_949_, v_m_950_);
lean_dec_ref(v_m_950_);
lean_dec(v_bot_949_);
return v_res_952_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00check2_spec__1(mut v_bot_953_: *mut lean_object, mut v_m_954_: *mut lean_object, mut v_n_955_: *mut lean_object, mut v_i_956_: *mut lean_object, mut v_a_957_: *mut lean_object) -> *mut lean_object{
let mut v___x_959_: *mut lean_object = core::ptr::null_mut(); 
v___x_959_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00check2_spec__1___redArg(v_bot_953_, v_m_954_, v_n_955_, v_i_956_);
return v___x_959_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00check2_spec__1___boxed(mut v_bot_960_: *mut lean_object, mut v_m_961_: *mut lean_object, mut v_n_962_: *mut lean_object, mut v_i_963_: *mut lean_object, mut v_a_964_: *mut lean_object, mut v___y_965_: *mut lean_object) -> *mut lean_object{
let mut v_res_966_: *mut lean_object = core::ptr::null_mut(); 
v_res_966_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00check2_spec__1(v_bot_960_, v_m_961_, v_n_962_, v_i_963_, v_a_964_);
lean_dec(v_n_962_);
lean_dec_ref(v_m_961_);
lean_dec(v_bot_960_);
return v_res_966_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00delLess_spec__0___redArg(mut v_n_967_: *mut lean_object, mut v_j_968_: *mut lean_object, mut v_a_969_: *mut lean_object) -> *mut lean_object{
let mut v_zero_970_: *mut lean_object = core::ptr::null_mut(); let mut v_isZero_971_: u8 = 0; let mut v_one_972_: *mut lean_object = core::ptr::null_mut(); let mut v_n_973_: *mut lean_object = core::ptr::null_mut(); let mut v___x_974_: *mut lean_object = core::ptr::null_mut(); let mut v___x_975_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v_zero_970_ = lean_unsigned_to_nat(0);
v_isZero_971_ = lean_nat_dec_eq(v_j_968_, v_zero_970_);
if v_isZero_971_ == 1 {
lean_dec(v_j_968_);
return v_a_969_;
} else {
v_one_972_ = lean_unsigned_to_nat(1);
v_n_973_ = lean_nat_sub(v_j_968_, v_one_972_);
v___x_974_ = lean_nat_sub(v_n_967_, v_j_968_);
lean_dec(v_j_968_);
v___x_975_ = l_Lean_PersistentHashMap_erase___at___00delOdd_spec__0___redArg(v_a_969_, v___x_974_);
lean_dec(v___x_974_);
v_j_968_ = v_n_973_;
v_a_969_ = v___x_975_;
state = 0; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00delLess_spec__0___redArg___boxed(mut v_n_977_: *mut lean_object, mut v_j_978_: *mut lean_object, mut v_a_979_: *mut lean_object) -> *mut lean_object{
let mut v_res_980_: *mut lean_object = core::ptr::null_mut(); 
v_res_980_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00delLess_spec__0___redArg(v_n_977_, v_j_978_, v_a_979_);
lean_dec(v_n_977_);
return v_res_980_;
}
#[no_mangle] pub unsafe extern "C" fn l_delLess(mut v_n_981_: *mut lean_object, mut v_m_982_: *mut lean_object) -> *mut lean_object{
let mut v___x_983_: *mut lean_object = core::ptr::null_mut(); 
lean_inc(v_n_981_);
v___x_983_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00delLess_spec__0___redArg(v_n_981_, v_n_981_, v_m_982_);
lean_dec(v_n_981_);
return v___x_983_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00delLess_spec__0(mut v_n_984_: *mut lean_object, mut v_j_985_: *mut lean_object, mut v_a_986_: *mut lean_object, mut v_a_987_: *mut lean_object) -> *mut lean_object{
let mut v___x_988_: *mut lean_object = core::ptr::null_mut(); 
v___x_988_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00delLess_spec__0___redArg(v_n_984_, v_j_985_, v_a_987_);
return v___x_988_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00delLess_spec__0___boxed(mut v_n_989_: *mut lean_object, mut v_j_990_: *mut lean_object, mut v_a_991_: *mut lean_object, mut v_a_992_: *mut lean_object) -> *mut lean_object{
let mut v_res_993_: *mut lean_object = core::ptr::null_mut(); 
v_res_993_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00delLess_spec__0(v_n_989_, v_j_990_, v_a_991_, v_a_992_);
lean_dec(v_n_989_);
return v_res_993_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_stats___at___00main_spec__0___redArg(mut v_m_996_: *mut lean_object) -> *mut lean_object{
let mut v___x_997_: *mut lean_object = core::ptr::null_mut(); let mut v___x_998_: *mut lean_object = core::ptr::null_mut(); let mut v___x_999_: *mut lean_object = core::ptr::null_mut(); 
v___x_997_ = l_Lean_PersistentHashMap_stats___at___00main_spec__0___redArg___closed__0;
v___x_998_ = lean_unsigned_to_nat(1);
v___x_999_ = l_Lean_PersistentHashMap_collectStats___redArg(v_m_996_, v___x_997_, v___x_998_);
return v___x_999_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_stats___at___00main_spec__0___redArg___boxed(mut v_m_1000_: *mut lean_object) -> *mut lean_object{
let mut v_res_1001_: *mut lean_object = core::ptr::null_mut(); 
v_res_1001_ = l_Lean_PersistentHashMap_stats___at___00main_spec__0___redArg(v_m_1000_);
lean_dec_ref(v_m_1000_);
return v_res_1001_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_stats___at___00main_spec__0(mut v_00_u03b2_1002_: *mut lean_object, mut v_m_1003_: *mut lean_object) -> *mut lean_object{
let mut v___x_1004_: *mut lean_object = core::ptr::null_mut(); 
v___x_1004_ = l_Lean_PersistentHashMap_stats___at___00main_spec__0___redArg(v_m_1003_);
return v___x_1004_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_stats___at___00main_spec__0___boxed(mut v_00_u03b2_1005_: *mut lean_object, mut v_m_1006_: *mut lean_object) -> *mut lean_object{
let mut v_res_1007_: *mut lean_object = core::ptr::null_mut(); 
v_res_1007_ = l_Lean_PersistentHashMap_stats___at___00main_spec__0(v_00_u03b2_1005_, v_m_1006_);
lean_dec_ref(v_m_1006_);
return v_res_1007_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__1(mut v_s_1008_: *mut lean_object) -> *mut lean_object{
let mut v___x_1010_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1011_: u32 = 0; let mut v___x_1012_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1013_: *mut lean_object = core::ptr::null_mut(); 
v___x_1010_ = l_Lean_PersistentHashMap_Stats_toString(v_s_1008_);
v___x_1011_ = 10;
v___x_1012_ = lean_string_push(v___x_1010_, v___x_1011_);
v___x_1013_ = l_IO_print___at___00IO_println___at___00check_spec__1_spec__2(v___x_1012_);
return v___x_1013_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__1___boxed(mut v_s_1014_: *mut lean_object, mut v_a_1015_: *mut lean_object) -> *mut lean_object{
let mut v_res_1016_: *mut lean_object = core::ptr::null_mut(); 
v_res_1016_ = l_IO_println___at___00main_spec__1(v_s_1014_);
return v_res_1016_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___redArg___closed__0() -> *mut lean_object{
let mut v_n_1017_: *mut lean_object = core::ptr::null_mut(); let mut v_m_1018_: *mut lean_object = core::ptr::null_mut(); 
v_n_1017_ = lean_unsigned_to_nat(5000);
v_m_1018_ = l_mkMap(v_n_1017_);
return v_m_1018_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___redArg___closed__1() -> *mut lean_object{
let mut v_m_1019_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1020_: *mut lean_object = core::ptr::null_mut(); 
v_m_1019_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___redArg___closed__0), core::ptr::addr_of_mut!(l_main___redArg___closed__0_once), _init_l_main___redArg___closed__0);
v___x_1020_ = l_Lean_PersistentHashMap_stats___at___00main_spec__0___redArg(v_m_1019_);
return v___x_1020_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___redArg___closed__2() -> *mut lean_object{
let mut v_m_1021_: *mut lean_object = core::ptr::null_mut(); let mut v_n_1022_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1023_: *mut lean_object = core::ptr::null_mut(); 
v_m_1021_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___redArg___closed__0), core::ptr::addr_of_mut!(l_main___redArg___closed__0_once), _init_l_main___redArg___closed__0);
v_n_1022_ = lean_unsigned_to_nat(5000);
v___x_1023_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00delOdd_spec__1___redArg(v_n_1022_, v_n_1022_, v_m_1021_);
return v___x_1023_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___redArg___closed__3() -> *mut lean_object{
let mut v___x_1024_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1025_: *mut lean_object = core::ptr::null_mut(); 
v___x_1024_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___redArg___closed__2), core::ptr::addr_of_mut!(l_main___redArg___closed__2_once), _init_l_main___redArg___closed__2);
v___x_1025_ = l_Lean_PersistentHashMap_stats___at___00main_spec__0___redArg(v___x_1024_);
return v___x_1025_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___redArg___closed__4() -> *mut lean_object{
let mut v___x_1026_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1027_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1028_: *mut lean_object = core::ptr::null_mut(); 
v___x_1026_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___redArg___closed__2), core::ptr::addr_of_mut!(l_main___redArg___closed__2_once), _init_l_main___redArg___closed__2);
v___x_1027_ = lean_unsigned_to_nat(4900);
v___x_1028_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00delLess_spec__0___redArg(v___x_1027_, v___x_1027_, v___x_1026_);
return v___x_1028_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___redArg___closed__5() -> *mut lean_object{
let mut v___x_1029_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1030_: *mut lean_object = core::ptr::null_mut(); 
v___x_1029_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___redArg___closed__4), core::ptr::addr_of_mut!(l_main___redArg___closed__4_once), _init_l_main___redArg___closed__4);
v___x_1030_ = l_Lean_PersistentHashMap_stats___at___00main_spec__0___redArg(v___x_1029_);
return v___x_1030_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___redArg___closed__6() -> *mut lean_object{
let mut v___x_1031_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1032_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1033_: *mut lean_object = core::ptr::null_mut(); 
v___x_1031_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___redArg___closed__4), core::ptr::addr_of_mut!(l_main___redArg___closed__4_once), _init_l_main___redArg___closed__4);
v___x_1032_ = lean_unsigned_to_nat(4990);
v___x_1033_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00delLess_spec__0___redArg(v___x_1032_, v___x_1032_, v___x_1031_);
return v___x_1033_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___redArg___closed__7() -> *mut lean_object{
let mut v___x_1034_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1035_: *mut lean_object = core::ptr::null_mut(); 
v___x_1034_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___redArg___closed__6), core::ptr::addr_of_mut!(l_main___redArg___closed__6_once), _init_l_main___redArg___closed__6);
v___x_1035_ = l_Lean_PersistentHashMap_stats___at___00main_spec__0___redArg(v___x_1034_);
return v___x_1035_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___redArg() -> *mut lean_object{
let mut v_n_1037_: *mut lean_object = core::ptr::null_mut(); let mut v_m_1038_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1039_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1040_: *mut lean_object = core::ptr::null_mut(); 
v_n_1037_ = lean_unsigned_to_nat(5000);
v_m_1038_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___redArg___closed__0), core::ptr::addr_of_mut!(l_main___redArg___closed__0_once), _init_l_main___redArg___closed__0);
v___x_1039_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___redArg___closed__1), core::ptr::addr_of_mut!(l_main___redArg___closed__1_once), _init_l_main___redArg___closed__1);
v___x_1040_ = l_IO_println___at___00main_spec__1(v___x_1039_);
if lean_obj_tag(v___x_1040_) == 0 {
let mut v___x_1041_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_1040_, 1);
v___x_1041_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00check_spec__2___redArg(v_m_1038_, v_n_1037_, v_n_1037_);
if lean_obj_tag(v___x_1041_) == 0 {
let mut v___x_1042_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1043_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1044_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_1041_, 1);
v___x_1042_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___redArg___closed__2), core::ptr::addr_of_mut!(l_main___redArg___closed__2_once), _init_l_main___redArg___closed__2);
v___x_1043_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___redArg___closed__3), core::ptr::addr_of_mut!(l_main___redArg___closed__3_once), _init_l_main___redArg___closed__3);
v___x_1044_ = l_IO_println___at___00main_spec__1(v___x_1043_);
if lean_obj_tag(v___x_1044_) == 0 {
let mut v___x_1045_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1046_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_1044_, 1);
v___x_1045_ = lean_unsigned_to_nat(0);
v___x_1046_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00check2_spec__1___redArg(v___x_1045_, v___x_1042_, v_n_1037_, v_n_1037_);
if lean_obj_tag(v___x_1046_) == 0 {
let mut v___x_1047_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1048_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1049_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_1046_, 1);
v___x_1047_ = lean_unsigned_to_nat(4900);
v___x_1048_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___redArg___closed__4), core::ptr::addr_of_mut!(l_main___redArg___closed__4_once), _init_l_main___redArg___closed__4);
v___x_1049_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00check2_spec__1___redArg(v___x_1047_, v___x_1048_, v_n_1037_, v_n_1037_);
if lean_obj_tag(v___x_1049_) == 0 {
let mut v___x_1050_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1051_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_1049_, 1);
v___x_1050_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___redArg___closed__5), core::ptr::addr_of_mut!(l_main___redArg___closed__5_once), _init_l_main___redArg___closed__5);
v___x_1051_ = l_IO_println___at___00main_spec__1(v___x_1050_);
if lean_obj_tag(v___x_1051_) == 0 {
let mut v___x_1052_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1053_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1054_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_1051_, 1);
v___x_1052_ = lean_unsigned_to_nat(4990);
v___x_1053_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___redArg___closed__6), core::ptr::addr_of_mut!(l_main___redArg___closed__6_once), _init_l_main___redArg___closed__6);
v___x_1054_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00check2_spec__1___redArg(v___x_1052_, v___x_1053_, v_n_1037_, v_n_1037_);
if lean_obj_tag(v___x_1054_) == 0 {
let mut v___x_1055_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1056_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_1054_, 1);
v___x_1055_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___redArg___closed__7), core::ptr::addr_of_mut!(l_main___redArg___closed__7_once), _init_l_main___redArg___closed__7);
v___x_1056_ = l_IO_println___at___00main_spec__1(v___x_1055_);
return v___x_1056_;
} else {
return v___x_1054_;
}
} else {
return v___x_1051_;
}
} else {
return v___x_1049_;
}
} else {
return v___x_1046_;
}
} else {
return v___x_1044_;
}
} else {
return v___x_1041_;
}
} else {
return v___x_1040_;
}
}
#[no_mangle] pub unsafe extern "C" fn l_main___redArg___boxed(mut v_a_1057_: *mut lean_object) -> *mut lean_object{
let mut v_res_1058_: *mut lean_object = core::ptr::null_mut(); 
v_res_1058_ = l_main___redArg();
return v_res_1058_;
}
#[no_mangle] pub unsafe extern "C" fn _lean_main(mut v_xs_1059_: *mut lean_object) -> *mut lean_object{
let mut v___x_1061_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_xs_1059_);
v___x_1061_ = l_main___redArg();
return v___x_1061_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___boxed(mut v_xs_1062_: *mut lean_object, mut v_a_1063_: *mut lean_object) -> *mut lean_object{
let mut v_res_1064_: *mut lean_object = core::ptr::null_mut(); 
v_res_1064_ = _lean_main(v_xs_1062_);
return v_res_1064_;
}
static mut _G_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn initialize_phashmap(builtin: u8) -> *mut lean_object {
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
  lean_initialize();
  let res = initialize_phashmap(1 /* builtin */);
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
