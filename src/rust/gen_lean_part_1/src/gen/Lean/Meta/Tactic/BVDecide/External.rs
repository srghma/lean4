// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.External
// Imports: Std.Tactic.BVDecide.LRAT.Parser Lean.CoreM Std.Tactic.BVDecide.Syntax
use crate::ffi::{
    lean_array_push, lean_array_size, lean_array_uget, lean_array_uset, lean_byte_array_fget,
    lean_byte_array_size, lean_int_dec_lt, lean_int_neg, lean_io_as_task,
    lean_io_process_child_kill, lean_io_process_child_try_wait, lean_io_process_child_wait,
    lean_io_process_spawn, lean_mk_empty_array_with_capacity, lean_nat_abs, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_mul, lean_nat_sub, lean_nat_to_int,
    lean_st_ref_get, lean_string_append, lean_string_memcmp, lean_string_to_utf8,
    lean_string_utf8_byte_size, lean_task_get_own, lean_uint8_dec_eq, lean_uint8_dec_le,
    lean_uint8_sub, lean_uint8_to_nat, lean_uint8_to_uint32, lean_uint32_dec_eq,
    lean_uint32_to_uint8, lean_usize_add, lean_usize_dec_lt,
};
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::System::CancelToken::l_IO_CancelToken_isSet;
use crate::r#gen::Init::System::IO::{l_IO_FS_Handle_readToEnd, l_IO_sleep};
use crate::r#gen::Init::System::IOError::{lean_io_error_to_string, lean_mk_io_user_error};
use crate::r#gen::Lean::CoreM::{initialize_Lean_CoreM, runtime_initialize_Lean_CoreM};
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Exception::l_Lean_interruptExceptionId;
use crate::r#gen::Lean::Message::l_Lean_MessageData_ofFormat;
use crate::r#gen::Std::Internal::Parsec::ByteArray::{
    l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go,
    l_Std_Internal_Parsec_ByteArray_Parser_run___redArg, l_Std_Internal_Parsec_ByteArray_skipBytes,
};
use crate::r#gen::Std::Tactic::BVDecide::LRAT::Parser::{
    initialize_Std_Tactic_BVDecide_LRAT_Parser, runtime_initialize_Std_Tactic_BVDecide_LRAT_Parser,
};
use crate::r#gen::Std::Tactic::BVDecide::Syntax::{
    initialize_Std_Tactic_BVDecide_Syntax, runtime_initialize_Std_Tactic_BVDecide_Syntax,
};
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__0: u8 = 0;
pub static l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__1_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [101, 120, 112, 101, 99, 116, 101, 100, 58, 32, 39, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__1_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__5_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [39, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__5_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__6_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__6: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__8_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [100, 105, 103, 105, 116, 32, 101, 120, 112, 101, 99, 116, 101, 100, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__8_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__9_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__8_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__9_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__10_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__10: u8 = 0;
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__11: u8 = 0;
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__12_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__12: u8 = 0;
pub static l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__13_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [105, 100, 32, 119, 97, 115, 32, 48, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__13_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__14_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__13_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__14_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__15_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__15: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__16_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__16: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__17_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__17: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__18_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__18: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__19_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__19: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__2___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__2___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__0: u8 = 0;
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__6_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__7_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [32, 48, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__7_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__8_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__8: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__9_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [13, 10, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__9_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__10_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__10: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__11: u8 = 0;
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__12_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__12: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__13_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__13: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__14_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__14: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__15_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__15: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__16_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__16: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseLines___closed__0_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseLines___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseLines___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseHeader___closed__0_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [115, 32, 83, 65, 84, 73, 83, 70, 73, 65, 66, 76, 69, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseHeader___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseHeader___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseHeader___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseHeader___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___closed__0_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0
            + 8) as u16,
        other: 0,
        tag: 0,
    },
    m_objs: [2 as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___closed__0_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___closed__0_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [45, 45, 117, 110, 115, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___closed__1_value: leanh::LeanArrayObject<1> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*1) as u16, other: 0, tag: 246 }, m_size: 1, m_capacity: 1, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___closed__0_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___closed__2_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [45, 45, 115, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___closed__3_value: leanh::LeanArrayObject<1> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*1) as u16, other: 0, tag: 246 }, m_size: 1, m_capacity: 1, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___closed__2_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___closed__4_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [45, 45, 100, 101, 102, 97, 117, 108, 116, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___closed__5_value: leanh::LeanArrayObject<1> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*1) as u16, other: 0, tag: 246 }, m_size: 1, m_capacity: 1, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___closed__4_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___closed__5_value) as *mut leanh::LeanObject;
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__0_value:
    leanh::LeanStringObject<57> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 57,
    m_capacity: 57,
    m_length: 56,
    m_data: [
        84, 104, 101, 32, 101, 120, 116, 101, 114, 110, 97, 108, 32, 112, 114, 111, 118, 101, 114,
        32, 112, 114, 111, 100, 117, 99, 101, 100, 32, 117, 110, 101, 120, 112, 101, 99, 116, 101,
        100, 32, 111, 117, 116, 112, 117, 116, 44, 32, 115, 116, 100, 111, 117, 116, 58, 10, 0,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__1_value:
    leanh::LeanStringObject<9> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [115, 116, 100, 101, 114, 114, 58, 10, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__3_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [69, 114, 114, 111, 114, 32, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__4_value:
    leanh::LeanStringObject<17> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 17,
    m_capacity: 17,
    m_length: 16,
    m_data: [
        32, 119, 104, 105, 108, 101, 32, 112, 97, 114, 115, 105, 110, 103, 58, 10, 0,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__5_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [45, 45, 108, 114, 97, 116, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__6_value:
    leanh::LeanStringObject<10> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [45, 45, 98, 105, 110, 97, 114, 121, 61, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__7_value:
    leanh::LeanStringObject<8> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [45, 45, 113, 117, 105, 101, 116, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__7:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__8_value:
    leanh::LeanStringObject<11> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [45, 45, 115, 104, 114, 105, 110, 107, 61, 48, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__9_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0
            + 8) as u16,
        other: 0,
        tag: 0,
    },
    m_objs: [131072 as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__9:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__10_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__10:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__11_value:
    leanh::LeanStringObject<16> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 16,
    m_capacity: 16,
    m_length: 15,
    m_data: [
        115, 32, 85, 78, 83, 65, 84, 73, 83, 70, 73, 65, 66, 76, 69, 0,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__11:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__11_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__12_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__12:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__13_value:
    leanh::LeanStringObject<36> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 36,
    m_capacity: 36,
    m_length: 35,
    m_data: [
        70, 97, 105, 108, 101, 100, 32, 116, 111, 32, 101, 120, 101, 99, 117, 116, 101, 32, 101,
        120, 116, 101, 114, 110, 97, 108, 32, 112, 114, 111, 118, 101, 114, 58, 10, 0,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__13:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__14_value:
    leanh::LeanStringObject<245> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 245,
    m_capacity: 245,
    m_length: 244,
    m_data: [
        84, 104, 101, 32, 83, 65, 84, 32, 115, 111, 108, 118, 101, 114, 32, 116, 105, 109, 101,
        100, 32, 111, 117, 116, 32, 119, 104, 105, 108, 101, 32, 115, 111, 108, 118, 105, 110, 103,
        32, 116, 104, 101, 32, 112, 114, 111, 98, 108, 101, 109, 46, 10, 67, 111, 110, 115, 105,
        100, 101, 114, 32, 105, 110, 99, 114, 101, 97, 115, 105, 110, 103, 32, 116, 104, 101, 32,
        116, 105, 109, 101, 111, 117, 116, 32, 119, 105, 116, 104, 32, 116, 104, 101, 32, 96, 116,
        105, 109, 101, 111, 117, 116, 96, 32, 99, 111, 110, 102, 105, 103, 32, 111, 112, 116, 105,
        111, 110, 46, 10, 73, 102, 32, 115, 111, 108, 118, 105, 110, 103, 32, 121, 111, 117, 114,
        32, 112, 114, 111, 98, 108, 101, 109, 32, 114, 101, 108, 105, 101, 115, 32, 105, 110, 104,
        101, 114, 101, 110, 116, 108, 121, 32, 111, 110, 32, 117, 115, 105, 110, 103, 32, 97, 115,
        115, 111, 99, 105, 97, 116, 105, 118, 105, 116, 121, 32, 111, 114, 32, 99, 111, 109, 109,
        117, 116, 97, 116, 105, 118, 105, 116, 121, 44, 32, 99, 111, 110, 115, 105, 100, 101, 114,
        32, 101, 110, 97, 98, 108, 105, 110, 103, 32, 116, 104, 101, 32, 96, 97, 99, 78, 102, 96,
        32, 99, 111, 110, 102, 105, 103, 32, 111, 112, 116, 105, 111, 110, 46, 0,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__14:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__15_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__14_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__15:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__15_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__16_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__16:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__17_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [102, 97, 108, 115, 101, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__17:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__17_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__18_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [116, 114, 117, 101, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__18:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__18_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_External_SolverResult_ctorIdx(
    mut v_x_1289_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1289_) == 0 {
        let mut v___x_1290_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1290_ = leanh::lean_unsigned_to_nat(0);
        return v___x_1290_;
    } else {
        let mut v___x_1291_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1291_ = leanh::lean_unsigned_to_nat(1);
        return v___x_1291_;
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_External_SolverResult_ctorIdx___boxed(
    mut v_x_1292_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1293_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1293_ = l_Lean_Meta_Tactic_BVDecide_External_SolverResult_ctorIdx(v_x_1292_);
    leanh::lean_dec(v_x_1292_);
    return v_res_1293_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_External_SolverResult_ctorElim___redArg(
    mut v_t_1294_: *mut leanh::LeanObject,
    mut v_k_1295_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_t_1294_) == 0 {
        let mut v_assignment_1296_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1297_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_assignment_1296_ = leanh::lean_ctor_get(v_t_1294_, 0);
        leanh::lean_inc_ref(v_assignment_1296_);
        leanh::lean_dec_ref_known(v_t_1294_, 1);
        v___x_1297_ = leanh::lean_apply_1(v_k_1295_, v_assignment_1296_);
        return v___x_1297_;
    } else {
        return v_k_1295_;
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_External_SolverResult_ctorElim(
    mut v_motive_1298_: *mut leanh::LeanObject,
    mut v_ctorIdx_1299_: *mut leanh::LeanObject,
    mut v_t_1300_: *mut leanh::LeanObject,
    mut v_h_1301_: *mut leanh::LeanObject,
    mut v_k_1302_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1303_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1303_ =
        l_Lean_Meta_Tactic_BVDecide_External_SolverResult_ctorElim___redArg(v_t_1300_, v_k_1302_);
    return v___x_1303_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_External_SolverResult_ctorElim___boxed(
    mut v_motive_1304_: *mut leanh::LeanObject,
    mut v_ctorIdx_1305_: *mut leanh::LeanObject,
    mut v_t_1306_: *mut leanh::LeanObject,
    mut v_h_1307_: *mut leanh::LeanObject,
    mut v_k_1308_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1309_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1309_ = l_Lean_Meta_Tactic_BVDecide_External_SolverResult_ctorElim(
        v_motive_1304_,
        v_ctorIdx_1305_,
        v_t_1306_,
        v_h_1307_,
        v_k_1308_,
    );
    leanh::lean_dec(v_ctorIdx_1305_);
    return v_res_1309_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_External_SolverResult_sat_elim___redArg(
    mut v_t_1310_: *mut leanh::LeanObject,
    mut v_sat_1311_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1312_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1312_ =
        l_Lean_Meta_Tactic_BVDecide_External_SolverResult_ctorElim___redArg(v_t_1310_, v_sat_1311_);
    return v___x_1312_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_External_SolverResult_sat_elim(
    mut v_motive_1313_: *mut leanh::LeanObject,
    mut v_t_1314_: *mut leanh::LeanObject,
    mut v_h_1315_: *mut leanh::LeanObject,
    mut v_sat_1316_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1317_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1317_ =
        l_Lean_Meta_Tactic_BVDecide_External_SolverResult_ctorElim___redArg(v_t_1314_, v_sat_1316_);
    return v___x_1317_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_External_SolverResult_unsat_elim___redArg(
    mut v_t_1318_: *mut leanh::LeanObject,
    mut v_unsat_1319_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1320_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1320_ = l_Lean_Meta_Tactic_BVDecide_External_SolverResult_ctorElim___redArg(
        v_t_1318_,
        v_unsat_1319_,
    );
    return v___x_1320_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_External_SolverResult_unsat_elim(
    mut v_motive_1321_: *mut leanh::LeanObject,
    mut v_t_1322_: *mut leanh::LeanObject,
    mut v_h_1323_: *mut leanh::LeanObject,
    mut v_unsat_1324_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1325_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1325_ = l_Lean_Meta_Tactic_BVDecide_External_SolverResult_ctorElim___redArg(
        v_t_1322_,
        v_unsat_1324_,
    );
    return v___x_1325_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__0()
-> u8 {
    let mut v___x_1326_: u32 = 0;
    let mut v___x_1327_: u8 = 0;
    v___x_1326_ = 32;
    v___x_1327_ = lean_uint32_to_uint8(v___x_1326_);
    return v___x_1327_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1329_: u8 = 0;
    let mut v___x_1330_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1329_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__0_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__0);
    v___x_1330_ = lean_uint8_to_nat(v___x_1329_);
    return v___x_1330_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1331_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__2_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__2);
    v___x_1332_ = l_Nat_reprFast(v___x_1331_);
    return v___x_1332_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1333_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__3_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__3);
    v___x_1334_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__1;
    v___x_1335_ = lean_string_append(v___x_1334_, v___x_1333_);
    return v___x_1335_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_1337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1337_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__5;
    v___x_1338_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__4_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__4);
    v___x_1339_ = lean_string_append(v___x_1338_, v___x_1337_);
    return v___x_1339_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_1340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1340_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__6_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__6);
    v___x_1341_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1341_, 0, v___x_1340_);
    return v___x_1341_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__10()
-> u8 {
    let mut v___x_1345_: u32 = 0;
    let mut v___x_1346_: u8 = 0;
    v___x_1345_ = 45;
    v___x_1346_ = lean_uint32_to_uint8(v___x_1345_);
    return v___x_1346_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__11()
-> u8 {
    let mut v___x_1347_: u32 = 0;
    let mut v___x_1348_: u8 = 0;
    v___x_1347_ = 48;
    v___x_1348_ = lean_uint32_to_uint8(v___x_1347_);
    return v___x_1348_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__12()
-> u8 {
    let mut v___x_1349_: u32 = 0;
    let mut v___x_1350_: u8 = 0;
    v___x_1349_ = 57;
    v___x_1350_ = lean_uint32_to_uint8(v___x_1349_);
    return v___x_1350_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_1354_: u8 = 0;
    let mut v___x_1355_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1354_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__10_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__10);
    v___x_1355_ = lean_uint8_to_nat(v___x_1354_);
    return v___x_1355_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__16()
-> *mut leanh::LeanObject {
    let mut v___x_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1356_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__15), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__15_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__15);
    v___x_1357_ = l_Nat_reprFast(v___x_1356_);
    return v___x_1357_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_1358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1358_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__16), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__16_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__16);
    v___x_1359_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__1;
    v___x_1360_ = lean_string_append(v___x_1359_, v___x_1358_);
    return v___x_1360_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__18()
-> *mut leanh::LeanObject {
    let mut v___x_1361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1361_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__5;
    v___x_1362_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__17), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__17_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__17);
    v___x_1363_ = lean_string_append(v___x_1362_, v___x_1361_);
    return v___x_1363_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__19()
-> *mut leanh::LeanObject {
    let mut v___x_1364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1364_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__18), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__18_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__18);
    v___x_1365_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1365_, 0, v___x_1364_);
    return v___x_1365_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit(
    mut v_a_1366_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_array_1367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: u8 = 0;
    let mut v___x_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: u8 = 0;
    let mut v_got_1374_: u8 = 0;
    let mut v___x_1375_: u8 = 0;
    let mut v___x_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1380_: u8 = 0;
    let mut v___x_1381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1388_: u8 = 0;
    let mut v___x_1389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: u8 = 0;
    let mut v___x_1392_: u8 = 0;
    let mut v___x_1393_: u8 = 0;
    let mut v___x_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: u8 = 0;
    let mut v___x_1397_: u8 = 0;
    let mut v___x_1398_: u8 = 0;
    let mut v___x_1399_: u8 = 0;
    let mut v___x_1400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_x27_1401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: u32 = 0;
    let mut v___x_1403_: u8 = 0;
    let mut v___x_1404_: u8 = 0;
    let mut v___x_1405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1411_: u8 = 0;
    let mut v___x_1412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: u8 = 0;
    let mut v___x_1414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1422_: u8 = 0;
    let mut v___x_1423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: u8 = 0;
    let mut v___x_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_1435_: u8 = 0;
    let mut v___x_1436_: u8 = 0;
    let mut v___x_1437_: u8 = 0;
    let mut v___x_1438_: u8 = 0;
    let mut v___x_1439_: u8 = 0;
    let mut v___x_1440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_x27_1441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: u32 = 0;
    let mut v___x_1443_: u8 = 0;
    let mut v___x_1444_: u8 = 0;
    let mut v___x_1445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1451_: u8 = 0;
    let mut v___x_1452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: u8 = 0;
    let mut v___x_1454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1463_: u8 = 0;
    let mut v_reuseFailAlloc_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1465_: u8 = 0;
    let mut v_unused_1466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_1367_ = leanh::lean_ctor_get(v_a_1366_, 0);
                v_idx_1368_ = leanh::lean_ctor_get(v_a_1366_, 1);
                v___x_1369_ = lean_byte_array_size(v_array_1367_);
                v___x_1370_ = lean_nat_dec_lt(v_idx_1368_, v___x_1369_);
                if v___x_1370_ == 0 {
                    v___x_1371_ = leanh::lean_box(0);
                    v___x_1372_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1372_, 0, v_a_1366_);
                    leanh::lean_ctor_set(v___x_1372_, 1, v___x_1371_);
                    return v___x_1372_;
                } else {
                    v___x_1373_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__0_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__0);
                    v_got_1374_ = lean_byte_array_fget(v_array_1367_, v_idx_1368_);
                    v___x_1375_ = lean_uint8_dec_eq(v_got_1374_, v___x_1373_);
                    if v___x_1375_ == 0 {
                        v___x_1376_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__7_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__7);
                        v___x_1377_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1377_, 0, v_a_1366_);
                        leanh::lean_ctor_set(v___x_1377_, 1, v___x_1376_);
                        return v___x_1377_;
                    } else {
                        leanh::lean_inc(v_idx_1368_);
                        leanh::lean_inc_ref(v_array_1367_);
                        v_isSharedCheck_1465_ = (!leanh::lean_is_exclusive(v_a_1366_)) as u8;
                        if v_isSharedCheck_1465_ == 0 {
                            v_unused_1466_ = leanh::lean_ctor_get(v_a_1366_, 1);
                            leanh::lean_dec(v_unused_1466_);
                            v_unused_1467_ = leanh::lean_ctor_get(v_a_1366_, 0);
                            leanh::lean_dec(v_unused_1467_);
                            v___x_1379_ = v_a_1366_;
                            v_isShared_1380_ = v_isSharedCheck_1465_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_a_1366_);
                            v___x_1379_ = leanh::lean_box(0);
                            v_isShared_1380_ = v_isSharedCheck_1465_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1381_ = leanh::lean_unsigned_to_nat(1);
                v___x_1382_ = lean_nat_add(v_idx_1368_, v___x_1381_);
                leanh::lean_dec(v_idx_1368_);
                leanh::lean_inc(v___x_1382_);
                leanh::lean_inc_ref(v_array_1367_);
                if v_isShared_1380_ == 0 {
                    leanh::lean_ctor_set(v___x_1379_, 1, v___x_1382_);
                    v___x_1384_ = v___x_1379_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1464_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_array_1367_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1464_, 1, v___x_1382_);
                    v___x_1384_ = v_reuseFailAlloc_1464_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1388_ = lean_nat_dec_lt(v___x_1382_, v___x_1369_);
                if v___x_1388_ == 0 {
                    leanh::lean_dec(v___x_1382_);
                    leanh::lean_dec_ref(v_array_1367_);
                    v___x_1389_ = leanh::lean_box(0);
                    v___x_1390_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1390_, 0, v___x_1384_);
                    leanh::lean_ctor_set(v___x_1390_, 1, v___x_1389_);
                    return v___x_1390_;
                } else {
                    v___x_1391_ = lean_byte_array_fget(v_array_1367_, v___x_1382_);
                    v___x_1392_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__10_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__10);
                    v___x_1393_ = lean_uint8_dec_eq(v___x_1391_, v___x_1392_);
                    if v___x_1393_ == 0 {
                        if v___x_1388_ == 0 {
                            leanh::lean_dec(v___x_1382_);
                            leanh::lean_dec_ref(v_array_1367_);
                            v___x_1394_ = leanh::lean_box(0);
                            v___x_1395_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_1395_, 0, v___x_1384_);
                            leanh::lean_ctor_set(v___x_1395_, 1, v___x_1394_);
                            return v___x_1395_;
                        } else {
                            v___x_1396_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__11_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__11);
                            v___x_1397_ = lean_uint8_dec_le(v___x_1396_, v___x_1391_);
                            if v___x_1397_ == 0 {
                                leanh::lean_dec(v___x_1382_);
                                leanh::lean_dec_ref(v_array_1367_);
                                state = 3;
                                continue;
                            } else {
                                v___x_1398_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__12), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__12_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__12);
                                v___x_1399_ = lean_uint8_dec_le(v___x_1391_, v___x_1398_);
                                if v___x_1399_ == 0 {
                                    leanh::lean_dec(v___x_1382_);
                                    leanh::lean_dec_ref(v_array_1367_);
                                    state = 3;
                                    continue;
                                } else {
                                    leanh::lean_dec_ref(v___x_1384_);
                                    v___x_1400_ = lean_nat_add(v___x_1382_, v___x_1381_);
                                    leanh::lean_dec(v___x_1382_);
                                    v_it_x27_1401_ =
                                        leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    leanh::lean_ctor_set(v_it_x27_1401_, 0, v_array_1367_);
                                    leanh::lean_ctor_set(v_it_x27_1401_, 1, v___x_1400_);
                                    v___x_1402_ = lean_uint8_to_uint32(v___x_1391_);
                                    v___x_1403_ = lean_uint32_to_uint8(v___x_1402_);
                                    v___x_1404_ = lean_uint8_sub(v___x_1403_, v___x_1396_);
                                    v___x_1405_ = lean_uint8_to_nat(v___x_1404_);
                                    v___x_1406_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_1401_, v___x_1405_);
                                    v_fst_1407_ = leanh::lean_ctor_get(v___x_1406_, 0);
                                    v_snd_1408_ = leanh::lean_ctor_get(v___x_1406_, 1);
                                    v_isSharedCheck_1422_ =
                                        (!leanh::lean_is_exclusive(v___x_1406_)) as u8;
                                    if v_isSharedCheck_1422_ == 0 {
                                        v___x_1410_ = v___x_1406_;
                                        v_isShared_1411_ = v_isSharedCheck_1422_;
                                        state = 4;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_snd_1408_);
                                        leanh::lean_inc(v_fst_1407_);
                                        leanh::lean_dec(v___x_1406_);
                                        v___x_1410_ = leanh::lean_box(0);
                                        v_isShared_1411_ = v_isSharedCheck_1422_;
                                        state = 4;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        if v___x_1388_ == 0 {
                            leanh::lean_dec(v___x_1382_);
                            leanh::lean_dec_ref(v_array_1367_);
                            v___x_1423_ = leanh::lean_box(0);
                            v___x_1424_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_1424_, 0, v___x_1384_);
                            leanh::lean_ctor_set(v___x_1424_, 1, v___x_1423_);
                            return v___x_1424_;
                        } else {
                            if v___x_1393_ == 0 {
                                leanh::lean_dec(v___x_1382_);
                                leanh::lean_dec_ref(v_array_1367_);
                                v___x_1425_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__19), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__19_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__19);
                                v___x_1426_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_1426_, 0, v___x_1384_);
                                leanh::lean_ctor_set(v___x_1426_, 1, v___x_1425_);
                                return v___x_1426_;
                            } else {
                                leanh::lean_dec_ref(v___x_1384_);
                                v___x_1427_ = lean_nat_add(v___x_1382_, v___x_1381_);
                                leanh::lean_dec(v___x_1382_);
                                leanh::lean_inc(v___x_1427_);
                                leanh::lean_inc_ref(v_array_1367_);
                                v___x_1428_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_1428_, 0, v_array_1367_);
                                leanh::lean_ctor_set(v___x_1428_, 1, v___x_1427_);
                                v___x_1432_ = lean_nat_dec_lt(v___x_1427_, v___x_1369_);
                                if v___x_1432_ == 0 {
                                    leanh::lean_dec(v___x_1427_);
                                    leanh::lean_dec_ref(v_array_1367_);
                                    v___x_1433_ = leanh::lean_box(0);
                                    v___x_1434_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_1434_, 0, v___x_1428_);
                                    leanh::lean_ctor_set(v___x_1434_, 1, v___x_1433_);
                                    return v___x_1434_;
                                } else {
                                    v_c_1435_ = lean_byte_array_fget(v_array_1367_, v___x_1427_);
                                    v___x_1436_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__11_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__11);
                                    v___x_1437_ = lean_uint8_dec_le(v___x_1436_, v_c_1435_);
                                    if v___x_1437_ == 0 {
                                        leanh::lean_dec(v___x_1427_);
                                        leanh::lean_dec_ref(v_array_1367_);
                                        state = 7;
                                        continue;
                                    } else {
                                        v___x_1438_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__12), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__12_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__12);
                                        v___x_1439_ = lean_uint8_dec_le(v_c_1435_, v___x_1438_);
                                        if v___x_1439_ == 0 {
                                            leanh::lean_dec(v___x_1427_);
                                            leanh::lean_dec_ref(v_array_1367_);
                                            state = 7;
                                            continue;
                                        } else {
                                            leanh::lean_dec_ref_known(v___x_1428_, 2);
                                            v___x_1440_ = lean_nat_add(v___x_1427_, v___x_1381_);
                                            leanh::lean_dec(v___x_1427_);
                                            v_it_x27_1441_ =
                                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                            leanh::lean_ctor_set(
                                                v_it_x27_1441_,
                                                0,
                                                v_array_1367_,
                                            );
                                            leanh::lean_ctor_set(
                                                v_it_x27_1441_,
                                                1,
                                                v___x_1440_,
                                            );
                                            v___x_1442_ = lean_uint8_to_uint32(v_c_1435_);
                                            v___x_1443_ = lean_uint32_to_uint8(v___x_1442_);
                                            v___x_1444_ = lean_uint8_sub(v___x_1443_, v___x_1436_);
                                            v___x_1445_ = lean_uint8_to_nat(v___x_1444_);
                                            v___x_1446_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_1441_, v___x_1445_);
                                            v_fst_1447_ =
                                                leanh::lean_ctor_get(v___x_1446_, 0);
                                            v_snd_1448_ =
                                                leanh::lean_ctor_get(v___x_1446_, 1);
                                            v_isSharedCheck_1463_ =
                                                (!leanh::lean_is_exclusive(v___x_1446_))
                                                    as u8;
                                            if v_isSharedCheck_1463_ == 0 {
                                                v___x_1450_ = v___x_1446_;
                                                v_isShared_1451_ = v_isSharedCheck_1463_;
                                                state = 8;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_snd_1448_);
                                                leanh::lean_inc(v_fst_1447_);
                                                leanh::lean_dec(v___x_1446_);
                                                v___x_1450_ = leanh::lean_box(0);
                                                v_isShared_1451_ = v_isSharedCheck_1463_;
                                                state = 8;
                                                continue;
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            3 => {
                v___x_1386_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__9;
                v___x_1387_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1387_, 0, v___x_1384_);
                leanh::lean_ctor_set(v___x_1387_, 1, v___x_1386_);
                return v___x_1387_;
            }
            4 => {
                v___x_1412_ = leanh::lean_unsigned_to_nat(0);
                v___x_1413_ = lean_nat_dec_eq(v_fst_1407_, v___x_1412_);
                if v___x_1413_ == 0 {
                    v___x_1414_ = lean_nat_to_int(v_fst_1407_);
                    if v_isShared_1411_ == 0 {
                        leanh::lean_ctor_set(v___x_1410_, 1, v___x_1414_);
                        leanh::lean_ctor_set(v___x_1410_, 0, v_snd_1408_);
                        v___x_1416_ = v___x_1410_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1417_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1417_, 0, v_snd_1408_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1417_, 1, v___x_1414_);
                        v___x_1416_ = v_reuseFailAlloc_1417_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_fst_1407_);
                    v___x_1418_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__14;
                    if v_isShared_1411_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_1410_, 1);
                        leanh::lean_ctor_set(v___x_1410_, 1, v___x_1418_);
                        leanh::lean_ctor_set(v___x_1410_, 0, v_snd_1408_);
                        v___x_1420_ = v___x_1410_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1421_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1421_, 0, v_snd_1408_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1421_, 1, v___x_1418_);
                        v___x_1420_ = v_reuseFailAlloc_1421_;
                        state = 6;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_1416_;
            }
            6 => {
                return v___x_1420_;
            }
            7 => {
                v___x_1430_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__9;
                v___x_1431_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1431_, 0, v___x_1428_);
                leanh::lean_ctor_set(v___x_1431_, 1, v___x_1430_);
                return v___x_1431_;
            }
            8 => {
                v___x_1452_ = leanh::lean_unsigned_to_nat(0);
                v___x_1453_ = lean_nat_dec_eq(v_fst_1447_, v___x_1452_);
                if v___x_1453_ == 0 {
                    v___x_1454_ = lean_nat_to_int(v_fst_1447_);
                    v___x_1455_ = lean_int_neg(v___x_1454_);
                    leanh::lean_dec(v___x_1454_);
                    if v_isShared_1451_ == 0 {
                        leanh::lean_ctor_set(v___x_1450_, 1, v___x_1455_);
                        leanh::lean_ctor_set(v___x_1450_, 0, v_snd_1448_);
                        v___x_1457_ = v___x_1450_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_1458_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1458_, 0, v_snd_1448_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1458_, 1, v___x_1455_);
                        v___x_1457_ = v_reuseFailAlloc_1458_;
                        state = 9;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_fst_1447_);
                    v___x_1459_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__14;
                    if v_isShared_1451_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_1450_, 1);
                        leanh::lean_ctor_set(v___x_1450_, 1, v___x_1459_);
                        leanh::lean_ctor_set(v___x_1450_, 0, v_snd_1448_);
                        v___x_1461_ = v___x_1450_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_1462_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_snd_1448_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1462_, 1, v___x_1459_);
                        v___x_1461_ = v_reuseFailAlloc_1462_;
                        state = 10;
                        continue;
                    }
                }
            }
            9 => {
                return v___x_1457_;
            }
            10 => {
                return v___x_1461_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Nat_cast___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__0(
    mut v_a_1468_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1469_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1469_ = lean_nat_to_int(v_a_1468_);
    return v___x_1469_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__2___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1470_ = leanh::lean_unsigned_to_nat(0);
    v___x_1471_ = lean_nat_to_int(v___x_1470_);
    return v___x_1471_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__2(
    mut v_idx_1472_: *mut leanh::LeanObject,
    mut v___x_1473_: *mut leanh::LeanObject,
    mut v_sz_1474_: usize,
    mut v_i_1475_: usize,
    mut v_bs_1476_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1477_: u8 = 0;
    let mut v_v_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: usize = 0;
    let mut v___x_1484_: usize = 0;
    let mut v___x_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: u8 = 0;
    let mut v___x_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: u8 = 0;
    let mut v___x_1493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1477_ = lean_usize_dec_lt(v_i_1475_, v_sz_1474_);
                if v___x_1477_ == 0 {
                    return v_bs_1476_;
                } else {
                    v_v_1478_ = lean_array_uget(v_bs_1476_, v_i_1475_);
                    v___x_1479_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1480_ = lean_array_uset(v_bs_1476_, v_i_1475_, v___x_1479_);
                    v___x_1487_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__2___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__2___closed__0_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__2___closed__0);
                    v___x_1488_ = lean_int_dec_lt(v___x_1487_, v_v_1478_);
                    if v___x_1488_ == 0 {
                        v___x_1489_ = lean_nat_abs(v_v_1478_);
                        leanh::lean_dec(v_v_1478_);
                        v___x_1490_ = leanh::lean_box((v___x_1488_) as usize);
                        v___x_1491_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1491_, 0, v___x_1490_);
                        leanh::lean_ctor_set(v___x_1491_, 1, v___x_1489_);
                        v___y_1482_ = v___x_1491_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1492_ = lean_nat_dec_lt(v_idx_1472_, v___x_1473_);
                        v___x_1493_ = lean_nat_abs(v_v_1478_);
                        leanh::lean_dec(v_v_1478_);
                        v___x_1494_ = leanh::lean_box((v___x_1492_) as usize);
                        v___x_1495_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1495_, 0, v___x_1494_);
                        leanh::lean_ctor_set(v___x_1495_, 1, v___x_1493_);
                        v___y_1482_ = v___x_1495_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1483_ = 1usize;
                v___x_1484_ = lean_usize_add(v_i_1475_, v___x_1483_);
                v___x_1485_ = lean_array_uset(v_bs_x27_1480_, v_i_1475_, v___y_1482_);
                v_i_1475_ = v___x_1484_;
                v_bs_1476_ = v___x_1485_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__2___boxed(
    mut v_idx_1496_: *mut leanh::LeanObject,
    mut v___x_1497_: *mut leanh::LeanObject,
    mut v_sz_1498_: *mut leanh::LeanObject,
    mut v_i_1499_: *mut leanh::LeanObject,
    mut v_bs_1500_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1501_: usize = 0;
    let mut v_i_boxed_1502_: usize = 0;
    let mut v_res_1503_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1501_ = leanh::lean_unbox_usize(v_sz_1498_);
    leanh::lean_dec(v_sz_1498_);
    v_i_boxed_1502_ = leanh::lean_unbox_usize(v_i_1499_);
    leanh::lean_dec(v_i_1499_);
    v_res_1503_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__2(v_idx_1496_, v___x_1497_, v_sz_boxed_1501_, v_i_boxed_1502_, v_bs_1500_);
    leanh::lean_dec(v___x_1497_);
    leanh::lean_dec(v_idx_1496_);
    return v_res_1503_;
}
pub unsafe fn l_Std_Internal_Parsec_manyCore___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__1(
    mut v_acc_1504_: *mut leanh::LeanObject,
    mut v_a_1505_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pos_1507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_1508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: u8 = 0;
    let mut v___x_1518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: u8 = 0;
    let mut v___x_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: u8 = 0;
    let mut v_got_1528_: u8 = 0;
    let mut v___x_1529_: u8 = 0;
    let mut v___x_1530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: u8 = 0;
    let mut v___x_1534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: u8 = 0;
    let mut v___x_1536_: u8 = 0;
    let mut v___x_1537_: u8 = 0;
    let mut v___x_1538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: u8 = 0;
    let mut v___x_1540_: u8 = 0;
    let mut v___x_1541_: u8 = 0;
    let mut v___x_1542_: u8 = 0;
    let mut v___x_1543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_x27_1544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: u32 = 0;
    let mut v___x_1546_: u8 = 0;
    let mut v___x_1547_: u8 = 0;
    let mut v___x_1548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: u8 = 0;
    let mut v___x_1554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: u8 = 0;
    let mut v___x_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_1561_: u8 = 0;
    let mut v___x_1562_: u8 = 0;
    let mut v___x_1563_: u8 = 0;
    let mut v___x_1564_: u8 = 0;
    let mut v___x_1565_: u8 = 0;
    let mut v___x_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_x27_1567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: u32 = 0;
    let mut v___x_1569_: u8 = 0;
    let mut v___x_1570_: u8 = 0;
    let mut v___x_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: u8 = 0;
    let mut v___x_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_1511_ = leanh::lean_ctor_get(v_a_1505_, 0);
                v_idx_1512_ = leanh::lean_ctor_get(v_a_1505_, 1);
                leanh::lean_inc(v_idx_1512_);
                v___x_1524_ = lean_byte_array_size(v_array_1511_);
                v___x_1525_ = lean_nat_dec_lt(v_idx_1512_, v___x_1524_);
                if v___x_1525_ == 0 {
                    v___x_1526_ = leanh::lean_box(0);
                    leanh::lean_inc(v_idx_1512_);
                    v_pos_1514_ = v_a_1505_;
                    v_idx_1515_ = v_idx_1512_;
                    v_err_1516_ = v___x_1526_;
                    state = 2;
                    continue;
                } else {
                    v___x_1527_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__0_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__0);
                    v_got_1528_ = lean_byte_array_fget(v_array_1511_, v_idx_1512_);
                    v___x_1529_ = lean_uint8_dec_eq(v_got_1528_, v___x_1527_);
                    if v___x_1529_ == 0 {
                        v___x_1530_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__7_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__7);
                        leanh::lean_inc(v_idx_1512_);
                        v_pos_1514_ = v_a_1505_;
                        v_idx_1515_ = v_idx_1512_;
                        v_err_1516_ = v___x_1530_;
                        state = 2;
                        continue;
                    } else {
                        v___x_1531_ = leanh::lean_unsigned_to_nat(1);
                        v___x_1532_ = lean_nat_add(v_idx_1512_, v___x_1531_);
                        v___x_1533_ = lean_nat_dec_lt(v___x_1532_, v___x_1524_);
                        if v___x_1533_ == 0 {
                            leanh::lean_dec(v___x_1532_);
                            v___x_1534_ = leanh::lean_box(0);
                            leanh::lean_inc(v_idx_1512_);
                            v_pos_1514_ = v_a_1505_;
                            v_idx_1515_ = v_idx_1512_;
                            v_err_1516_ = v___x_1534_;
                            state = 2;
                            continue;
                        } else {
                            v___x_1535_ = lean_byte_array_fget(v_array_1511_, v___x_1532_);
                            v___x_1536_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__10_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__10);
                            v___x_1537_ = lean_uint8_dec_eq(v___x_1535_, v___x_1536_);
                            if v___x_1537_ == 0 {
                                if v___x_1533_ == 0 {
                                    leanh::lean_dec(v___x_1532_);
                                    v___x_1538_ = leanh::lean_box(0);
                                    leanh::lean_inc(v_idx_1512_);
                                    v_pos_1514_ = v_a_1505_;
                                    v_idx_1515_ = v_idx_1512_;
                                    v_err_1516_ = v___x_1538_;
                                    state = 2;
                                    continue;
                                } else {
                                    v___x_1539_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__11_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__11);
                                    v___x_1540_ = lean_uint8_dec_le(v___x_1539_, v___x_1535_);
                                    if v___x_1540_ == 0 {
                                        leanh::lean_dec(v___x_1532_);
                                        state = 4;
                                        continue;
                                    } else {
                                        v___x_1541_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__12), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__12_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__12);
                                        v___x_1542_ = lean_uint8_dec_le(v___x_1535_, v___x_1541_);
                                        if v___x_1542_ == 0 {
                                            leanh::lean_dec(v___x_1532_);
                                            state = 4;
                                            continue;
                                        } else {
                                            v___x_1543_ = lean_nat_add(v___x_1532_, v___x_1531_);
                                            leanh::lean_dec(v___x_1532_);
                                            leanh::lean_inc_ref(v_array_1511_);
                                            v_it_x27_1544_ =
                                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                            leanh::lean_ctor_set(
                                                v_it_x27_1544_,
                                                0,
                                                v_array_1511_,
                                            );
                                            leanh::lean_ctor_set(
                                                v_it_x27_1544_,
                                                1,
                                                v___x_1543_,
                                            );
                                            v___x_1545_ = lean_uint8_to_uint32(v___x_1535_);
                                            v___x_1546_ = lean_uint32_to_uint8(v___x_1545_);
                                            v___x_1547_ = lean_uint8_sub(v___x_1546_, v___x_1539_);
                                            v___x_1548_ = lean_uint8_to_nat(v___x_1547_);
                                            v___x_1549_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_1544_, v___x_1548_);
                                            v_fst_1550_ =
                                                leanh::lean_ctor_get(v___x_1549_, 0);
                                            leanh::lean_inc(v_fst_1550_);
                                            v_snd_1551_ =
                                                leanh::lean_ctor_get(v___x_1549_, 1);
                                            leanh::lean_inc(v_snd_1551_);
                                            leanh::lean_dec_ref(v___x_1549_);
                                            v___x_1552_ = leanh::lean_unsigned_to_nat(0);
                                            v___x_1553_ = lean_nat_dec_eq(v_fst_1550_, v___x_1552_);
                                            if v___x_1553_ == 0 {
                                                leanh::lean_dec(v_idx_1512_);
                                                leanh::lean_dec_ref(v_a_1505_);
                                                v___x_1554_ = lean_nat_to_int(v_fst_1550_);
                                                v_pos_1507_ = v_snd_1551_;
                                                v_res_1508_ = v___x_1554_;
                                                state = 1;
                                                continue;
                                            } else {
                                                leanh::lean_dec(v_snd_1551_);
                                                leanh::lean_dec(v_fst_1550_);
                                                v___x_1555_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__14;
                                                leanh::lean_inc(v_idx_1512_);
                                                v_pos_1514_ = v_a_1505_;
                                                v_idx_1515_ = v_idx_1512_;
                                                v_err_1516_ = v___x_1555_;
                                                state = 2;
                                                continue;
                                            }
                                        }
                                    }
                                }
                            } else {
                                if v___x_1533_ == 0 {
                                    leanh::lean_dec(v___x_1532_);
                                    v___x_1556_ = leanh::lean_box(0);
                                    leanh::lean_inc(v_idx_1512_);
                                    v_pos_1514_ = v_a_1505_;
                                    v_idx_1515_ = v_idx_1512_;
                                    v_err_1516_ = v___x_1556_;
                                    state = 2;
                                    continue;
                                } else {
                                    if v___x_1537_ == 0 {
                                        leanh::lean_dec(v___x_1532_);
                                        v___x_1557_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__19), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__19_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__19);
                                        leanh::lean_inc(v_idx_1512_);
                                        v_pos_1514_ = v_a_1505_;
                                        v_idx_1515_ = v_idx_1512_;
                                        v_err_1516_ = v___x_1557_;
                                        state = 2;
                                        continue;
                                    } else {
                                        v___x_1558_ = lean_nat_add(v___x_1532_, v___x_1531_);
                                        leanh::lean_dec(v___x_1532_);
                                        v___x_1559_ = lean_nat_dec_lt(v___x_1558_, v___x_1524_);
                                        if v___x_1559_ == 0 {
                                            leanh::lean_dec(v___x_1558_);
                                            v___x_1560_ = leanh::lean_box(0);
                                            leanh::lean_inc(v_idx_1512_);
                                            v_pos_1514_ = v_a_1505_;
                                            v_idx_1515_ = v_idx_1512_;
                                            v_err_1516_ = v___x_1560_;
                                            state = 2;
                                            continue;
                                        } else {
                                            v_c_1561_ =
                                                lean_byte_array_fget(v_array_1511_, v___x_1558_);
                                            v___x_1562_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__11_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__11);
                                            v___x_1563_ = lean_uint8_dec_le(v___x_1562_, v_c_1561_);
                                            if v___x_1563_ == 0 {
                                                leanh::lean_dec(v___x_1558_);
                                                state = 3;
                                                continue;
                                            } else {
                                                v___x_1564_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__12), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__12_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__12);
                                                v___x_1565_ =
                                                    lean_uint8_dec_le(v_c_1561_, v___x_1564_);
                                                if v___x_1565_ == 0 {
                                                    leanh::lean_dec(v___x_1558_);
                                                    state = 3;
                                                    continue;
                                                } else {
                                                    v___x_1566_ =
                                                        lean_nat_add(v___x_1558_, v___x_1531_);
                                                    leanh::lean_dec(v___x_1558_);
                                                    leanh::lean_inc_ref(v_array_1511_);
                                                    v_it_x27_1567_ = leanh::lean_alloc_ctor(
                                                        0,
                                                        2,
                                                        (0) as u32,
                                                    );
                                                    leanh::lean_ctor_set(
                                                        v_it_x27_1567_,
                                                        0,
                                                        v_array_1511_,
                                                    );
                                                    leanh::lean_ctor_set(
                                                        v_it_x27_1567_,
                                                        1,
                                                        v___x_1566_,
                                                    );
                                                    v___x_1568_ = lean_uint8_to_uint32(v_c_1561_);
                                                    v___x_1569_ = lean_uint32_to_uint8(v___x_1568_);
                                                    v___x_1570_ =
                                                        lean_uint8_sub(v___x_1569_, v___x_1562_);
                                                    v___x_1571_ = lean_uint8_to_nat(v___x_1570_);
                                                    v___x_1572_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_1567_, v___x_1571_);
                                                    v_fst_1573_ =
                                                        leanh::lean_ctor_get(v___x_1572_, 0);
                                                    leanh::lean_inc(v_fst_1573_);
                                                    v_snd_1574_ =
                                                        leanh::lean_ctor_get(v___x_1572_, 1);
                                                    leanh::lean_inc(v_snd_1574_);
                                                    leanh::lean_dec_ref(v___x_1572_);
                                                    v___x_1575_ =
                                                        leanh::lean_unsigned_to_nat(0);
                                                    v___x_1576_ =
                                                        lean_nat_dec_eq(v_fst_1573_, v___x_1575_);
                                                    if v___x_1576_ == 0 {
                                                        leanh::lean_dec(v_idx_1512_);
                                                        leanh::lean_dec_ref(v_a_1505_);
                                                        v___x_1577_ = lean_nat_to_int(v_fst_1573_);
                                                        v___x_1578_ = lean_int_neg(v___x_1577_);
                                                        leanh::lean_dec(v___x_1577_);
                                                        v_pos_1507_ = v_snd_1574_;
                                                        v_res_1508_ = v___x_1578_;
                                                        state = 1;
                                                        continue;
                                                    } else {
                                                        leanh::lean_dec(v_snd_1574_);
                                                        leanh::lean_dec(v_fst_1573_);
                                                        v___x_1579_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__14;
                                                        leanh::lean_inc(v_idx_1512_);
                                                        v_pos_1514_ = v_a_1505_;
                                                        v_idx_1515_ = v_idx_1512_;
                                                        v_err_1516_ = v___x_1579_;
                                                        state = 2;
                                                        continue;
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_1509_ = lean_array_push(v_acc_1504_, v_res_1508_);
                v_acc_1504_ = v___x_1509_;
                v_a_1505_ = v_pos_1507_;
                state = 0;
                continue;
            }
            2 => {
                v___x_1517_ = lean_nat_dec_eq(v_idx_1512_, v_idx_1515_);
                leanh::lean_dec(v_idx_1515_);
                leanh::lean_dec(v_idx_1512_);
                if v___x_1517_ == 0 {
                    leanh::lean_dec_ref(v_acc_1504_);
                    leanh::lean_inc(v_err_1516_);
                    v___x_1518_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1518_, 0, v_pos_1514_);
                    leanh::lean_ctor_set(v___x_1518_, 1, v_err_1516_);
                    return v___x_1518_;
                } else {
                    v___x_1519_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1519_, 0, v_pos_1514_);
                    leanh::lean_ctor_set(v___x_1519_, 1, v_acc_1504_);
                    return v___x_1519_;
                }
            }
            3 => {
                v___x_1521_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__9;
                leanh::lean_inc(v_idx_1512_);
                v_pos_1514_ = v_a_1505_;
                v_idx_1515_ = v_idx_1512_;
                v_err_1516_ = v___x_1521_;
                state = 2;
                continue;
            }
            4 => {
                v___x_1523_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__9;
                leanh::lean_inc(v_idx_1512_);
                v_pos_1514_ = v_a_1505_;
                v_idx_1515_ = v_idx_1512_;
                v_err_1516_ = v___x_1523_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__0()
-> u8 {
    let mut v___x_1580_: u32 = 0;
    let mut v___x_1581_: u8 = 0;
    v___x_1580_ = 118;
    v___x_1581_ = lean_uint32_to_uint8(v___x_1580_);
    return v___x_1581_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1582_: u8 = 0;
    let mut v___x_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1582_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__0_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__0);
    v___x_1583_ = lean_uint8_to_nat(v___x_1582_);
    return v___x_1583_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1584_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__1_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__1);
    v___x_1585_ = l_Nat_reprFast(v___x_1584_);
    return v___x_1585_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1586_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__2_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__2);
    v___x_1587_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__1;
    v___x_1588_ = lean_string_append(v___x_1587_, v___x_1586_);
    return v___x_1588_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1589_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__5;
    v___x_1590_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__3_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__3);
    v___x_1591_ = lean_string_append(v___x_1590_, v___x_1589_);
    return v___x_1591_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1592_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__4_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__4);
    v___x_1593_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1593_, 0, v___x_1592_);
    return v___x_1593_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_1597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_utf8_1598_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1597_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__7;
    v_utf8_1598_ = lean_string_to_utf8(v___x_1597_);
    return v_utf8_1598_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_1600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_utf8_1601_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1600_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__9;
    v_utf8_1601_ = lean_string_to_utf8(v___x_1600_);
    return v_utf8_1601_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__11()
-> u8 {
    let mut v___x_1602_: u32 = 0;
    let mut v___x_1603_: u8 = 0;
    v___x_1602_ = 10;
    v___x_1603_ = lean_uint32_to_uint8(v___x_1602_);
    return v___x_1603_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_1604_: u8 = 0;
    let mut v___x_1605_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1604_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__11_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__11);
    v___x_1605_ = lean_uint8_to_nat(v___x_1604_);
    return v___x_1605_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1606_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__12), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__12_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__12);
    v___x_1607_ = l_Nat_reprFast(v___x_1606_);
    return v___x_1607_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__14()
-> *mut leanh::LeanObject {
    let mut v___x_1608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1608_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__13), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__13_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__13);
    v___x_1609_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__1;
    v___x_1610_ = lean_string_append(v___x_1609_, v___x_1608_);
    return v___x_1610_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_1611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1613_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1611_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__5;
    v___x_1612_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__14), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__14_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__14);
    v___x_1613_ = lean_string_append(v___x_1612_, v___x_1611_);
    return v___x_1613_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__16()
-> *mut leanh::LeanObject {
    let mut v___x_1614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1614_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__15), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__15_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__15);
    v___x_1615_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1615_, 0, v___x_1614_);
    return v___x_1615_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment(
    mut v_a_1616_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_array_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: u8 = 0;
    let mut v___x_1621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: u8 = 0;
    let mut v_got_1624_: u8 = 0;
    let mut v___x_1625_: u8 = 0;
    let mut v___x_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1630_: u8 = 0;
    let mut v___x_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1641_: u8 = 0;
    let mut v_sz_1642_: usize = 0;
    let mut v___x_1643_: usize = 0;
    let mut v___x_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: u8 = 0;
    let mut v___x_1655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1665_: u8 = 0;
    let mut v___x_1667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1669_: u8 = 0;
    let mut v_utf8_1670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_1675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1678_: u8 = 0;
    let mut v_idx_1679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_1680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: u8 = 0;
    let mut v_utf8_1687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: u8 = 0;
    let mut v___x_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: u8 = 0;
    let mut v___x_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: u8 = 0;
    let mut v_got_1701_: u8 = 0;
    let mut v___x_1702_: u8 = 0;
    let mut v___x_1703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1709_: u8 = 0;
    let mut v___x_1710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1714_: u8 = 0;
    let mut v_unused_1715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1717_: u8 = 0;
    let mut v_isSharedCheck_1718_: u8 = 0;
    let mut v_pos_1719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1723_: u8 = 0;
    let mut v___x_1725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1727_: u8 = 0;
    let mut v_reuseFailAlloc_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1729_: u8 = 0;
    let mut v_unused_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_1617_ = leanh::lean_ctor_get(v_a_1616_, 0);
                v_idx_1618_ = leanh::lean_ctor_get(v_a_1616_, 1);
                v___x_1619_ = lean_byte_array_size(v_array_1617_);
                v___x_1620_ = lean_nat_dec_lt(v_idx_1618_, v___x_1619_);
                if v___x_1620_ == 0 {
                    v___x_1621_ = leanh::lean_box(0);
                    v___x_1622_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1622_, 0, v_a_1616_);
                    leanh::lean_ctor_set(v___x_1622_, 1, v___x_1621_);
                    return v___x_1622_;
                } else {
                    v___x_1623_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__0_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__0);
                    v_got_1624_ = lean_byte_array_fget(v_array_1617_, v_idx_1618_);
                    v___x_1625_ = lean_uint8_dec_eq(v_got_1624_, v___x_1623_);
                    if v___x_1625_ == 0 {
                        v___x_1626_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__5_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__5);
                        v___x_1627_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1627_, 0, v_a_1616_);
                        leanh::lean_ctor_set(v___x_1627_, 1, v___x_1626_);
                        return v___x_1627_;
                    } else {
                        leanh::lean_inc(v_idx_1618_);
                        leanh::lean_inc_ref(v_array_1617_);
                        v_isSharedCheck_1729_ = (!leanh::lean_is_exclusive(v_a_1616_)) as u8;
                        if v_isSharedCheck_1729_ == 0 {
                            v_unused_1730_ = leanh::lean_ctor_get(v_a_1616_, 1);
                            leanh::lean_dec(v_unused_1730_);
                            v_unused_1731_ = leanh::lean_ctor_get(v_a_1616_, 0);
                            leanh::lean_dec(v_unused_1731_);
                            v___x_1629_ = v_a_1616_;
                            v_isShared_1630_ = v_isSharedCheck_1729_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_a_1616_);
                            v___x_1629_ = leanh::lean_box(0);
                            v_isShared_1630_ = v_isSharedCheck_1729_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1631_ = leanh::lean_unsigned_to_nat(1);
                v___x_1632_ = lean_nat_add(v_idx_1618_, v___x_1631_);
                if v_isShared_1630_ == 0 {
                    leanh::lean_ctor_set(v___x_1629_, 1, v___x_1632_);
                    v___x_1634_ = v___x_1629_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1728_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1728_, 0, v_array_1617_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1728_, 1, v___x_1632_);
                    v___x_1634_ = v_reuseFailAlloc_1728_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1635_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__6;
                v___x_1636_ = l_Std_Internal_Parsec_manyCore___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__1(v___x_1635_, v___x_1634_);
                if leanh::lean_obj_tag(v___x_1636_) == 0 {
                    v_pos_1637_ = leanh::lean_ctor_get(v___x_1636_, 0);
                    v_res_1638_ = leanh::lean_ctor_get(v___x_1636_, 1);
                    v_isSharedCheck_1718_ = (!leanh::lean_is_exclusive(v___x_1636_)) as u8;
                    if v_isSharedCheck_1718_ == 0 {
                        v___x_1640_ = v___x_1636_;
                        v_isShared_1641_ = v_isSharedCheck_1718_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_res_1638_);
                        leanh::lean_inc(v_pos_1637_);
                        leanh::lean_dec(v___x_1636_);
                        v___x_1640_ = leanh::lean_box(0);
                        v_isShared_1641_ = v_isSharedCheck_1718_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_idx_1618_);
                    v_pos_1719_ = leanh::lean_ctor_get(v___x_1636_, 0);
                    v_err_1720_ = leanh::lean_ctor_get(v___x_1636_, 1);
                    v_isSharedCheck_1727_ = (!leanh::lean_is_exclusive(v___x_1636_)) as u8;
                    if v_isSharedCheck_1727_ == 0 {
                        v___x_1722_ = v___x_1636_;
                        v_isShared_1723_ = v_isSharedCheck_1727_;
                        state = 17;
                        continue;
                    } else {
                        leanh::lean_inc(v_err_1720_);
                        leanh::lean_inc(v_pos_1719_);
                        leanh::lean_dec(v___x_1636_);
                        v___x_1722_ = leanh::lean_box(0);
                        v_isShared_1723_ = v_isSharedCheck_1727_;
                        state = 17;
                        continue;
                    }
                }
            }
            3 => {
                v_sz_1642_ = lean_array_size(v_res_1638_);
                v___x_1643_ = 0usize;
                v___x_1644_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__2(v_idx_1618_, v___x_1619_, v_sz_1642_, v___x_1643_, v_res_1638_);
                leanh::lean_dec(v_idx_1618_);
                v_utf8_1670_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__8_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__8);
                leanh::lean_inc(v_pos_1637_);
                v___x_1671_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_1670_, v_pos_1637_);
                if leanh::lean_obj_tag(v___x_1671_) == 0 {
                    leanh::lean_dec(v_pos_1637_);
                    v_pos_1672_ = leanh::lean_ctor_get(v___x_1671_, 0);
                    leanh::lean_inc(v_pos_1672_);
                    leanh::lean_dec_ref_known(v___x_1671_, 2);
                    v_pos_1646_ = v_pos_1672_;
                    state = 4;
                    continue;
                } else {
                    if leanh::lean_obj_tag(v___x_1671_) == 0 {
                        leanh::lean_dec(v_pos_1637_);
                        v_pos_1673_ = leanh::lean_ctor_get(v___x_1671_, 0);
                        leanh::lean_inc(v_pos_1673_);
                        leanh::lean_dec_ref_known(v___x_1671_, 2);
                        v_pos_1646_ = v_pos_1673_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_del_object(v___x_1640_);
                        v_pos_1674_ = leanh::lean_ctor_get(v___x_1671_, 0);
                        v_err_1675_ = leanh::lean_ctor_get(v___x_1671_, 1);
                        v_isSharedCheck_1717_ =
                            (!leanh::lean_is_exclusive(v___x_1671_)) as u8;
                        if v_isSharedCheck_1717_ == 0 {
                            v___x_1677_ = v___x_1671_;
                            v_isShared_1678_ = v_isSharedCheck_1717_;
                            state = 10;
                            continue;
                        } else {
                            leanh::lean_inc(v_err_1675_);
                            leanh::lean_inc(v_pos_1674_);
                            leanh::lean_dec(v___x_1671_);
                            v___x_1677_ = leanh::lean_box(0);
                            v_isShared_1678_ = v_isSharedCheck_1717_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            4 => {
                v___x_1647_ = leanh::lean_box((v___x_1620_) as usize);
                v___x_1648_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1648_, 0, v___x_1647_);
                leanh::lean_ctor_set(v___x_1648_, 1, v___x_1644_);
                if v_isShared_1641_ == 0 {
                    leanh::lean_ctor_set(v___x_1640_, 1, v___x_1648_);
                    leanh::lean_ctor_set(v___x_1640_, 0, v_pos_1646_);
                    v___x_1650_ = v___x_1640_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1651_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1651_, 0, v_pos_1646_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1651_, 1, v___x_1648_);
                    v___x_1650_ = v_reuseFailAlloc_1651_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1650_;
            }
            6 => {
                v___x_1654_ = 0;
                v___x_1655_ = leanh::lean_box((v___x_1654_) as usize);
                v___x_1656_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1656_, 0, v___x_1655_);
                leanh::lean_ctor_set(v___x_1656_, 1, v___x_1644_);
                v___x_1657_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1657_, 0, v_pos_1653_);
                leanh::lean_ctor_set(v___x_1657_, 1, v___x_1656_);
                return v___x_1657_;
            }
            7 => {
                if leanh::lean_obj_tag(v___y_1659_) == 0 {
                    v_pos_1660_ = leanh::lean_ctor_get(v___y_1659_, 0);
                    leanh::lean_inc(v_pos_1660_);
                    leanh::lean_dec_ref_known(v___y_1659_, 2);
                    v_pos_1653_ = v_pos_1660_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_dec_ref(v___x_1644_);
                    v_pos_1661_ = leanh::lean_ctor_get(v___y_1659_, 0);
                    v_err_1662_ = leanh::lean_ctor_get(v___y_1659_, 1);
                    v_isSharedCheck_1669_ = (!leanh::lean_is_exclusive(v___y_1659_)) as u8;
                    if v_isSharedCheck_1669_ == 0 {
                        v___x_1664_ = v___y_1659_;
                        v_isShared_1665_ = v_isSharedCheck_1669_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_err_1662_);
                        leanh::lean_inc(v_pos_1661_);
                        leanh::lean_dec(v___y_1659_);
                        v___x_1664_ = leanh::lean_box(0);
                        v_isShared_1665_ = v_isSharedCheck_1669_;
                        state = 8;
                        continue;
                    }
                }
            }
            8 => {
                if v_isShared_1665_ == 0 {
                    v___x_1667_ = v___x_1664_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1668_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_pos_1661_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1668_, 1, v_err_1662_);
                    v___x_1667_ = v_reuseFailAlloc_1668_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1667_;
            }
            10 => {
                v_idx_1679_ = leanh::lean_ctor_get(v_pos_1637_, 1);
                leanh::lean_inc(v_idx_1679_);
                leanh::lean_dec(v_pos_1637_);
                v_array_1680_ = leanh::lean_ctor_get(v_pos_1674_, 0);
                v_idx_1681_ = leanh::lean_ctor_get(v_pos_1674_, 1);
                v___x_1690_ = lean_nat_dec_eq(v_idx_1679_, v_idx_1681_);
                leanh::lean_dec(v_idx_1679_);
                if v___x_1690_ == 0 {
                    leanh::lean_dec_ref(v___x_1644_);
                    if v_isShared_1678_ == 0 {
                        v___x_1692_ = v___x_1677_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_1693_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1693_, 0, v_pos_1674_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1693_, 1, v_err_1675_);
                        v___x_1692_ = v_reuseFailAlloc_1693_;
                        state = 12;
                        continue;
                    }
                } else {
                    leanh::lean_inc(v_idx_1681_);
                    leanh::lean_dec(v_err_1675_);
                    v___x_1694_ = lean_byte_array_size(v_array_1680_);
                    v___x_1695_ = lean_nat_dec_lt(v_idx_1681_, v___x_1694_);
                    if v___x_1695_ == 0 {
                        v___x_1696_ = leanh::lean_box(0);
                        leanh::lean_inc(v_pos_1674_);
                        if v_isShared_1678_ == 0 {
                            leanh::lean_ctor_set(v___x_1677_, 1, v___x_1696_);
                            v___x_1698_ = v___x_1677_;
                            state = 13;
                            continue;
                        } else {
                            v_reuseFailAlloc_1699_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1699_, 0, v_pos_1674_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1699_, 1, v___x_1696_);
                            v___x_1698_ = v_reuseFailAlloc_1699_;
                            state = 13;
                            continue;
                        }
                    } else {
                        v___x_1700_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__11_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__11);
                        v_got_1701_ = lean_byte_array_fget(v_array_1680_, v_idx_1681_);
                        v___x_1702_ = lean_uint8_dec_eq(v_got_1701_, v___x_1700_);
                        if v___x_1702_ == 0 {
                            v___x_1703_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__16), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__16_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__16);
                            leanh::lean_inc(v_pos_1674_);
                            if v_isShared_1678_ == 0 {
                                leanh::lean_ctor_set(v___x_1677_, 1, v___x_1703_);
                                v___x_1705_ = v___x_1677_;
                                state = 14;
                                continue;
                            } else {
                                v_reuseFailAlloc_1706_ =
                                    leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_1706_, 0, v_pos_1674_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_1706_, 1, v___x_1703_);
                                v___x_1705_ = v_reuseFailAlloc_1706_;
                                state = 14;
                                continue;
                            }
                        } else {
                            leanh::lean_inc_ref(v_array_1680_);
                            leanh::lean_del_object(v___x_1677_);
                            v_isSharedCheck_1714_ =
                                (!leanh::lean_is_exclusive(v_pos_1674_)) as u8;
                            if v_isSharedCheck_1714_ == 0 {
                                v_unused_1715_ = leanh::lean_ctor_get(v_pos_1674_, 1);
                                leanh::lean_dec(v_unused_1715_);
                                v_unused_1716_ = leanh::lean_ctor_get(v_pos_1674_, 0);
                                leanh::lean_dec(v_unused_1716_);
                                v___x_1708_ = v_pos_1674_;
                                v_isShared_1709_ = v_isSharedCheck_1714_;
                                state = 15;
                                continue;
                            } else {
                                leanh::lean_dec(v_pos_1674_);
                                v___x_1708_ = leanh::lean_box(0);
                                v_isShared_1709_ = v_isSharedCheck_1714_;
                                state = 15;
                                continue;
                            }
                        }
                    }
                }
            }
            11 => {
                v___x_1686_ = lean_nat_dec_eq(v_idx_1681_, v_idx_1685_);
                leanh::lean_dec(v_idx_1685_);
                leanh::lean_dec(v_idx_1681_);
                if v___x_1686_ == 0 {
                    leanh::lean_dec_ref(v_pos_1684_);
                    v___y_1659_ = v___y_1683_;
                    state = 7;
                    continue;
                } else {
                    leanh::lean_dec_ref(v___y_1683_);
                    v_utf8_1687_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__10_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__10);
                    v___x_1688_ =
                        l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_1687_, v_pos_1684_);
                    if leanh::lean_obj_tag(v___x_1688_) == 0 {
                        v_pos_1689_ = leanh::lean_ctor_get(v___x_1688_, 0);
                        leanh::lean_inc(v_pos_1689_);
                        leanh::lean_dec_ref_known(v___x_1688_, 2);
                        v_pos_1653_ = v_pos_1689_;
                        state = 6;
                        continue;
                    } else {
                        v___y_1659_ = v___x_1688_;
                        state = 7;
                        continue;
                    }
                }
            }
            12 => {
                return v___x_1692_;
            }
            13 => {
                leanh::lean_inc(v_idx_1681_);
                v___y_1683_ = v___x_1698_;
                v_pos_1684_ = v_pos_1674_;
                v_idx_1685_ = v_idx_1681_;
                state = 11;
                continue;
            }
            14 => {
                leanh::lean_inc(v_idx_1681_);
                v___y_1683_ = v___x_1705_;
                v_pos_1684_ = v_pos_1674_;
                v_idx_1685_ = v_idx_1681_;
                state = 11;
                continue;
            }
            15 => {
                v___x_1710_ = lean_nat_add(v_idx_1681_, v___x_1631_);
                leanh::lean_dec(v_idx_1681_);
                if v_isShared_1709_ == 0 {
                    leanh::lean_ctor_set(v___x_1708_, 1, v___x_1710_);
                    v___x_1712_ = v___x_1708_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1713_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1713_, 0, v_array_1680_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1713_, 1, v___x_1710_);
                    v___x_1712_ = v_reuseFailAlloc_1713_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v_pos_1653_ = v___x_1712_;
                state = 6;
                continue;
            }
            17 => {
                if v_isShared_1723_ == 0 {
                    v___x_1725_ = v___x_1722_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_1726_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1726_, 0, v_pos_1719_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1726_, 1, v_err_1720_);
                    v___x_1725_ = v_reuseFailAlloc_1726_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_1725_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseLines_go(
    mut v_acc_1732_: *mut leanh::LeanObject,
    mut v_a_1733_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_1735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1739_: u8 = 0;
    let mut v_fst_1740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: u8 = 0;
    let mut v___x_1746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1748_: u8 = 0;
    let mut v_pos_1749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_1750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1753_: u8 = 0;
    let mut v___x_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1757_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1734_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment(v_a_1733_);
                if leanh::lean_obj_tag(v___x_1734_) == 0 {
                    v_res_1735_ = leanh::lean_ctor_get(v___x_1734_, 1);
                    v_pos_1736_ = leanh::lean_ctor_get(v___x_1734_, 0);
                    v_isSharedCheck_1748_ = (!leanh::lean_is_exclusive(v___x_1734_)) as u8;
                    if v_isSharedCheck_1748_ == 0 {
                        v___x_1738_ = v___x_1734_;
                        v_isShared_1739_ = v_isSharedCheck_1748_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_res_1735_);
                        leanh::lean_inc(v_pos_1736_);
                        leanh::lean_dec(v___x_1734_);
                        v___x_1738_ = leanh::lean_box(0);
                        v_isShared_1739_ = v_isSharedCheck_1748_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_acc_1732_);
                    v_pos_1749_ = leanh::lean_ctor_get(v___x_1734_, 0);
                    v_err_1750_ = leanh::lean_ctor_get(v___x_1734_, 1);
                    v_isSharedCheck_1757_ = (!leanh::lean_is_exclusive(v___x_1734_)) as u8;
                    if v_isSharedCheck_1757_ == 0 {
                        v___x_1752_ = v___x_1734_;
                        v_isShared_1753_ = v_isSharedCheck_1757_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_err_1750_);
                        leanh::lean_inc(v_pos_1749_);
                        leanh::lean_dec(v___x_1734_);
                        v___x_1752_ = leanh::lean_box(0);
                        v_isShared_1753_ = v_isSharedCheck_1757_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1740_ = leanh::lean_ctor_get(v_res_1735_, 0);
                leanh::lean_inc(v_fst_1740_);
                v_snd_1741_ = leanh::lean_ctor_get(v_res_1735_, 1);
                leanh::lean_inc(v_snd_1741_);
                leanh::lean_dec(v_res_1735_);
                v___x_1742_ = l_Array_append___redArg(v_acc_1732_, v_snd_1741_);
                leanh::lean_dec(v_snd_1741_);
                v___x_1743_ = (leanh::lean_unbox(v_fst_1740_) as u8);
                leanh::lean_dec(v_fst_1740_);
                if v___x_1743_ == 0 {
                    leanh::lean_del_object(v___x_1738_);
                    v_acc_1732_ = v___x_1742_;
                    v_a_1733_ = v_pos_1736_;
                    state = 0;
                    continue;
                } else {
                    if v_isShared_1739_ == 0 {
                        leanh::lean_ctor_set(v___x_1738_, 1, v___x_1742_);
                        v___x_1746_ = v___x_1738_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1747_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1747_, 0, v_pos_1736_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1747_, 1, v___x_1742_);
                        v___x_1746_ = v_reuseFailAlloc_1747_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1746_;
            }
            3 => {
                if v_isShared_1753_ == 0 {
                    v___x_1755_ = v___x_1752_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1756_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1756_, 0, v_pos_1749_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1756_, 1, v_err_1750_);
                    v___x_1755_ = v_reuseFailAlloc_1756_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1755_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseLines(
    mut v_a_1760_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1761_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseLines___closed__0;
    v___x_1762_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseLines_go(v___x_1761_, v_a_1760_);
    return v___x_1762_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseHeader___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_utf8_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1764_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseHeader___closed__0;
    v_utf8_1765_ = lean_string_to_utf8(v___x_1764_);
    return v_utf8_1765_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseHeader(
    mut v_a_1766_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_idx_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: u8 = 0;
    let mut v_utf8_1773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1778_: u8 = 0;
    let mut v___x_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1783_: u8 = 0;
    let mut v_unused_1784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: u8 = 0;
    let mut v___x_1791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: u8 = 0;
    let mut v_got_1794_: u8 = 0;
    let mut v___x_1795_: u8 = 0;
    let mut v___x_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1800_: u8 = 0;
    let mut v___x_1801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1808_: u8 = 0;
    let mut v_unused_1809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_utf8_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_utf8_1811_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseHeader___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseHeader___closed__1_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseHeader___closed__1);
                v___x_1812_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_1811_, v_a_1766_);
                if leanh::lean_obj_tag(v___x_1812_) == 0 {
                    v_pos_1813_ = leanh::lean_ctor_get(v___x_1812_, 0);
                    leanh::lean_inc(v_pos_1813_);
                    leanh::lean_dec_ref_known(v___x_1812_, 2);
                    v_pos_1786_ = v_pos_1813_;
                    state = 4;
                    continue;
                } else {
                    if leanh::lean_obj_tag(v___x_1812_) == 0 {
                        v_pos_1814_ = leanh::lean_ctor_get(v___x_1812_, 0);
                        leanh::lean_inc(v_pos_1814_);
                        leanh::lean_dec_ref_known(v___x_1812_, 2);
                        v_pos_1786_ = v_pos_1814_;
                        state = 4;
                        continue;
                    } else {
                        return v___x_1812_;
                    }
                }
            }
            1 => {
                v___x_1772_ = lean_nat_dec_eq(v_idx_1768_, v_idx_1771_);
                leanh::lean_dec(v_idx_1771_);
                leanh::lean_dec(v_idx_1768_);
                if v___x_1772_ == 0 {
                    leanh::lean_dec_ref(v_pos_1770_);
                    return v___y_1769_;
                } else {
                    leanh::lean_dec_ref(v___y_1769_);
                    v_utf8_1773_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__10_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__10);
                    v___x_1774_ =
                        l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_1773_, v_pos_1770_);
                    if leanh::lean_obj_tag(v___x_1774_) == 0 {
                        v_pos_1775_ = leanh::lean_ctor_get(v___x_1774_, 0);
                        v_isSharedCheck_1783_ =
                            (!leanh::lean_is_exclusive(v___x_1774_)) as u8;
                        if v_isSharedCheck_1783_ == 0 {
                            v_unused_1784_ = leanh::lean_ctor_get(v___x_1774_, 1);
                            leanh::lean_dec(v_unused_1784_);
                            v___x_1777_ = v___x_1774_;
                            v_isShared_1778_ = v_isSharedCheck_1783_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_pos_1775_);
                            leanh::lean_dec(v___x_1774_);
                            v___x_1777_ = leanh::lean_box(0);
                            v_isShared_1778_ = v_isSharedCheck_1783_;
                            state = 2;
                            continue;
                        }
                    } else {
                        return v___x_1774_;
                    }
                }
            }
            2 => {
                v___x_1779_ = leanh::lean_box(0);
                if v_isShared_1778_ == 0 {
                    leanh::lean_ctor_set(v___x_1777_, 1, v___x_1779_);
                    v___x_1781_ = v___x_1777_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1782_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1782_, 0, v_pos_1775_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1782_, 1, v___x_1779_);
                    v___x_1781_ = v_reuseFailAlloc_1782_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1781_;
            }
            4 => {
                v_array_1787_ = leanh::lean_ctor_get(v_pos_1786_, 0);
                v_idx_1788_ = leanh::lean_ctor_get(v_pos_1786_, 1);
                leanh::lean_inc(v_idx_1788_);
                v___x_1789_ = lean_byte_array_size(v_array_1787_);
                v___x_1790_ = lean_nat_dec_lt(v_idx_1788_, v___x_1789_);
                if v___x_1790_ == 0 {
                    v___x_1791_ = leanh::lean_box(0);
                    leanh::lean_inc_ref(v_pos_1786_);
                    v___x_1792_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1792_, 0, v_pos_1786_);
                    leanh::lean_ctor_set(v___x_1792_, 1, v___x_1791_);
                    leanh::lean_inc(v_idx_1788_);
                    v_idx_1768_ = v_idx_1788_;
                    v___y_1769_ = v___x_1792_;
                    v_pos_1770_ = v_pos_1786_;
                    v_idx_1771_ = v_idx_1788_;
                    state = 1;
                    continue;
                } else {
                    v___x_1793_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__11_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__11);
                    v_got_1794_ = lean_byte_array_fget(v_array_1787_, v_idx_1788_);
                    v___x_1795_ = lean_uint8_dec_eq(v_got_1794_, v___x_1793_);
                    if v___x_1795_ == 0 {
                        v___x_1796_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__16), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__16_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__16);
                        leanh::lean_inc_ref(v_pos_1786_);
                        v___x_1797_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1797_, 0, v_pos_1786_);
                        leanh::lean_ctor_set(v___x_1797_, 1, v___x_1796_);
                        leanh::lean_inc(v_idx_1788_);
                        v_idx_1768_ = v_idx_1788_;
                        v___y_1769_ = v___x_1797_;
                        v_pos_1770_ = v_pos_1786_;
                        v_idx_1771_ = v_idx_1788_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc_ref(v_array_1787_);
                        v_isSharedCheck_1808_ =
                            (!leanh::lean_is_exclusive(v_pos_1786_)) as u8;
                        if v_isSharedCheck_1808_ == 0 {
                            v_unused_1809_ = leanh::lean_ctor_get(v_pos_1786_, 1);
                            leanh::lean_dec(v_unused_1809_);
                            v_unused_1810_ = leanh::lean_ctor_get(v_pos_1786_, 0);
                            leanh::lean_dec(v_unused_1810_);
                            v___x_1799_ = v_pos_1786_;
                            v_isShared_1800_ = v_isSharedCheck_1808_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_dec(v_pos_1786_);
                            v___x_1799_ = leanh::lean_box(0);
                            v_isShared_1800_ = v_isSharedCheck_1808_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            5 => {
                v___x_1801_ = leanh::lean_unsigned_to_nat(1);
                v___x_1802_ = lean_nat_add(v_idx_1788_, v___x_1801_);
                leanh::lean_dec(v_idx_1788_);
                if v_isShared_1800_ == 0 {
                    leanh::lean_ctor_set(v___x_1799_, 1, v___x_1802_);
                    v___x_1804_ = v___x_1799_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1807_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1807_, 0, v_array_1787_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1807_, 1, v___x_1802_);
                    v___x_1804_ = v_reuseFailAlloc_1807_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_1805_ = leanh::lean_box(0);
                v___x_1806_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1806_, 0, v___x_1804_);
                leanh::lean_ctor_set(v___x_1806_, 1, v___x_1805_);
                return v___x_1806_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parse(
    mut v_a_1815_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1824_: u8 = 0;
    let mut v___x_1826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1828_: u8 = 0;
    let mut v_idx_1830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: u8 = 0;
    let mut v_utf8_1835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_1841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: u8 = 0;
    let mut v___x_1845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: u8 = 0;
    let mut v_got_1848_: u8 = 0;
    let mut v___x_1849_: u8 = 0;
    let mut v___x_1850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1854_: u8 = 0;
    let mut v___x_1855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1861_: u8 = 0;
    let mut v_unused_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_utf8_1864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_utf8_1864_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseHeader___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseHeader___closed__1_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseHeader___closed__1);
                v___x_1865_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_1864_, v_a_1815_);
                if leanh::lean_obj_tag(v___x_1865_) == 0 {
                    v_pos_1866_ = leanh::lean_ctor_get(v___x_1865_, 0);
                    leanh::lean_inc(v_pos_1866_);
                    leanh::lean_dec_ref_known(v___x_1865_, 2);
                    v_pos_1840_ = v_pos_1866_;
                    state = 5;
                    continue;
                } else {
                    if leanh::lean_obj_tag(v___x_1865_) == 0 {
                        v_pos_1867_ = leanh::lean_ctor_get(v___x_1865_, 0);
                        leanh::lean_inc(v_pos_1867_);
                        leanh::lean_dec_ref_known(v___x_1865_, 2);
                        v_pos_1840_ = v_pos_1867_;
                        state = 5;
                        continue;
                    } else {
                        v___y_1817_ = v___x_1865_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v___y_1817_) == 0 {
                    v_pos_1818_ = leanh::lean_ctor_get(v___y_1817_, 0);
                    leanh::lean_inc(v_pos_1818_);
                    leanh::lean_dec_ref_known(v___y_1817_, 2);
                    v___x_1819_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseLines(v_pos_1818_);
                    return v___x_1819_;
                } else {
                    v_pos_1820_ = leanh::lean_ctor_get(v___y_1817_, 0);
                    v_err_1821_ = leanh::lean_ctor_get(v___y_1817_, 1);
                    v_isSharedCheck_1828_ = (!leanh::lean_is_exclusive(v___y_1817_)) as u8;
                    if v_isSharedCheck_1828_ == 0 {
                        v___x_1823_ = v___y_1817_;
                        v_isShared_1824_ = v_isSharedCheck_1828_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_err_1821_);
                        leanh::lean_inc(v_pos_1820_);
                        leanh::lean_dec(v___y_1817_);
                        v___x_1823_ = leanh::lean_box(0);
                        v_isShared_1824_ = v_isSharedCheck_1828_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1824_ == 0 {
                    v___x_1826_ = v___x_1823_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1827_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_pos_1820_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1827_, 1, v_err_1821_);
                    v___x_1826_ = v_reuseFailAlloc_1827_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1826_;
            }
            4 => {
                v___x_1834_ = lean_nat_dec_eq(v_idx_1830_, v_idx_1833_);
                leanh::lean_dec(v_idx_1833_);
                leanh::lean_dec(v_idx_1830_);
                if v___x_1834_ == 0 {
                    leanh::lean_dec_ref(v_pos_1832_);
                    v___y_1817_ = v___y_1831_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec_ref(v___y_1831_);
                    v_utf8_1835_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__10_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__10);
                    v___x_1836_ =
                        l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_1835_, v_pos_1832_);
                    if leanh::lean_obj_tag(v___x_1836_) == 0 {
                        v_pos_1837_ = leanh::lean_ctor_get(v___x_1836_, 0);
                        leanh::lean_inc(v_pos_1837_);
                        leanh::lean_dec_ref_known(v___x_1836_, 2);
                        v___x_1838_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseLines(v_pos_1837_);
                        return v___x_1838_;
                    } else {
                        v___y_1817_ = v___x_1836_;
                        state = 1;
                        continue;
                    }
                }
            }
            5 => {
                v_array_1841_ = leanh::lean_ctor_get(v_pos_1840_, 0);
                v_idx_1842_ = leanh::lean_ctor_get(v_pos_1840_, 1);
                leanh::lean_inc(v_idx_1842_);
                v___x_1843_ = lean_byte_array_size(v_array_1841_);
                v___x_1844_ = lean_nat_dec_lt(v_idx_1842_, v___x_1843_);
                if v___x_1844_ == 0 {
                    v___x_1845_ = leanh::lean_box(0);
                    leanh::lean_inc_ref(v_pos_1840_);
                    v___x_1846_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1846_, 0, v_pos_1840_);
                    leanh::lean_ctor_set(v___x_1846_, 1, v___x_1845_);
                    leanh::lean_inc(v_idx_1842_);
                    v_idx_1830_ = v_idx_1842_;
                    v___y_1831_ = v___x_1846_;
                    v_pos_1832_ = v_pos_1840_;
                    v_idx_1833_ = v_idx_1842_;
                    state = 4;
                    continue;
                } else {
                    v___x_1847_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__11_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__11);
                    v_got_1848_ = lean_byte_array_fget(v_array_1841_, v_idx_1842_);
                    v___x_1849_ = lean_uint8_dec_eq(v_got_1848_, v___x_1847_);
                    if v___x_1849_ == 0 {
                        v___x_1850_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__16), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__16_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__16);
                        leanh::lean_inc_ref(v_pos_1840_);
                        v___x_1851_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1851_, 0, v_pos_1840_);
                        leanh::lean_ctor_set(v___x_1851_, 1, v___x_1850_);
                        leanh::lean_inc(v_idx_1842_);
                        v_idx_1830_ = v_idx_1842_;
                        v___y_1831_ = v___x_1851_;
                        v_pos_1832_ = v_pos_1840_;
                        v_idx_1833_ = v_idx_1842_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc_ref(v_array_1841_);
                        v_isSharedCheck_1861_ =
                            (!leanh::lean_is_exclusive(v_pos_1840_)) as u8;
                        if v_isSharedCheck_1861_ == 0 {
                            v_unused_1862_ = leanh::lean_ctor_get(v_pos_1840_, 1);
                            leanh::lean_dec(v_unused_1862_);
                            v_unused_1863_ = leanh::lean_ctor_get(v_pos_1840_, 0);
                            leanh::lean_dec(v_unused_1863_);
                            v___x_1853_ = v_pos_1840_;
                            v_isShared_1854_ = v_isSharedCheck_1861_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_dec(v_pos_1840_);
                            v___x_1853_ = leanh::lean_box(0);
                            v_isShared_1854_ = v_isSharedCheck_1861_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            6 => {
                v___x_1855_ = leanh::lean_unsigned_to_nat(1);
                v___x_1856_ = lean_nat_add(v_idx_1842_, v___x_1855_);
                leanh::lean_dec(v_idx_1842_);
                if v_isShared_1854_ == 0 {
                    leanh::lean_ctor_set(v___x_1853_, 1, v___x_1856_);
                    v___x_1858_ = v___x_1853_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1860_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1860_, 0, v_array_1841_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1860_, 1, v___x_1856_);
                    v___x_1858_ = v_reuseFailAlloc_1860_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_1859_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseLines(v___x_1858_);
                return v___x_1859_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorIdx___redArg(
    mut v_x_1868_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1868_) == 0 {
        let mut v___x_1869_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1869_ = leanh::lean_unsigned_to_nat(0);
        return v___x_1869_;
    } else {
        let mut v___x_1870_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1870_ = leanh::lean_unsigned_to_nat(1);
        return v___x_1870_;
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorIdx___redArg___boxed(
    mut v_x_1871_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1872_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1872_ = l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorIdx___redArg(v_x_1871_);
    leanh::lean_dec(v_x_1871_);
    return v_res_1872_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorIdx(
    mut v_00_u03b1_1873_: *mut leanh::LeanObject,
    mut v_x_1874_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1875_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1875_ = l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorIdx___redArg(v_x_1874_);
    return v___x_1875_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorIdx___boxed(
    mut v_00_u03b1_1876_: *mut leanh::LeanObject,
    mut v_x_1877_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1878_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1878_ =
        l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorIdx(v_00_u03b1_1876_, v_x_1877_);
    leanh::lean_dec(v_x_1877_);
    return v_res_1878_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorElim___redArg(
    mut v_t_1879_: *mut leanh::LeanObject,
    mut v_k_1880_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_t_1879_) == 0 {
        let mut v_x_1881_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1882_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_x_1881_ = leanh::lean_ctor_get(v_t_1879_, 0);
        leanh::lean_inc(v_x_1881_);
        leanh::lean_dec_ref_known(v_t_1879_, 1);
        v___x_1882_ = leanh::lean_apply_1(v_k_1880_, v_x_1881_);
        return v___x_1882_;
    } else {
        return v_k_1880_;
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorElim(
    mut v_00_u03b1_1883_: *mut leanh::LeanObject,
    mut v_motive_1884_: *mut leanh::LeanObject,
    mut v_ctorIdx_1885_: *mut leanh::LeanObject,
    mut v_t_1886_: *mut leanh::LeanObject,
    mut v_h_1887_: *mut leanh::LeanObject,
    mut v_k_1888_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1889_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1889_ =
        l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorElim___redArg(v_t_1886_, v_k_1888_);
    return v___x_1889_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorElim___boxed(
    mut v_00_u03b1_1890_: *mut leanh::LeanObject,
    mut v_motive_1891_: *mut leanh::LeanObject,
    mut v_ctorIdx_1892_: *mut leanh::LeanObject,
    mut v_t_1893_: *mut leanh::LeanObject,
    mut v_h_1894_: *mut leanh::LeanObject,
    mut v_k_1895_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1896_ = l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorElim(
        v_00_u03b1_1890_,
        v_motive_1891_,
        v_ctorIdx_1892_,
        v_t_1893_,
        v_h_1894_,
        v_k_1895_,
    );
    leanh::lean_dec(v_ctorIdx_1892_);
    return v_res_1896_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_External_TimedOut_success_elim___redArg(
    mut v_t_1897_: *mut leanh::LeanObject,
    mut v_success_1898_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1899_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1899_ =
        l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorElim___redArg(v_t_1897_, v_success_1898_);
    return v___x_1899_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_External_TimedOut_success_elim(
    mut v_00_u03b1_1900_: *mut leanh::LeanObject,
    mut v_motive_1901_: *mut leanh::LeanObject,
    mut v_t_1902_: *mut leanh::LeanObject,
    mut v_h_1903_: *mut leanh::LeanObject,
    mut v_success_1904_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1905_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1905_ =
        l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorElim___redArg(v_t_1902_, v_success_1904_);
    return v___x_1905_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_External_TimedOut_timeout_elim___redArg(
    mut v_t_1906_: *mut leanh::LeanObject,
    mut v_timeout_1907_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1908_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1908_ =
        l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorElim___redArg(v_t_1906_, v_timeout_1907_);
    return v___x_1908_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_External_TimedOut_timeout_elim(
    mut v_00_u03b1_1909_: *mut leanh::LeanObject,
    mut v_motive_1910_: *mut leanh::LeanObject,
    mut v_t_1911_: *mut leanh::LeanObject,
    mut v_h_1912_: *mut leanh::LeanObject,
    mut v_timeout_1913_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1914_ =
        l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorElim___redArg(v_t_1911_, v_timeout_1913_);
    return v___x_1914_;
}
pub unsafe fn _init_l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1915_ = leanh::lean_box(0);
    v___x_1916_ = l_Lean_interruptExceptionId;
    v___x_1917_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1917_, 0, v___x_1916_);
    leanh::lean_ctor_set(v___x_1917_, 1, v___x_1915_);
    return v___x_1917_;
}
pub unsafe fn l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0___redArg()
-> *mut leanh::LeanObject {
    let mut v___x_1919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1920_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1919_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0___redArg___closed__0_once), _init_l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0___redArg___closed__0);
    v___x_1920_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1920_, 0, v___x_1919_);
    return v___x_1920_;
}
pub unsafe fn l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0___redArg___boxed(
    mut v___y_1921_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1922_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1922_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0___redArg();
    return v_res_1922_;
}
pub unsafe fn l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0(
    mut v_00_u03b1_1923_: *mut leanh::LeanObject,
    mut v___y_1924_: *mut leanh::LeanObject,
    mut v___y_1925_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1927_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1927_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0___redArg();
    return v___x_1927_;
}
pub unsafe fn l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0___boxed(
    mut v_00_u03b1_1928_: *mut leanh::LeanObject,
    mut v___y_1929_: *mut leanh::LeanObject,
    mut v___y_1930_: *mut leanh::LeanObject,
    mut v___y_1931_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1932_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1932_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0(v_00_u03b1_1928_, v___y_1929_, v___y_1930_);
    leanh::lean_dec(v___y_1930_);
    leanh::lean_dec_ref(v___y_1929_);
    return v_res_1932_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck___redArg(
    mut v_cleanup_1933_: *mut leanh::LeanObject,
    mut v_x_1934_: *mut leanh::LeanObject,
    mut v_a_1935_: *mut leanh::LeanObject,
    mut v_a_1936_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cancelTk_x3f_1938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: u8 = 0;
    let mut v___x_1941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1947_: u8 = 0;
    let mut v___x_1949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1951_: u8 = 0;
    let mut v_a_1952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1955_: u8 = 0;
    let mut v___x_1957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1959_: u8 = 0;
    let mut v___x_1960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_cancelTk_x3f_1938_ = leanh::lean_ctor_get(v_a_1935_, 12);
                if leanh::lean_obj_tag(v_cancelTk_x3f_1938_) == 1 {
                    v_val_1939_ = leanh::lean_ctor_get(v_cancelTk_x3f_1938_, 0);
                    v___x_1940_ = l_IO_CancelToken_isSet(v_val_1939_);
                    if v___x_1940_ == 0 {
                        leanh::lean_dec_ref(v_cleanup_1933_);
                        leanh::lean_inc(v_a_1936_);
                        leanh::lean_inc_ref(v_a_1935_);
                        v___x_1941_ = leanh::lean_apply_3(
                            v_x_1934_,
                            v_a_1935_,
                            v_a_1936_,
                            leanh::lean_box(0),
                        );
                        return v___x_1941_;
                    } else {
                        leanh::lean_dec_ref(v_x_1934_);
                        leanh::lean_inc(v_a_1936_);
                        leanh::lean_inc_ref(v_a_1935_);
                        v___x_1942_ = leanh::lean_apply_3(
                            v_cleanup_1933_,
                            v_a_1935_,
                            v_a_1936_,
                            leanh::lean_box(0),
                        );
                        if leanh::lean_obj_tag(v___x_1942_) == 0 {
                            leanh::lean_dec_ref_known(v___x_1942_, 1);
                            v___x_1943_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0___redArg();
                            v_a_1944_ = leanh::lean_ctor_get(v___x_1943_, 0);
                            v_isSharedCheck_1951_ =
                                (!leanh::lean_is_exclusive(v___x_1943_)) as u8;
                            if v_isSharedCheck_1951_ == 0 {
                                v___x_1946_ = v___x_1943_;
                                v_isShared_1947_ = v_isSharedCheck_1951_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1944_);
                                leanh::lean_dec(v___x_1943_);
                                v___x_1946_ = leanh::lean_box(0);
                                v_isShared_1947_ = v_isSharedCheck_1951_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_1952_ = leanh::lean_ctor_get(v___x_1942_, 0);
                            v_isSharedCheck_1959_ =
                                (!leanh::lean_is_exclusive(v___x_1942_)) as u8;
                            if v_isSharedCheck_1959_ == 0 {
                                v___x_1954_ = v___x_1942_;
                                v_isShared_1955_ = v_isSharedCheck_1959_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1952_);
                                leanh::lean_dec(v___x_1942_);
                                v___x_1954_ = leanh::lean_box(0);
                                v_isShared_1955_ = v_isSharedCheck_1959_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_cleanup_1933_);
                    leanh::lean_inc(v_a_1936_);
                    leanh::lean_inc_ref(v_a_1935_);
                    v___x_1960_ = leanh::lean_apply_3(
                        v_x_1934_,
                        v_a_1935_,
                        v_a_1936_,
                        leanh::lean_box(0),
                    );
                    return v___x_1960_;
                }
            }
            1 => {
                if v_isShared_1947_ == 0 {
                    v___x_1949_ = v___x_1946_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1950_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1950_, 0, v_a_1944_);
                    v___x_1949_ = v_reuseFailAlloc_1950_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1949_;
            }
            3 => {
                if v_isShared_1955_ == 0 {
                    v___x_1957_ = v___x_1954_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1958_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_a_1952_);
                    v___x_1957_ = v_reuseFailAlloc_1958_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1957_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck___redArg___boxed(
    mut v_cleanup_1961_: *mut leanh::LeanObject,
    mut v_x_1962_: *mut leanh::LeanObject,
    mut v_a_1963_: *mut leanh::LeanObject,
    mut v_a_1964_: *mut leanh::LeanObject,
    mut v_a_1965_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1966_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck___redArg(v_cleanup_1961_, v_x_1962_, v_a_1963_, v_a_1964_);
    leanh::lean_dec(v_a_1964_);
    leanh::lean_dec_ref(v_a_1963_);
    return v_res_1966_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck(
    mut v_00_u03b1_1967_: *mut leanh::LeanObject,
    mut v_cleanup_1968_: *mut leanh::LeanObject,
    mut v_x_1969_: *mut leanh::LeanObject,
    mut v_a_1970_: *mut leanh::LeanObject,
    mut v_a_1971_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1973_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1973_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck___redArg(v_cleanup_1968_, v_x_1969_, v_a_1970_, v_a_1971_);
    return v___x_1973_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck___boxed(
    mut v_00_u03b1_1974_: *mut leanh::LeanObject,
    mut v_cleanup_1975_: *mut leanh::LeanObject,
    mut v_x_1976_: *mut leanh::LeanObject,
    mut v_a_1977_: *mut leanh::LeanObject,
    mut v_a_1978_: *mut leanh::LeanObject,
    mut v_a_1979_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1980_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1980_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck(v_00_u03b1_1974_, v_cleanup_1975_, v_x_1976_, v_a_1977_, v_a_1978_);
    leanh::lean_dec(v_a_1978_);
    leanh::lean_dec_ref(v_a_1977_);
    return v_res_1980_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withTimeoutCheck___redArg(
    mut v_budgetMs_1981_: *mut leanh::LeanObject,
    mut v_cleanup_1982_: *mut leanh::LeanObject,
    mut v_x_1983_: *mut leanh::LeanObject,
    mut v_a_1984_: *mut leanh::LeanObject,
    mut v_a_1985_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: u8 = 0;
    let mut v___x_1989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1993_: u8 = 0;
    let mut v___x_1994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1998_: u8 = 0;
    let mut v_unused_1999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2003_: u8 = 0;
    let mut v___x_2005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2007_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1987_ = leanh::lean_unsigned_to_nat(0);
                v___x_1988_ = lean_nat_dec_eq(v_budgetMs_1981_, v___x_1987_);
                if v___x_1988_ == 0 {
                    leanh::lean_dec_ref(v_cleanup_1982_);
                    leanh::lean_inc(v_a_1985_);
                    leanh::lean_inc_ref(v_a_1984_);
                    v___x_1989_ = leanh::lean_apply_3(
                        v_x_1983_,
                        v_a_1984_,
                        v_a_1985_,
                        leanh::lean_box(0),
                    );
                    return v___x_1989_;
                } else {
                    leanh::lean_dec_ref(v_x_1983_);
                    leanh::lean_inc(v_a_1985_);
                    leanh::lean_inc_ref(v_a_1984_);
                    v___x_1990_ = leanh::lean_apply_3(
                        v_cleanup_1982_,
                        v_a_1984_,
                        v_a_1985_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_1990_) == 0 {
                        v_isSharedCheck_1998_ =
                            (!leanh::lean_is_exclusive(v___x_1990_)) as u8;
                        if v_isSharedCheck_1998_ == 0 {
                            v_unused_1999_ = leanh::lean_ctor_get(v___x_1990_, 0);
                            leanh::lean_dec(v_unused_1999_);
                            v___x_1992_ = v___x_1990_;
                            v_isShared_1993_ = v_isSharedCheck_1998_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_1990_);
                            v___x_1992_ = leanh::lean_box(0);
                            v_isShared_1993_ = v_isSharedCheck_1998_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2000_ = leanh::lean_ctor_get(v___x_1990_, 0);
                        v_isSharedCheck_2007_ =
                            (!leanh::lean_is_exclusive(v___x_1990_)) as u8;
                        if v_isSharedCheck_2007_ == 0 {
                            v___x_2002_ = v___x_1990_;
                            v_isShared_2003_ = v_isSharedCheck_2007_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2000_);
                            leanh::lean_dec(v___x_1990_);
                            v___x_2002_ = leanh::lean_box(0);
                            v_isShared_2003_ = v_isSharedCheck_2007_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1994_ = leanh::lean_box(1);
                if v_isShared_1993_ == 0 {
                    leanh::lean_ctor_set(v___x_1992_, 0, v___x_1994_);
                    v___x_1996_ = v___x_1992_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1997_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1997_, 0, v___x_1994_);
                    v___x_1996_ = v_reuseFailAlloc_1997_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1996_;
            }
            3 => {
                if v_isShared_2003_ == 0 {
                    v___x_2005_ = v___x_2002_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2006_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2006_, 0, v_a_2000_);
                    v___x_2005_ = v_reuseFailAlloc_2006_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2005_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withTimeoutCheck___redArg___boxed(
    mut v_budgetMs_2008_: *mut leanh::LeanObject,
    mut v_cleanup_2009_: *mut leanh::LeanObject,
    mut v_x_2010_: *mut leanh::LeanObject,
    mut v_a_2011_: *mut leanh::LeanObject,
    mut v_a_2012_: *mut leanh::LeanObject,
    mut v_a_2013_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2014_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2014_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withTimeoutCheck___redArg(v_budgetMs_2008_, v_cleanup_2009_, v_x_2010_, v_a_2011_, v_a_2012_);
    leanh::lean_dec(v_a_2012_);
    leanh::lean_dec_ref(v_a_2011_);
    leanh::lean_dec(v_budgetMs_2008_);
    return v_res_2014_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withTimeoutCheck(
    mut v_00_u03b1_2015_: *mut leanh::LeanObject,
    mut v_budgetMs_2016_: *mut leanh::LeanObject,
    mut v_cleanup_2017_: *mut leanh::LeanObject,
    mut v_x_2018_: *mut leanh::LeanObject,
    mut v_a_2019_: *mut leanh::LeanObject,
    mut v_a_2020_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2022_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2022_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withTimeoutCheck___redArg(v_budgetMs_2016_, v_cleanup_2017_, v_x_2018_, v_a_2019_, v_a_2020_);
    return v___x_2022_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withTimeoutCheck___boxed(
    mut v_00_u03b1_2023_: *mut leanh::LeanObject,
    mut v_budgetMs_2024_: *mut leanh::LeanObject,
    mut v_cleanup_2025_: *mut leanh::LeanObject,
    mut v_x_2026_: *mut leanh::LeanObject,
    mut v_a_2027_: *mut leanh::LeanObject,
    mut v_a_2028_: *mut leanh::LeanObject,
    mut v_a_2029_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2030_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2030_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withTimeoutCheck(v_00_u03b1_2023_, v_budgetMs_2024_, v_cleanup_2025_, v_x_2026_, v_a_2027_, v_a_2028_);
    leanh::lean_dec(v_a_2028_);
    leanh::lean_dec_ref(v_a_2027_);
    leanh::lean_dec(v_budgetMs_2024_);
    return v_res_2030_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_killAndWait(
    mut v_cfg_2031_: *mut leanh::LeanObject,
    mut v_child_2032_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2038_: u8 = 0;
    let mut v___x_2039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2043_: u8 = 0;
    let mut v_unused_2044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2048_: u8 = 0;
    let mut v___x_2050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2052_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2034_ = lean_io_process_child_kill(v_cfg_2031_, v_child_2032_);
                if leanh::lean_obj_tag(v___x_2034_) == 0 {
                    leanh::lean_dec_ref_known(v___x_2034_, 1);
                    v___x_2035_ = lean_io_process_child_wait(v_cfg_2031_, v_child_2032_);
                    if leanh::lean_obj_tag(v___x_2035_) == 0 {
                        v_isSharedCheck_2043_ =
                            (!leanh::lean_is_exclusive(v___x_2035_)) as u8;
                        if v_isSharedCheck_2043_ == 0 {
                            v_unused_2044_ = leanh::lean_ctor_get(v___x_2035_, 0);
                            leanh::lean_dec(v_unused_2044_);
                            v___x_2037_ = v___x_2035_;
                            v_isShared_2038_ = v_isSharedCheck_2043_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_2035_);
                            v___x_2037_ = leanh::lean_box(0);
                            v_isShared_2038_ = v_isSharedCheck_2043_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2045_ = leanh::lean_ctor_get(v___x_2035_, 0);
                        v_isSharedCheck_2052_ =
                            (!leanh::lean_is_exclusive(v___x_2035_)) as u8;
                        if v_isSharedCheck_2052_ == 0 {
                            v___x_2047_ = v___x_2035_;
                            v_isShared_2048_ = v_isSharedCheck_2052_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2045_);
                            leanh::lean_dec(v___x_2035_);
                            v___x_2047_ = leanh::lean_box(0);
                            v_isShared_2048_ = v_isSharedCheck_2052_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    return v___x_2034_;
                }
            }
            1 => {
                v___x_2039_ = leanh::lean_box(0);
                if v_isShared_2038_ == 0 {
                    leanh::lean_ctor_set(v___x_2037_, 0, v___x_2039_);
                    v___x_2041_ = v___x_2037_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2042_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2042_, 0, v___x_2039_);
                    v___x_2041_ = v_reuseFailAlloc_2042_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2041_;
            }
            3 => {
                if v_isShared_2048_ == 0 {
                    v___x_2050_ = v___x_2047_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2051_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2051_, 0, v_a_2045_);
                    v___x_2050_ = v_reuseFailAlloc_2051_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2050_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_killAndWait___boxed(
    mut v_cfg_2053_: *mut leanh::LeanObject,
    mut v_child_2054_: *mut leanh::LeanObject,
    mut v_a_2055_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2056_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2056_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_killAndWait(v_cfg_2053_, v_child_2054_);
    leanh::lean_dec_ref(v_child_2054_);
    leanh::lean_dec_ref(v_cfg_2053_);
    return v_res_2056_;
}
pub unsafe fn l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go_spec__0___redArg(
    mut v_e_2057_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2062_: u8 = 0;
    let mut v___x_2063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2068_: u8 = 0;
    let mut v_a_2069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2072_: u8 = 0;
    let mut v___x_2074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2076_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_e_2057_) == 0 {
                    v_a_2059_ = leanh::lean_ctor_get(v_e_2057_, 0);
                    v_isSharedCheck_2068_ = (!leanh::lean_is_exclusive(v_e_2057_)) as u8;
                    if v_isSharedCheck_2068_ == 0 {
                        v___x_2061_ = v_e_2057_;
                        v_isShared_2062_ = v_isSharedCheck_2068_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2059_);
                        leanh::lean_dec(v_e_2057_);
                        v___x_2061_ = leanh::lean_box(0);
                        v_isShared_2062_ = v_isSharedCheck_2068_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2069_ = leanh::lean_ctor_get(v_e_2057_, 0);
                    v_isSharedCheck_2076_ = (!leanh::lean_is_exclusive(v_e_2057_)) as u8;
                    if v_isSharedCheck_2076_ == 0 {
                        v___x_2071_ = v_e_2057_;
                        v_isShared_2072_ = v_isSharedCheck_2076_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2069_);
                        leanh::lean_dec(v_e_2057_);
                        v___x_2071_ = leanh::lean_box(0);
                        v_isShared_2072_ = v_isSharedCheck_2076_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2063_ = lean_io_error_to_string(v_a_2059_);
                v___x_2064_ = lean_mk_io_user_error(v___x_2063_);
                if v_isShared_2062_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2061_, 1);
                    leanh::lean_ctor_set(v___x_2061_, 0, v___x_2064_);
                    v___x_2066_ = v___x_2061_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2067_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2067_, 0, v___x_2064_);
                    v___x_2066_ = v_reuseFailAlloc_2067_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2066_;
            }
            3 => {
                if v_isShared_2072_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2071_, 0);
                    v___x_2074_ = v___x_2071_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2075_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2075_, 0, v_a_2069_);
                    v___x_2074_ = v_reuseFailAlloc_2075_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2074_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go_spec__0___redArg___boxed(
    mut v_e_2077_: *mut leanh::LeanObject,
    mut v_a_2078_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2079_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2079_ = l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go_spec__0___redArg(v_e_2077_);
    return v_res_2079_;
}
pub unsafe fn l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go_spec__0(
    mut v_00_u03b1_2080_: *mut leanh::LeanObject,
    mut v_e_2081_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2083_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2083_ = l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go_spec__0___redArg(v_e_2081_);
    return v___x_2083_;
}
pub unsafe fn l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go_spec__0___boxed(
    mut v_00_u03b1_2084_: *mut leanh::LeanObject,
    mut v_e_2085_: *mut leanh::LeanObject,
    mut v_a_2086_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2087_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2087_ = l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go_spec__0(v_00_u03b1_2084_, v_e_2085_);
    return v_res_2087_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go___lam__1(
    mut v_cfg_2088_: *mut leanh::LeanObject,
    mut v_child_2089_: *mut leanh::LeanObject,
    mut v___y_2090_: *mut leanh::LeanObject,
    mut v___y_2091_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2097_: u8 = 0;
    let mut v___x_2099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2101_: u8 = 0;
    let mut v_a_2102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2105_: u8 = 0;
    let mut v_ref_2106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2114_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2093_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_killAndWait(v_cfg_2088_, v_child_2089_);
                if leanh::lean_obj_tag(v___x_2093_) == 0 {
                    v_a_2094_ = leanh::lean_ctor_get(v___x_2093_, 0);
                    v_isSharedCheck_2101_ = (!leanh::lean_is_exclusive(v___x_2093_)) as u8;
                    if v_isSharedCheck_2101_ == 0 {
                        v___x_2096_ = v___x_2093_;
                        v_isShared_2097_ = v_isSharedCheck_2101_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2094_);
                        leanh::lean_dec(v___x_2093_);
                        v___x_2096_ = leanh::lean_box(0);
                        v_isShared_2097_ = v_isSharedCheck_2101_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2102_ = leanh::lean_ctor_get(v___x_2093_, 0);
                    v_isSharedCheck_2114_ = (!leanh::lean_is_exclusive(v___x_2093_)) as u8;
                    if v_isSharedCheck_2114_ == 0 {
                        v___x_2104_ = v___x_2093_;
                        v_isShared_2105_ = v_isSharedCheck_2114_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2102_);
                        leanh::lean_dec(v___x_2093_);
                        v___x_2104_ = leanh::lean_box(0);
                        v_isShared_2105_ = v_isSharedCheck_2114_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2097_ == 0 {
                    v___x_2099_ = v___x_2096_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2100_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2100_, 0, v_a_2094_);
                    v___x_2099_ = v_reuseFailAlloc_2100_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2099_;
            }
            3 => {
                v_ref_2106_ = leanh::lean_ctor_get(v___y_2090_, 5);
                v___x_2107_ = lean_io_error_to_string(v_a_2102_);
                v___x_2108_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2108_, 0, v___x_2107_);
                v___x_2109_ = l_Lean_MessageData_ofFormat(v___x_2108_);
                leanh::lean_inc(v_ref_2106_);
                v___x_2110_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2110_, 0, v_ref_2106_);
                leanh::lean_ctor_set(v___x_2110_, 1, v___x_2109_);
                if v_isShared_2105_ == 0 {
                    leanh::lean_ctor_set(v___x_2104_, 0, v___x_2110_);
                    v___x_2112_ = v___x_2104_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2113_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2113_, 0, v___x_2110_);
                    v___x_2112_ = v_reuseFailAlloc_2113_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2112_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go___lam__1___boxed(
    mut v_cfg_2115_: *mut leanh::LeanObject,
    mut v_child_2116_: *mut leanh::LeanObject,
    mut v___y_2117_: *mut leanh::LeanObject,
    mut v___y_2118_: *mut leanh::LeanObject,
    mut v___y_2119_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2120_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2120_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go___lam__1(v_cfg_2115_, v_child_2116_, v___y_2117_, v___y_2118_);
    leanh::lean_dec(v___y_2118_);
    leanh::lean_dec_ref(v___y_2117_);
    leanh::lean_dec_ref(v_child_2116_);
    leanh::lean_dec_ref(v_cfg_2115_);
    return v_res_2120_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go___lam__0(
    mut v_cfg_2121_: *mut leanh::LeanObject,
    mut v_child_2122_: *mut leanh::LeanObject,
    mut v_budgetMs_2123_: *mut leanh::LeanObject,
    mut v_stdout_2124_: *mut leanh::LeanObject,
    mut v_stderr_2125_: *mut leanh::LeanObject,
    mut v___y_2126_: *mut leanh::LeanObject,
    mut v___y_2127_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: u32 = 0;
    let mut v___x_2132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2139_: u8 = 0;
    let mut v___x_2140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2148_: u8 = 0;
    let mut v___x_2149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: u32 = 0;
    let mut v___x_2152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2157_: u8 = 0;
    let mut v_a_2158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2161_: u8 = 0;
    let mut v_ref_2162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2172_: u8 = 0;
    let mut v_a_2173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2176_: u8 = 0;
    let mut v_ref_2177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2187_: u8 = 0;
    let mut v_isSharedCheck_2188_: u8 = 0;
    let mut v_a_2189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2192_: u8 = 0;
    let mut v_ref_2193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2201_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2129_ = lean_io_process_child_try_wait(v_cfg_2121_, v_child_2122_);
                if leanh::lean_obj_tag(v___x_2129_) == 0 {
                    v_a_2130_ = leanh::lean_ctor_get(v___x_2129_, 0);
                    leanh::lean_inc(v_a_2130_);
                    leanh::lean_dec_ref_known(v___x_2129_, 1);
                    if leanh::lean_obj_tag(v_a_2130_) == 0 {
                        v___x_2131_ = 50;
                        v___x_2132_ = l_IO_sleep(v___x_2131_);
                        v___x_2133_ = leanh::lean_unsigned_to_nat(50);
                        v___x_2134_ = lean_nat_sub(v_budgetMs_2123_, v___x_2133_);
                        v___x_2135_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go(v_cfg_2121_, v___x_2134_, v_child_2122_, v_stdout_2124_, v_stderr_2125_, v___y_2126_, v___y_2127_);
                        return v___x_2135_;
                    } else {
                        leanh::lean_dec_ref(v_child_2122_);
                        leanh::lean_dec_ref(v_cfg_2121_);
                        v_val_2136_ = leanh::lean_ctor_get(v_a_2130_, 0);
                        v_isSharedCheck_2188_ = (!leanh::lean_is_exclusive(v_a_2130_)) as u8;
                        if v_isSharedCheck_2188_ == 0 {
                            v___x_2138_ = v_a_2130_;
                            v_isShared_2139_ = v_isSharedCheck_2188_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_2136_);
                            leanh::lean_dec(v_a_2130_);
                            v___x_2138_ = leanh::lean_box(0);
                            v_isShared_2139_ = v_isSharedCheck_2188_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_stderr_2125_);
                    leanh::lean_dec_ref(v_stdout_2124_);
                    leanh::lean_dec_ref(v_child_2122_);
                    leanh::lean_dec_ref(v_cfg_2121_);
                    v_a_2189_ = leanh::lean_ctor_get(v___x_2129_, 0);
                    v_isSharedCheck_2201_ = (!leanh::lean_is_exclusive(v___x_2129_)) as u8;
                    if v_isSharedCheck_2201_ == 0 {
                        v___x_2191_ = v___x_2129_;
                        v_isShared_2192_ = v_isSharedCheck_2201_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2189_);
                        leanh::lean_dec(v___x_2129_);
                        v___x_2191_ = leanh::lean_box(0);
                        v_isShared_2192_ = v_isSharedCheck_2201_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2140_ = lean_task_get_own(v_stdout_2124_);
                v___x_2141_ = l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go_spec__0___redArg(v___x_2140_);
                if leanh::lean_obj_tag(v___x_2141_) == 0 {
                    v_a_2142_ = leanh::lean_ctor_get(v___x_2141_, 0);
                    leanh::lean_inc(v_a_2142_);
                    leanh::lean_dec_ref_known(v___x_2141_, 1);
                    v___x_2143_ = lean_task_get_own(v_stderr_2125_);
                    v___x_2144_ = l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go_spec__0___redArg(v___x_2143_);
                    if leanh::lean_obj_tag(v___x_2144_) == 0 {
                        v_a_2145_ = leanh::lean_ctor_get(v___x_2144_, 0);
                        v_isSharedCheck_2157_ =
                            (!leanh::lean_is_exclusive(v___x_2144_)) as u8;
                        if v_isSharedCheck_2157_ == 0 {
                            v___x_2147_ = v___x_2144_;
                            v_isShared_2148_ = v_isSharedCheck_2157_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2145_);
                            leanh::lean_dec(v___x_2144_);
                            v___x_2147_ = leanh::lean_box(0);
                            v_isShared_2148_ = v_isSharedCheck_2157_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_2142_);
                        leanh::lean_dec(v_val_2136_);
                        v_a_2158_ = leanh::lean_ctor_get(v___x_2144_, 0);
                        v_isSharedCheck_2172_ =
                            (!leanh::lean_is_exclusive(v___x_2144_)) as u8;
                        if v_isSharedCheck_2172_ == 0 {
                            v___x_2160_ = v___x_2144_;
                            v_isShared_2161_ = v_isSharedCheck_2172_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2158_);
                            leanh::lean_dec(v___x_2144_);
                            v___x_2160_ = leanh::lean_box(0);
                            v_isShared_2161_ = v_isSharedCheck_2172_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_val_2136_);
                    leanh::lean_dec_ref(v_stderr_2125_);
                    v_a_2173_ = leanh::lean_ctor_get(v___x_2141_, 0);
                    v_isSharedCheck_2187_ = (!leanh::lean_is_exclusive(v___x_2141_)) as u8;
                    if v_isSharedCheck_2187_ == 0 {
                        v___x_2175_ = v___x_2141_;
                        v_isShared_2176_ = v_isSharedCheck_2187_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2173_);
                        leanh::lean_dec(v___x_2141_);
                        v___x_2175_ = leanh::lean_box(0);
                        v_isShared_2176_ = v_isSharedCheck_2187_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2149_ = leanh::lean_alloc_ctor(0, 2, (4) as u32);
                leanh::lean_ctor_set(v___x_2149_, 0, v_a_2142_);
                leanh::lean_ctor_set(v___x_2149_, 1, v_a_2145_);
                v___x_2150_ = leanh::lean_unbox_uint32(v_val_2136_);
                leanh::lean_dec(v_val_2136_);
                leanh::lean_ctor_set_uint32(
                    v___x_2149_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_2150_,
                );
                if v_isShared_2139_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2138_, 0);
                    leanh::lean_ctor_set(v___x_2138_, 0, v___x_2149_);
                    v___x_2152_ = v___x_2138_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2156_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2156_, 0, v___x_2149_);
                    v___x_2152_ = v_reuseFailAlloc_2156_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2148_ == 0 {
                    leanh::lean_ctor_set(v___x_2147_, 0, v___x_2152_);
                    v___x_2154_ = v___x_2147_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2155_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2155_, 0, v___x_2152_);
                    v___x_2154_ = v_reuseFailAlloc_2155_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2154_;
            }
            5 => {
                v_ref_2162_ = leanh::lean_ctor_get(v___y_2126_, 5);
                v___x_2163_ = lean_io_error_to_string(v_a_2158_);
                if v_isShared_2139_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2138_, 3);
                    leanh::lean_ctor_set(v___x_2138_, 0, v___x_2163_);
                    v___x_2165_ = v___x_2138_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2171_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2171_, 0, v___x_2163_);
                    v___x_2165_ = v_reuseFailAlloc_2171_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_2166_ = l_Lean_MessageData_ofFormat(v___x_2165_);
                leanh::lean_inc(v_ref_2162_);
                v___x_2167_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2167_, 0, v_ref_2162_);
                leanh::lean_ctor_set(v___x_2167_, 1, v___x_2166_);
                if v_isShared_2161_ == 0 {
                    leanh::lean_ctor_set(v___x_2160_, 0, v___x_2167_);
                    v___x_2169_ = v___x_2160_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2170_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2170_, 0, v___x_2167_);
                    v___x_2169_ = v_reuseFailAlloc_2170_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2169_;
            }
            8 => {
                v_ref_2177_ = leanh::lean_ctor_get(v___y_2126_, 5);
                v___x_2178_ = lean_io_error_to_string(v_a_2173_);
                if v_isShared_2139_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2138_, 3);
                    leanh::lean_ctor_set(v___x_2138_, 0, v___x_2178_);
                    v___x_2180_ = v___x_2138_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2186_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2186_, 0, v___x_2178_);
                    v___x_2180_ = v_reuseFailAlloc_2186_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_2181_ = l_Lean_MessageData_ofFormat(v___x_2180_);
                leanh::lean_inc(v_ref_2177_);
                v___x_2182_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2182_, 0, v_ref_2177_);
                leanh::lean_ctor_set(v___x_2182_, 1, v___x_2181_);
                if v_isShared_2176_ == 0 {
                    leanh::lean_ctor_set(v___x_2175_, 0, v___x_2182_);
                    v___x_2184_ = v___x_2175_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2185_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2185_, 0, v___x_2182_);
                    v___x_2184_ = v_reuseFailAlloc_2185_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2184_;
            }
            11 => {
                v_ref_2193_ = leanh::lean_ctor_get(v___y_2126_, 5);
                v___x_2194_ = lean_io_error_to_string(v_a_2189_);
                v___x_2195_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2195_, 0, v___x_2194_);
                v___x_2196_ = l_Lean_MessageData_ofFormat(v___x_2195_);
                leanh::lean_inc(v_ref_2193_);
                v___x_2197_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2197_, 0, v_ref_2193_);
                leanh::lean_ctor_set(v___x_2197_, 1, v___x_2196_);
                if v_isShared_2192_ == 0 {
                    leanh::lean_ctor_set(v___x_2191_, 0, v___x_2197_);
                    v___x_2199_ = v___x_2191_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2200_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2200_, 0, v___x_2197_);
                    v___x_2199_ = v_reuseFailAlloc_2200_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2199_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go___lam__0___boxed(
    mut v_cfg_2202_: *mut leanh::LeanObject,
    mut v_child_2203_: *mut leanh::LeanObject,
    mut v_budgetMs_2204_: *mut leanh::LeanObject,
    mut v_stdout_2205_: *mut leanh::LeanObject,
    mut v_stderr_2206_: *mut leanh::LeanObject,
    mut v___y_2207_: *mut leanh::LeanObject,
    mut v___y_2208_: *mut leanh::LeanObject,
    mut v___y_2209_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2210_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2210_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go___lam__0(v_cfg_2202_, v_child_2203_, v_budgetMs_2204_, v_stdout_2205_, v_stderr_2206_, v___y_2207_, v___y_2208_);
    leanh::lean_dec(v___y_2208_);
    leanh::lean_dec_ref(v___y_2207_);
    leanh::lean_dec(v_budgetMs_2204_);
    return v_res_2210_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go(
    mut v_cfg_2211_: *mut leanh::LeanObject,
    mut v_budgetMs_2212_: *mut leanh::LeanObject,
    mut v_child_2213_: *mut leanh::LeanObject,
    mut v_stdout_2214_: *mut leanh::LeanObject,
    mut v_stderr_2215_: *mut leanh::LeanObject,
    mut v_a_2216_: *mut leanh::LeanObject,
    mut v_a_2217_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_budgetMs_2212_);
    leanh::lean_inc_ref(v_child_2213_);
    leanh::lean_inc_ref(v_cfg_2211_);
    v___f_2219_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go___lam__0___boxed as *mut core::ffi::c_void, 8, 5);
    leanh::lean_closure_set(v___f_2219_, 0, v_cfg_2211_);
    leanh::lean_closure_set(v___f_2219_, 1, v_child_2213_);
    leanh::lean_closure_set(v___f_2219_, 2, v_budgetMs_2212_);
    leanh::lean_closure_set(v___f_2219_, 3, v_stdout_2214_);
    leanh::lean_closure_set(v___f_2219_, 4, v_stderr_2215_);
    v___f_2220_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go___lam__1___boxed as *mut core::ffi::c_void, 5, 2);
    leanh::lean_closure_set(v___f_2220_, 0, v_cfg_2211_);
    leanh::lean_closure_set(v___f_2220_, 1, v_child_2213_);
    leanh::lean_inc_ref(v___f_2220_);
    v___x_2221_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck___boxed as *mut core::ffi::c_void, 6, 3);
    leanh::lean_closure_set(v___x_2221_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2221_, 1, v___f_2220_);
    leanh::lean_closure_set(v___x_2221_, 2, v___f_2219_);
    v___x_2222_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withTimeoutCheck___redArg(v_budgetMs_2212_, v___f_2220_, v___x_2221_, v_a_2216_, v_a_2217_);
    leanh::lean_dec(v_budgetMs_2212_);
    return v___x_2222_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go___boxed(
    mut v_cfg_2223_: *mut leanh::LeanObject,
    mut v_budgetMs_2224_: *mut leanh::LeanObject,
    mut v_child_2225_: *mut leanh::LeanObject,
    mut v_stdout_2226_: *mut leanh::LeanObject,
    mut v_stderr_2227_: *mut leanh::LeanObject,
    mut v_a_2228_: *mut leanh::LeanObject,
    mut v_a_2229_: *mut leanh::LeanObject,
    mut v_a_2230_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2231_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2231_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go(v_cfg_2223_, v_budgetMs_2224_, v_child_2225_, v_stdout_2226_, v_stderr_2227_, v_a_2228_, v_a_2229_);
    leanh::lean_dec(v_a_2229_);
    leanh::lean_dec_ref(v_a_2228_);
    return v_res_2231_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___lam__0(
    mut v_stdout_2232_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2238_: u8 = 0;
    let mut v___x_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2242_: u8 = 0;
    let mut v_a_2243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2246_: u8 = 0;
    let mut v___x_2248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2250_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2234_ = l_IO_FS_Handle_readToEnd(v_stdout_2232_);
                if leanh::lean_obj_tag(v___x_2234_) == 0 {
                    v_a_2235_ = leanh::lean_ctor_get(v___x_2234_, 0);
                    v_isSharedCheck_2242_ = (!leanh::lean_is_exclusive(v___x_2234_)) as u8;
                    if v_isSharedCheck_2242_ == 0 {
                        v___x_2237_ = v___x_2234_;
                        v_isShared_2238_ = v_isSharedCheck_2242_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2235_);
                        leanh::lean_dec(v___x_2234_);
                        v___x_2237_ = leanh::lean_box(0);
                        v_isShared_2238_ = v_isSharedCheck_2242_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2243_ = leanh::lean_ctor_get(v___x_2234_, 0);
                    v_isSharedCheck_2250_ = (!leanh::lean_is_exclusive(v___x_2234_)) as u8;
                    if v_isSharedCheck_2250_ == 0 {
                        v___x_2245_ = v___x_2234_;
                        v_isShared_2246_ = v_isSharedCheck_2250_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2243_);
                        leanh::lean_dec(v___x_2234_);
                        v___x_2245_ = leanh::lean_box(0);
                        v_isShared_2246_ = v_isSharedCheck_2250_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2238_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2237_, 1);
                    v___x_2240_ = v___x_2237_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2241_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2241_, 0, v_a_2235_);
                    v___x_2240_ = v_reuseFailAlloc_2241_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2240_;
            }
            3 => {
                if v_isShared_2246_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2245_, 0);
                    v___x_2248_ = v___x_2245_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2249_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2249_, 0, v_a_2243_);
                    v___x_2248_ = v_reuseFailAlloc_2249_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2248_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___lam__0___boxed(
    mut v_stdout_2251_: *mut leanh::LeanObject,
    mut v___y_2252_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2253_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2253_ = l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___lam__0(v_stdout_2251_);
    leanh::lean_dec(v_stdout_2251_);
    return v_res_2253_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___lam__1(
    mut v_stderr_2254_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2260_: u8 = 0;
    let mut v___x_2262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2264_: u8 = 0;
    let mut v_a_2265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2268_: u8 = 0;
    let mut v___x_2270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2272_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2256_ = l_IO_FS_Handle_readToEnd(v_stderr_2254_);
                if leanh::lean_obj_tag(v___x_2256_) == 0 {
                    v_a_2257_ = leanh::lean_ctor_get(v___x_2256_, 0);
                    v_isSharedCheck_2264_ = (!leanh::lean_is_exclusive(v___x_2256_)) as u8;
                    if v_isSharedCheck_2264_ == 0 {
                        v___x_2259_ = v___x_2256_;
                        v_isShared_2260_ = v_isSharedCheck_2264_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2257_);
                        leanh::lean_dec(v___x_2256_);
                        v___x_2259_ = leanh::lean_box(0);
                        v_isShared_2260_ = v_isSharedCheck_2264_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2265_ = leanh::lean_ctor_get(v___x_2256_, 0);
                    v_isSharedCheck_2272_ = (!leanh::lean_is_exclusive(v___x_2256_)) as u8;
                    if v_isSharedCheck_2272_ == 0 {
                        v___x_2267_ = v___x_2256_;
                        v_isShared_2268_ = v_isSharedCheck_2272_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2265_);
                        leanh::lean_dec(v___x_2256_);
                        v___x_2267_ = leanh::lean_box(0);
                        v_isShared_2268_ = v_isSharedCheck_2272_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2260_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2259_, 1);
                    v___x_2262_ = v___x_2259_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2263_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2263_, 0, v_a_2257_);
                    v___x_2262_ = v_reuseFailAlloc_2263_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2262_;
            }
            3 => {
                if v_isShared_2268_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2267_, 0);
                    v___x_2270_ = v___x_2267_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2271_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2271_, 0, v_a_2265_);
                    v___x_2270_ = v_reuseFailAlloc_2271_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2270_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___lam__1___boxed(
    mut v_stderr_2273_: *mut leanh::LeanObject,
    mut v___y_2274_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2275_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2275_ = l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___lam__1(v_stderr_2273_);
    leanh::lean_dec(v_stderr_2273_);
    return v_res_2275_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_External_runInterruptible(
    mut v_timeout_2279_: *mut leanh::LeanObject,
    mut v_args_2280_: *mut leanh::LeanObject,
    mut v_a_2281_: *mut leanh::LeanObject,
    mut v_a_2282_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cmd_2285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_2286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cwd_2287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritEnv_2289_: u8 = 0;
    let mut v_setsid_2290_: u8 = 0;
    let mut v___x_2292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2293_: u8 = 0;
    let mut v___x_2295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stdout_2298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stderr_2299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2311_: u8 = 0;
    let mut v_ref_2312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2320_: u8 = 0;
    let mut v_reuseFailAlloc_2321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2322_: u8 = 0;
    let mut v_unused_2323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2284_ = l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___closed__0;
                v_cmd_2285_ = leanh::lean_ctor_get(v_args_2280_, 1);
                v_args_2286_ = leanh::lean_ctor_get(v_args_2280_, 2);
                v_cwd_2287_ = leanh::lean_ctor_get(v_args_2280_, 3);
                v_env_2288_ = leanh::lean_ctor_get(v_args_2280_, 4);
                v_inheritEnv_2289_ = leanh::lean_ctor_get_uint8(
                    v_args_2280_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                );
                v_setsid_2290_ = leanh::lean_ctor_get_uint8(
                    v_args_2280_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 1) as u32,
                );
                v_isSharedCheck_2322_ = (!leanh::lean_is_exclusive(v_args_2280_)) as u8;
                if v_isSharedCheck_2322_ == 0 {
                    v_unused_2323_ = leanh::lean_ctor_get(v_args_2280_, 0);
                    leanh::lean_dec(v_unused_2323_);
                    v___x_2292_ = v_args_2280_;
                    v_isShared_2293_ = v_isSharedCheck_2322_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_env_2288_);
                    leanh::lean_inc(v_cwd_2287_);
                    leanh::lean_inc(v_args_2286_);
                    leanh::lean_inc(v_cmd_2285_);
                    leanh::lean_dec(v_args_2280_);
                    v___x_2292_ = leanh::lean_box(0);
                    v_isShared_2293_ = v_isSharedCheck_2322_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_2293_ == 0 {
                    leanh::lean_ctor_set(v___x_2292_, 0, v___x_2284_);
                    v___x_2295_ = v___x_2292_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2321_ = leanh::lean_alloc_ctor(0, 5, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2321_, 0, v___x_2284_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2321_, 1, v_cmd_2285_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2321_, 2, v_args_2286_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2321_, 3, v_cwd_2287_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2321_, 4, v_env_2288_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2321_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                        v_inheritEnv_2289_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2321_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 1) as u32,
                        v_setsid_2290_,
                    );
                    v___x_2295_ = v_reuseFailAlloc_2321_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2296_ = lean_io_process_spawn(v___x_2295_);
                if leanh::lean_obj_tag(v___x_2296_) == 0 {
                    v_a_2297_ = leanh::lean_ctor_get(v___x_2296_, 0);
                    leanh::lean_inc(v_a_2297_);
                    leanh::lean_dec_ref_known(v___x_2296_, 1);
                    v_stdout_2298_ = leanh::lean_ctor_get(v_a_2297_, 1);
                    v_stderr_2299_ = leanh::lean_ctor_get(v_a_2297_, 2);
                    leanh::lean_inc(v_stdout_2298_);
                    v___f_2300_ = leanh::lean_alloc_closure(
                        l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___lam__0___boxed
                            as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    leanh::lean_closure_set(v___f_2300_, 0, v_stdout_2298_);
                    v___x_2301_ = leanh::lean_unsigned_to_nat(9);
                    v___x_2302_ = lean_io_as_task(v___f_2300_, v___x_2301_);
                    leanh::lean_inc(v_stderr_2299_);
                    v___f_2303_ = leanh::lean_alloc_closure(
                        l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___lam__1___boxed
                            as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    leanh::lean_closure_set(v___f_2303_, 0, v_stderr_2299_);
                    v___x_2304_ = lean_io_as_task(v___f_2303_, v___x_2301_);
                    v___x_2305_ = leanh::lean_unsigned_to_nat(1000);
                    v___x_2306_ = lean_nat_mul(v_timeout_2279_, v___x_2305_);
                    v___x_2307_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go(v___x_2284_, v___x_2306_, v_a_2297_, v___x_2302_, v___x_2304_, v_a_2281_, v_a_2282_);
                    return v___x_2307_;
                } else {
                    v_a_2308_ = leanh::lean_ctor_get(v___x_2296_, 0);
                    v_isSharedCheck_2320_ = (!leanh::lean_is_exclusive(v___x_2296_)) as u8;
                    if v_isSharedCheck_2320_ == 0 {
                        v___x_2310_ = v___x_2296_;
                        v_isShared_2311_ = v_isSharedCheck_2320_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2308_);
                        leanh::lean_dec(v___x_2296_);
                        v___x_2310_ = leanh::lean_box(0);
                        v_isShared_2311_ = v_isSharedCheck_2320_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v_ref_2312_ = leanh::lean_ctor_get(v_a_2281_, 5);
                v___x_2313_ = lean_io_error_to_string(v_a_2308_);
                v___x_2314_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2314_, 0, v___x_2313_);
                v___x_2315_ = l_Lean_MessageData_ofFormat(v___x_2314_);
                leanh::lean_inc(v_ref_2312_);
                v___x_2316_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2316_, 0, v_ref_2312_);
                leanh::lean_ctor_set(v___x_2316_, 1, v___x_2315_);
                if v_isShared_2311_ == 0 {
                    leanh::lean_ctor_set(v___x_2310_, 0, v___x_2316_);
                    v___x_2318_ = v___x_2310_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2319_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2319_, 0, v___x_2316_);
                    v___x_2318_ = v_reuseFailAlloc_2319_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2318_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___boxed(
    mut v_timeout_2324_: *mut leanh::LeanObject,
    mut v_args_2325_: *mut leanh::LeanObject,
    mut v_a_2326_: *mut leanh::LeanObject,
    mut v_a_2327_: *mut leanh::LeanObject,
    mut v_a_2328_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2329_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2329_ = l_Lean_Meta_Tactic_BVDecide_External_runInterruptible(
        v_timeout_2324_,
        v_args_2325_,
        v_a_2326_,
        v_a_2327_,
    );
    leanh::lean_dec(v_a_2327_);
    leanh::lean_dec_ref(v_a_2326_);
    leanh::lean_dec(v_timeout_2324_);
    return v_res_2329_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags(
    mut v_mode_2345_: u8,
) -> *mut leanh::LeanObject {
    match v_mode_2345_ {
        0 => {
            let mut v___x_2346_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2346_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___closed__1;
            return v___x_2346_;
        }
        1 => {
            let mut v___x_2347_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2347_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___closed__3;
            return v___x_2347_;
        }
        _ => {
            let mut v___x_2348_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2348_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___closed__5;
            return v___x_2348_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___boxed(
    mut v_mode_2349_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_mode_boxed_2350_: u8 = 0;
    let mut v_res_2351_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_mode_boxed_2350_ = (leanh::lean_unbox(v_mode_2349_) as u8);
    v_res_2351_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags(v_mode_boxed_2350_);
    return v_res_2351_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2352_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2352_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_2352_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2353_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__0);
    v___x_2354_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2354_, 0, v___x_2353_);
    return v___x_2354_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2355_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__1);
    v___x_2356_ = leanh::lean_unsigned_to_nat(0);
    v___x_2357_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_2357_, 0, v___x_2356_);
    leanh::lean_ctor_set(v___x_2357_, 1, v___x_2356_);
    leanh::lean_ctor_set(v___x_2357_, 2, v___x_2356_);
    leanh::lean_ctor_set(v___x_2357_, 3, v___x_2356_);
    leanh::lean_ctor_set(v___x_2357_, 4, v___x_2355_);
    leanh::lean_ctor_set(v___x_2357_, 5, v___x_2355_);
    leanh::lean_ctor_set(v___x_2357_, 6, v___x_2355_);
    leanh::lean_ctor_set(v___x_2357_, 7, v___x_2355_);
    leanh::lean_ctor_set(v___x_2357_, 8, v___x_2355_);
    leanh::lean_ctor_set(v___x_2357_, 9, v___x_2355_);
    return v___x_2357_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2358_ = leanh::lean_unsigned_to_nat(32);
    v___x_2359_ = lean_mk_empty_array_with_capacity(v___x_2358_);
    v___x_2360_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2360_, 0, v___x_2359_);
    return v___x_2360_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_2361_: usize = 0;
    let mut v___x_2362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2361_ = 5usize;
    v___x_2362_ = leanh::lean_unsigned_to_nat(0);
    v___x_2363_ = leanh::lean_unsigned_to_nat(32);
    v___x_2364_ = lean_mk_empty_array_with_capacity(v___x_2363_);
    v___x_2365_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__3);
    v___x_2366_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_2366_, 0, v___x_2365_);
    leanh::lean_ctor_set(v___x_2366_, 1, v___x_2364_);
    leanh::lean_ctor_set(v___x_2366_, 2, v___x_2362_);
    leanh::lean_ctor_set(v___x_2366_, 3, v___x_2362_);
    leanh::lean_ctor_set_usize(v___x_2366_, 4, v___x_2361_);
    return v___x_2366_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_2367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2367_ = leanh::lean_box(1);
    v___x_2368_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__4);
    v___x_2369_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__1);
    v___x_2370_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2370_, 0, v___x_2369_);
    leanh::lean_ctor_set(v___x_2370_, 1, v___x_2368_);
    leanh::lean_ctor_set(v___x_2370_, 2, v___x_2367_);
    return v___x_2370_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0(
    mut v_msgData_2371_: *mut leanh::LeanObject,
    mut v___y_2372_: *mut leanh::LeanObject,
    mut v___y_2373_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2375_ = lean_st_ref_get(v___y_2373_);
    v_env_2376_ = leanh::lean_ctor_get(v___x_2375_, 0);
    leanh::lean_inc_ref(v_env_2376_);
    leanh::lean_dec(v___x_2375_);
    v_options_2377_ = leanh::lean_ctor_get(v___y_2372_, 2);
    v___x_2378_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__2);
    v___x_2379_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__5);
    leanh::lean_inc_ref(v_options_2377_);
    v___x_2380_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_2380_, 0, v_env_2376_);
    leanh::lean_ctor_set(v___x_2380_, 1, v___x_2378_);
    leanh::lean_ctor_set(v___x_2380_, 2, v___x_2379_);
    leanh::lean_ctor_set(v___x_2380_, 3, v_options_2377_);
    v___x_2381_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2381_, 0, v___x_2380_);
    leanh::lean_ctor_set(v___x_2381_, 1, v_msgData_2371_);
    v___x_2382_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2382_, 0, v___x_2381_);
    return v___x_2382_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___boxed(
    mut v_msgData_2383_: *mut leanh::LeanObject,
    mut v___y_2384_: *mut leanh::LeanObject,
    mut v___y_2385_: *mut leanh::LeanObject,
    mut v___y_2386_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2387_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2387_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0(v_msgData_2383_, v___y_2384_, v___y_2385_);
    leanh::lean_dec(v___y_2385_);
    leanh::lean_dec_ref(v___y_2384_);
    return v_res_2387_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0___redArg(
    mut v_msg_2388_: *mut leanh::LeanObject,
    mut v___y_2389_: *mut leanh::LeanObject,
    mut v___y_2390_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_2392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2397_: u8 = 0;
    let mut v___x_2398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2402_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2392_ = leanh::lean_ctor_get(v___y_2389_, 5);
                v___x_2393_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0(v_msg_2388_, v___y_2389_, v___y_2390_);
                v_a_2394_ = leanh::lean_ctor_get(v___x_2393_, 0);
                v_isSharedCheck_2402_ = (!leanh::lean_is_exclusive(v___x_2393_)) as u8;
                if v_isSharedCheck_2402_ == 0 {
                    v___x_2396_ = v___x_2393_;
                    v_isShared_2397_ = v_isSharedCheck_2402_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2394_);
                    leanh::lean_dec(v___x_2393_);
                    v___x_2396_ = leanh::lean_box(0);
                    v_isShared_2397_ = v_isSharedCheck_2402_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_2392_);
                v___x_2398_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2398_, 0, v_ref_2392_);
                leanh::lean_ctor_set(v___x_2398_, 1, v_a_2394_);
                if v_isShared_2397_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2396_, 1);
                    leanh::lean_ctor_set(v___x_2396_, 0, v___x_2398_);
                    v___x_2400_ = v___x_2396_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2401_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2401_, 0, v___x_2398_);
                    v___x_2400_ = v_reuseFailAlloc_2401_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2400_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0___redArg___boxed(
    mut v_msg_2403_: *mut leanh::LeanObject,
    mut v___y_2404_: *mut leanh::LeanObject,
    mut v___y_2405_: *mut leanh::LeanObject,
    mut v___y_2406_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2407_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2407_ =
        l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0___redArg(
            v_msg_2403_,
            v___y_2404_,
            v___y_2405_,
        );
    leanh::lean_dec(v___y_2405_);
    leanh::lean_dec_ref(v___y_2404_);
    return v_res_2407_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2411_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2410_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseHeader___closed__0;
    v___x_2411_ = lean_string_utf8_byte_size(v___x_2410_);
    return v___x_2411_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_2424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2424_ = l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__11;
    v___x_2425_ = lean_string_utf8_byte_size(v___x_2424_);
    return v___x_2425_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__16()
-> *mut leanh::LeanObject {
    let mut v___x_2430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2430_ = l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__15;
    v___x_2431_ = l_Lean_MessageData_ofFormat(v___x_2430_);
    return v___x_2431_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_External_satQuery(
    mut v_solverPath_2434_: *mut leanh::LeanObject,
    mut v_problemPath_2435_: *mut leanh::LeanObject,
    mut v_proofOutput_2436_: *mut leanh::LeanObject,
    mut v_timeout_2437_: *mut leanh::LeanObject,
    mut v_binaryProofs_2438_: u8,
    mut v_mode_2439_: u8,
    mut v_a_2440_: *mut leanh::LeanObject,
    mut v_a_2441_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2458_: u8 = 0;
    let mut v___x_2459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: u8 = 0;
    let mut v___x_2463_: u8 = 0;
    let mut v___x_2464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2470_: u8 = 0;
    let mut v___x_2471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2481_: u8 = 0;
    let mut v_a_2482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2485_: u8 = 0;
    let mut v___x_2487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2490_: u8 = 0;
    let mut v___x_2491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_2507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_2509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: u8 = 0;
    let mut v___x_2515_: u8 = 0;
    let mut v___x_2516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_2519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2522_: u8 = 0;
    let mut v_exitCode_2523_: u32 = 0;
    let mut v_stdout_2524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stderr_2525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: u32 = 0;
    let mut v___x_2527_: u8 = 0;
    let mut v___x_2528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: u8 = 0;
    let mut v___x_2532_: u8 = 0;
    let mut v___x_2533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2540_: u8 = 0;
    let mut v___x_2541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2546_: u8 = 0;
    let mut v___x_2548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2550_: u8 = 0;
    let mut v___x_2551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2493_ = l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__5;
                v___x_2494_ = l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__6;
                if v_binaryProofs_2438_ == 0 {
                    v___x_2551_ = l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__17;
                    v___y_2496_ = v___x_2551_;
                    state = 7;
                    continue;
                } else {
                    v___x_2552_ = l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__18;
                    v___y_2496_ = v___x_2552_;
                    state = 7;
                    continue;
                }
            }
            1 => {
                v___x_2446_ = l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__0;
                v___x_2447_ = lean_string_append(v___x_2446_, v___y_2444_);
                leanh::lean_dec_ref(v___y_2444_);
                v___x_2448_ = l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__1;
                v___x_2449_ = lean_string_append(v___x_2447_, v___x_2448_);
                v___x_2450_ = lean_string_append(v___x_2449_, v___y_2445_);
                leanh::lean_dec_ref(v___y_2445_);
                v___x_2451_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2451_, 0, v___x_2450_);
                v___x_2452_ = l_Lean_MessageData_ofFormat(v___x_2451_);
                v___x_2453_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0___redArg(v___x_2452_, v_a_2440_, v_a_2441_);
                return v___x_2453_;
            }
            2 => {
                if v___y_2458_ == 0 {
                    v___x_2459_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseHeader___closed__0;
                    v___x_2460_ = lean_string_utf8_byte_size(v___y_2456_);
                    v___x_2461_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__2_once
                        ),
                        _init_l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__2,
                    );
                    v___x_2462_ = lean_nat_dec_le(v___x_2461_, v___x_2460_);
                    if v___x_2462_ == 0 {
                        v___y_2444_ = v___y_2456_;
                        v___y_2445_ = v___y_2457_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2463_ = lean_string_memcmp(
                            v___y_2456_,
                            v___x_2459_,
                            v___y_2455_,
                            v___y_2455_,
                            v___x_2461_,
                        );
                        if v___x_2463_ == 0 {
                            v___y_2444_ = v___y_2456_;
                            v___y_2445_ = v___y_2457_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v___y_2457_);
                            v___x_2464_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parse as *mut core::ffi::c_void, 1, 0);
                            v___x_2465_ = lean_string_to_utf8(v___y_2456_);
                            v___x_2466_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(
                                v___x_2464_,
                                v___x_2465_,
                            );
                            if leanh::lean_obj_tag(v___x_2466_) == 0 {
                                v_a_2467_ = leanh::lean_ctor_get(v___x_2466_, 0);
                                v_isSharedCheck_2481_ =
                                    (!leanh::lean_is_exclusive(v___x_2466_)) as u8;
                                if v_isSharedCheck_2481_ == 0 {
                                    v___x_2469_ = v___x_2466_;
                                    v_isShared_2470_ = v_isSharedCheck_2481_;
                                    state = 3;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2467_);
                                    leanh::lean_dec(v___x_2466_);
                                    v___x_2469_ = leanh::lean_box(0);
                                    v_isShared_2470_ = v_isSharedCheck_2481_;
                                    state = 3;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec_ref(v___y_2456_);
                                v_a_2482_ = leanh::lean_ctor_get(v___x_2466_, 0);
                                v_isSharedCheck_2490_ =
                                    (!leanh::lean_is_exclusive(v___x_2466_)) as u8;
                                if v_isSharedCheck_2490_ == 0 {
                                    v___x_2484_ = v___x_2466_;
                                    v_isShared_2485_ = v_isSharedCheck_2490_;
                                    state = 5;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2482_);
                                    leanh::lean_dec(v___x_2466_);
                                    v___x_2484_ = leanh::lean_box(0);
                                    v_isShared_2485_ = v_isSharedCheck_2490_;
                                    state = 5;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___y_2457_);
                    leanh::lean_dec_ref(v___y_2456_);
                    v___x_2491_ = leanh::lean_box(1);
                    v___x_2492_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2492_, 0, v___x_2491_);
                    return v___x_2492_;
                }
            }
            3 => {
                v___x_2471_ = l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__3;
                v___x_2472_ = lean_string_append(v___x_2471_, v_a_2467_);
                leanh::lean_dec(v_a_2467_);
                v___x_2473_ = l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__4;
                v___x_2474_ = lean_string_append(v___x_2472_, v___x_2473_);
                v___x_2475_ = lean_string_append(v___x_2474_, v___y_2456_);
                leanh::lean_dec_ref(v___y_2456_);
                if v_isShared_2470_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2469_, 3);
                    leanh::lean_ctor_set(v___x_2469_, 0, v___x_2475_);
                    v___x_2477_ = v___x_2469_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2480_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2480_, 0, v___x_2475_);
                    v___x_2477_ = v_reuseFailAlloc_2480_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2478_ = l_Lean_MessageData_ofFormat(v___x_2477_);
                v___x_2479_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0___redArg(v___x_2478_, v_a_2440_, v_a_2441_);
                return v___x_2479_;
            }
            5 => {
                if v_isShared_2485_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2484_, 0);
                    v___x_2487_ = v___x_2484_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2489_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2489_, 0, v_a_2482_);
                    v___x_2487_ = v_reuseFailAlloc_2489_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_2488_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2488_, 0, v___x_2487_);
                return v___x_2488_;
            }
            7 => {
                v___x_2497_ = lean_string_append(v___x_2494_, v___y_2496_);
                v___x_2498_ = l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__7;
                v___x_2499_ = l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__8;
                v___x_2500_ = leanh::lean_unsigned_to_nat(6);
                v___x_2501_ = lean_mk_empty_array_with_capacity(v___x_2500_);
                v___x_2502_ = lean_array_push(v___x_2501_, v_problemPath_2435_);
                v___x_2503_ = lean_array_push(v___x_2502_, v_proofOutput_2436_);
                v___x_2504_ = lean_array_push(v___x_2503_, v___x_2493_);
                v___x_2505_ = lean_array_push(v___x_2504_, v___x_2497_);
                v___x_2506_ = lean_array_push(v___x_2505_, v___x_2498_);
                v_args_2507_ = lean_array_push(v___x_2506_, v___x_2499_);
                v___x_2508_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags(v_mode_2439_);
                v_args_2509_ = l_Array_append___redArg(v_args_2507_, v___x_2508_);
                leanh::lean_dec_ref(v___x_2508_);
                v___x_2510_ = l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__9;
                v___x_2511_ = leanh::lean_box(0);
                v___x_2512_ = leanh::lean_unsigned_to_nat(0);
                v___x_2513_ = l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__10;
                v___x_2514_ = 1;
                v___x_2515_ = 0;
                v___x_2516_ = leanh::lean_alloc_ctor(0, 5, (2) as u32);
                leanh::lean_ctor_set(v___x_2516_, 0, v___x_2510_);
                leanh::lean_ctor_set(v___x_2516_, 1, v_solverPath_2434_);
                leanh::lean_ctor_set(v___x_2516_, 2, v_args_2509_);
                leanh::lean_ctor_set(v___x_2516_, 3, v___x_2511_);
                leanh::lean_ctor_set(v___x_2516_, 4, v___x_2513_);
                leanh::lean_ctor_set_uint8(
                    v___x_2516_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                    v___x_2514_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2516_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 1) as u32,
                    v___x_2515_,
                );
                v___x_2517_ = l_Lean_Meta_Tactic_BVDecide_External_runInterruptible(
                    v_timeout_2437_,
                    v___x_2516_,
                    v_a_2440_,
                    v_a_2441_,
                );
                if leanh::lean_obj_tag(v___x_2517_) == 0 {
                    v_a_2518_ = leanh::lean_ctor_get(v___x_2517_, 0);
                    leanh::lean_inc(v_a_2518_);
                    leanh::lean_dec_ref_known(v___x_2517_, 1);
                    if leanh::lean_obj_tag(v_a_2518_) == 0 {
                        v_x_2519_ = leanh::lean_ctor_get(v_a_2518_, 0);
                        v_isSharedCheck_2540_ = (!leanh::lean_is_exclusive(v_a_2518_)) as u8;
                        if v_isSharedCheck_2540_ == 0 {
                            v___x_2521_ = v_a_2518_;
                            v_isShared_2522_ = v_isSharedCheck_2540_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_inc(v_x_2519_);
                            leanh::lean_dec(v_a_2518_);
                            v___x_2521_ = leanh::lean_box(0);
                            v_isShared_2522_ = v_isSharedCheck_2540_;
                            state = 8;
                            continue;
                        }
                    } else {
                        v___x_2541_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__16
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__16_once
                            ),
                            _init_l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__16,
                        );
                        v___x_2542_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0___redArg(v___x_2541_, v_a_2440_, v_a_2441_);
                        return v___x_2542_;
                    }
                } else {
                    v_a_2543_ = leanh::lean_ctor_get(v___x_2517_, 0);
                    v_isSharedCheck_2550_ = (!leanh::lean_is_exclusive(v___x_2517_)) as u8;
                    if v_isSharedCheck_2550_ == 0 {
                        v___x_2545_ = v___x_2517_;
                        v_isShared_2546_ = v_isSharedCheck_2550_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2543_);
                        leanh::lean_dec(v___x_2517_);
                        v___x_2545_ = leanh::lean_box(0);
                        v_isShared_2546_ = v_isSharedCheck_2550_;
                        state = 10;
                        continue;
                    }
                }
            }
            8 => {
                v_exitCode_2523_ = leanh::lean_ctor_get_uint32(
                    v_x_2519_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                );
                v_stdout_2524_ = leanh::lean_ctor_get(v_x_2519_, 0);
                leanh::lean_inc_ref(v_stdout_2524_);
                v_stderr_2525_ = leanh::lean_ctor_get(v_x_2519_, 1);
                leanh::lean_inc_ref(v_stderr_2525_);
                leanh::lean_dec(v_x_2519_);
                v___x_2526_ = 255;
                v___x_2527_ = lean_uint32_dec_eq(v_exitCode_2523_, v___x_2526_);
                if v___x_2527_ == 0 {
                    leanh::lean_del_object(v___x_2521_);
                    v___x_2528_ = l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__11;
                    v___x_2529_ = lean_string_utf8_byte_size(v_stdout_2524_);
                    v___x_2530_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__12
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__12_once
                        ),
                        _init_l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__12,
                    );
                    v___x_2531_ = lean_nat_dec_le(v___x_2530_, v___x_2529_);
                    if v___x_2531_ == 0 {
                        v___y_2455_ = v___x_2512_;
                        v___y_2456_ = v_stdout_2524_;
                        v___y_2457_ = v_stderr_2525_;
                        v___y_2458_ = v___x_2527_;
                        state = 2;
                        continue;
                    } else {
                        v___x_2532_ = lean_string_memcmp(
                            v_stdout_2524_,
                            v___x_2528_,
                            v___x_2512_,
                            v___x_2512_,
                            v___x_2530_,
                        );
                        v___y_2455_ = v___x_2512_;
                        v___y_2456_ = v_stdout_2524_;
                        v___y_2457_ = v_stderr_2525_;
                        v___y_2458_ = v___x_2532_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_stdout_2524_);
                    v___x_2533_ = l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__13;
                    v___x_2534_ = lean_string_append(v___x_2533_, v_stderr_2525_);
                    leanh::lean_dec_ref(v_stderr_2525_);
                    if v_isShared_2522_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_2521_, 3);
                        leanh::lean_ctor_set(v___x_2521_, 0, v___x_2534_);
                        v___x_2536_ = v___x_2521_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_2539_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2539_, 0, v___x_2534_);
                        v___x_2536_ = v_reuseFailAlloc_2539_;
                        state = 9;
                        continue;
                    }
                }
            }
            9 => {
                v___x_2537_ = l_Lean_MessageData_ofFormat(v___x_2536_);
                v___x_2538_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0___redArg(v___x_2537_, v_a_2440_, v_a_2441_);
                return v___x_2538_;
            }
            10 => {
                if v_isShared_2546_ == 0 {
                    v___x_2548_ = v___x_2545_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2549_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2549_, 0, v_a_2543_);
                    v___x_2548_ = v_reuseFailAlloc_2549_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2548_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_External_satQuery___boxed(
    mut v_solverPath_2553_: *mut leanh::LeanObject,
    mut v_problemPath_2554_: *mut leanh::LeanObject,
    mut v_proofOutput_2555_: *mut leanh::LeanObject,
    mut v_timeout_2556_: *mut leanh::LeanObject,
    mut v_binaryProofs_2557_: *mut leanh::LeanObject,
    mut v_mode_2558_: *mut leanh::LeanObject,
    mut v_a_2559_: *mut leanh::LeanObject,
    mut v_a_2560_: *mut leanh::LeanObject,
    mut v_a_2561_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_binaryProofs_boxed_2562_: u8 = 0;
    let mut v_mode_boxed_2563_: u8 = 0;
    let mut v_res_2564_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_binaryProofs_boxed_2562_ = (leanh::lean_unbox(v_binaryProofs_2557_) as u8);
    v_mode_boxed_2563_ = (leanh::lean_unbox(v_mode_2558_) as u8);
    v_res_2564_ = l_Lean_Meta_Tactic_BVDecide_External_satQuery(
        v_solverPath_2553_,
        v_problemPath_2554_,
        v_proofOutput_2555_,
        v_timeout_2556_,
        v_binaryProofs_boxed_2562_,
        v_mode_boxed_2563_,
        v_a_2559_,
        v_a_2560_,
    );
    leanh::lean_dec(v_a_2560_);
    leanh::lean_dec_ref(v_a_2559_);
    leanh::lean_dec(v_timeout_2556_);
    return v_res_2564_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0(
    mut v_00_u03b1_2565_: *mut leanh::LeanObject,
    mut v_msg_2566_: *mut leanh::LeanObject,
    mut v___y_2567_: *mut leanh::LeanObject,
    mut v___y_2568_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2570_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2570_ =
        l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0___redArg(
            v_msg_2566_,
            v___y_2567_,
            v___y_2568_,
        );
    return v___x_2570_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0___boxed(
    mut v_00_u03b1_2571_: *mut leanh::LeanObject,
    mut v_msg_2572_: *mut leanh::LeanObject,
    mut v___y_2573_: *mut leanh::LeanObject,
    mut v___y_2574_: *mut leanh::LeanObject,
    mut v___y_2575_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2576_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2576_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0(
        v_00_u03b1_2571_,
        v_msg_2572_,
        v___y_2573_,
        v___y_2574_,
    );
    leanh::lean_dec(v___y_2574_);
    leanh::lean_dec_ref(v___y_2573_);
    return v_res_2576_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_BVDecide_External(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Parser(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_CoreM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Syntax(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_BVDecide_External(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_BVDecide_External(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_BVDecide_LRAT_Parser(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_CoreM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Syntax(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_External(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_BVDecide_External(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_BVDecide_External(builtin);
}