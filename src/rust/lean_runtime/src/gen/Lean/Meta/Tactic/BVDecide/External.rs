// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.External
// Imports: Std.Tactic.BVDecide.LRAT.Parser Lean.CoreM Std.Tactic.BVDecide.Syntax
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
use crate::lean_imports_rs::Init::Core::lean_task_get_own;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::ByteArray::Basic::lean_byte_array_fget;
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_dec_lt, lean_int_neg, lean_nat_abs, lean_nat_to_int,
};
use crate::lean_imports_rs::Init::Data::String::Defs::{lean_string_append, lean_string_to_utf8};
use crate::lean_imports_rs::Init::Data::String::Pattern::Basic::lean_string_memcmp;
use crate::lean_imports_rs::Init::Data::UInt::Basic::lean_uint8_sub;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_uint8_to_nat, lean_uint8_to_uint32, lean_uint32_to_uint8, lean_usize_add,
    lean_usize_dec_lt,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_push, lean_byte_array_size, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_mul, lean_nat_sub,
    lean_string_utf8_byte_size, lean_uint8_dec_eq, lean_uint8_dec_le, lean_uint32_dec_eq,
};
use crate::lean_imports_rs::Init::System::IO::{
    lean_io_as_task, lean_io_process_child_kill, lean_io_process_child_try_wait,
    lean_io_process_child_wait, lean_io_process_spawn,
};
use crate::lean_imports_rs::Init::System::ST::lean_st_ref_get;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_3, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_get_uint32, lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8,
    lean_ctor_set_uint32, lean_ctor_set_usize, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_inc, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_uint8_once, lean_unbox, lean_unbox_uint32,
    lean_unbox_usize, lean_unsigned_to_nat,
};
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__0: u8 = 0;
pub static l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__1_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [101, 120, 112, 101, 99, 116, 101, 100, 58, 32, 39, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__1_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__5_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [39, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__5_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__8_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [100, 105, 103, 105, 116, 32, 101, 120, 112, 101, 99, 116, 101, 100, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__8_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__9_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__8_value) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__9_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__10_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__10: u8 = 0;
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__11: u8 = 0;
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__12_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__12: u8 = 0;
pub static l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__13_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [105, 100, 32, 119, 97, 115, 32, 48, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__13: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__13_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__14_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__13_value) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__14: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__14_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__15_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__15: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__16_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__16: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__17_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__17: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__18_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__18: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__19_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__19: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__2___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__2___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__0: u8 = 0;
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__6_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__7_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [32, 48, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__7_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__8_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__8: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__9_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [13, 10, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__9_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__10_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__10: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__11: u8 = 0;
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__12_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__12: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__13: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__14_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__14: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__15_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__15: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__16_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__16: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseLines___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseLines___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseLines___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseHeader___closed__0_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [115, 32, 83, 65, 84, 73, 83, 70, 73, 65, 66, 76, 69, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseHeader___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseHeader___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseHeader___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseHeader___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___closed__0_value: LeanCtorObject<
    1,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 0
            + 8) as u16,
        other: 0,
        tag: 0,
    },
    m_objs: [2 as *mut LeanObject],
};
static mut l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___closed__0_value)
        as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___closed__0_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [45, 45, 117, 110, 115, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___closed__1_value: LeanArrayObject<1> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 246 }, m_size: 1, m_capacity: 1, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___closed__0_value) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___closed__2_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [45, 45, 115, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___closed__3_value: LeanArrayObject<1> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 246 }, m_size: 1, m_capacity: 1, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___closed__2_value) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___closed__4_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [45, 45, 100, 101, 102, 97, 117, 108, 116, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___closed__5_value: LeanArrayObject<1> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 246 }, m_size: 1, m_capacity: 1, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___closed__4_value) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___closed__5_value) as *mut LeanObject;
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__0_value: LeanStringObject<57> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 57,
        m_capacity: 57,
        m_length: 56,
        m_data: [
            84, 104, 101, 32, 101, 120, 116, 101, 114, 110, 97, 108, 32, 112, 114, 111, 118, 101,
            114, 32, 112, 114, 111, 100, 117, 99, 101, 100, 32, 117, 110, 101, 120, 112, 101, 99,
            116, 101, 100, 32, 111, 117, 116, 112, 117, 116, 44, 32, 115, 116, 100, 111, 117, 116,
            58, 10, 0,
        ],
    };
static mut l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__1_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__3_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__4_value: LeanStringObject<17> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__5_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__6_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__7_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__8_value: LeanStringObject<11> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__9_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 0
                + 8) as u16,
            other: 0,
            tag: 0,
        },
        m_objs: [131072 as *mut LeanObject],
    };
static mut l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__10_value: LeanArrayObject<0> =
    LeanArrayObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__11_value: LeanStringObject<16> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__11_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__12_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__12: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__13_value: LeanStringObject<36> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 36,
        m_capacity: 36,
        m_length: 35,
        m_data: [
            70, 97, 105, 108, 101, 100, 32, 116, 111, 32, 101, 120, 101, 99, 117, 116, 101, 32,
            101, 120, 116, 101, 114, 110, 97, 108, 32, 112, 114, 111, 118, 101, 114, 58, 10, 0,
        ],
    };
static mut l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__13_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__14_value: LeanStringObject<245> =
    LeanStringObject {
        m_header: LeanObject {
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
            100, 32, 111, 117, 116, 32, 119, 104, 105, 108, 101, 32, 115, 111, 108, 118, 105, 110,
            103, 32, 116, 104, 101, 32, 112, 114, 111, 98, 108, 101, 109, 46, 10, 67, 111, 110,
            115, 105, 100, 101, 114, 32, 105, 110, 99, 114, 101, 97, 115, 105, 110, 103, 32, 116,
            104, 101, 32, 116, 105, 109, 101, 111, 117, 116, 32, 119, 105, 116, 104, 32, 116, 104,
            101, 32, 96, 116, 105, 109, 101, 111, 117, 116, 96, 32, 99, 111, 110, 102, 105, 103,
            32, 111, 112, 116, 105, 111, 110, 46, 10, 73, 102, 32, 115, 111, 108, 118, 105, 110,
            103, 32, 121, 111, 117, 114, 32, 112, 114, 111, 98, 108, 101, 109, 32, 114, 101, 108,
            105, 101, 115, 32, 105, 110, 104, 101, 114, 101, 110, 116, 108, 121, 32, 111, 110, 32,
            117, 115, 105, 110, 103, 32, 97, 115, 115, 111, 99, 105, 97, 116, 105, 118, 105, 116,
            121, 32, 111, 114, 32, 99, 111, 109, 109, 117, 116, 97, 116, 105, 118, 105, 116, 121,
            44, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 101, 110, 97, 98, 108, 105, 110,
            103, 32, 116, 104, 101, 32, 96, 97, 99, 78, 102, 96, 32, 99, 111, 110, 102, 105, 103,
            32, 111, 112, 116, 105, 111, 110, 46, 0,
        ],
    };
static mut l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__14_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__15_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__14_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__15_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__16_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__16: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__17_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__17_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__18_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__18_value)
        as *mut LeanObject;
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_External_SolverResult_ctorIdx(
    mut v_x_1289_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1289_) == 0 {
        let mut v___x_1290_: *mut LeanObject = core::ptr::null_mut();
        v___x_1290_ = lean_unsigned_to_nat(0);
        return v___x_1290_;
    } else {
        let mut v___x_1291_: *mut LeanObject = core::ptr::null_mut();
        v___x_1291_ = lean_unsigned_to_nat(1);
        return v___x_1291_;
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_External_SolverResult_ctorIdx___boxed(
    mut v_x_1292_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1293_: *mut LeanObject = core::ptr::null_mut();
    v_res_1293_ = l_Lean_Meta_Tactic_BVDecide_External_SolverResult_ctorIdx(v_x_1292_);
    lean_dec(v_x_1292_);
    return v_res_1293_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_External_SolverResult_ctorElim___redArg(
    mut v_t_1294_: *mut LeanObject,
    mut v_k_1295_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_1294_) == 0 {
        let mut v_assignment_1296_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1297_: *mut LeanObject = core::ptr::null_mut();
        v_assignment_1296_ = lean_ctor_get(v_t_1294_, 0);
        lean_inc_ref(v_assignment_1296_);
        lean_dec_ref_known(v_t_1294_, 1);
        v___x_1297_ = lean_apply_1(v_k_1295_, v_assignment_1296_);
        return v___x_1297_;
    } else {
        return v_k_1295_;
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_External_SolverResult_ctorElim(
    mut v_motive_1298_: *mut LeanObject,
    mut v_ctorIdx_1299_: *mut LeanObject,
    mut v_t_1300_: *mut LeanObject,
    mut v_h_1301_: *mut LeanObject,
    mut v_k_1302_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1303_: *mut LeanObject = core::ptr::null_mut();
    v___x_1303_ =
        l_Lean_Meta_Tactic_BVDecide_External_SolverResult_ctorElim___redArg(v_t_1300_, v_k_1302_);
    return v___x_1303_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_External_SolverResult_ctorElim___boxed(
    mut v_motive_1304_: *mut LeanObject,
    mut v_ctorIdx_1305_: *mut LeanObject,
    mut v_t_1306_: *mut LeanObject,
    mut v_h_1307_: *mut LeanObject,
    mut v_k_1308_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1309_: *mut LeanObject = core::ptr::null_mut();
    v_res_1309_ = l_Lean_Meta_Tactic_BVDecide_External_SolverResult_ctorElim(
        v_motive_1304_,
        v_ctorIdx_1305_,
        v_t_1306_,
        v_h_1307_,
        v_k_1308_,
    );
    lean_dec(v_ctorIdx_1305_);
    return v_res_1309_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_External_SolverResult_sat_elim___redArg(
    mut v_t_1310_: *mut LeanObject,
    mut v_sat_1311_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1312_: *mut LeanObject = core::ptr::null_mut();
    v___x_1312_ =
        l_Lean_Meta_Tactic_BVDecide_External_SolverResult_ctorElim___redArg(v_t_1310_, v_sat_1311_);
    return v___x_1312_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_External_SolverResult_sat_elim(
    mut v_motive_1313_: *mut LeanObject,
    mut v_t_1314_: *mut LeanObject,
    mut v_h_1315_: *mut LeanObject,
    mut v_sat_1316_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1317_: *mut LeanObject = core::ptr::null_mut();
    v___x_1317_ =
        l_Lean_Meta_Tactic_BVDecide_External_SolverResult_ctorElim___redArg(v_t_1314_, v_sat_1316_);
    return v___x_1317_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_External_SolverResult_unsat_elim___redArg(
    mut v_t_1318_: *mut LeanObject,
    mut v_unsat_1319_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1320_: *mut LeanObject = core::ptr::null_mut();
    v___x_1320_ = l_Lean_Meta_Tactic_BVDecide_External_SolverResult_ctorElim___redArg(
        v_t_1318_,
        v_unsat_1319_,
    );
    return v___x_1320_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_External_SolverResult_unsat_elim(
    mut v_motive_1321_: *mut LeanObject,
    mut v_t_1322_: *mut LeanObject,
    mut v_h_1323_: *mut LeanObject,
    mut v_unsat_1324_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1325_: *mut LeanObject = core::ptr::null_mut();
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
-> *mut LeanObject {
    let mut v___x_1329_: u8 = 0;
    let mut v___x_1330_: *mut LeanObject = core::ptr::null_mut();
    v___x_1329_ = lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__0_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__0);
    v___x_1330_ = lean_uint8_to_nat(v___x_1329_);
    return v___x_1330_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__3()
-> *mut LeanObject {
    let mut v___x_1331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut LeanObject = core::ptr::null_mut();
    v___x_1331_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__2_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__2);
    v___x_1332_ = l_Nat_reprFast(v___x_1331_);
    return v___x_1332_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__4()
-> *mut LeanObject {
    let mut v___x_1333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut LeanObject = core::ptr::null_mut();
    v___x_1333_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__3_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__3);
    v___x_1334_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__1;
    v___x_1335_ = lean_string_append(v___x_1334_, v___x_1333_);
    return v___x_1335_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__6()
-> *mut LeanObject {
    let mut v___x_1337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut LeanObject = core::ptr::null_mut();
    v___x_1337_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__5;
    v___x_1338_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__4_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__4);
    v___x_1339_ = lean_string_append(v___x_1338_, v___x_1337_);
    return v___x_1339_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__7()
-> *mut LeanObject {
    let mut v___x_1340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: *mut LeanObject = core::ptr::null_mut();
    v___x_1340_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__6_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__6);
    v___x_1341_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1341_, 0, v___x_1340_);
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
-> *mut LeanObject {
    let mut v___x_1354_: u8 = 0;
    let mut v___x_1355_: *mut LeanObject = core::ptr::null_mut();
    v___x_1354_ = lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__10_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__10);
    v___x_1355_ = lean_uint8_to_nat(v___x_1354_);
    return v___x_1355_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__16()
-> *mut LeanObject {
    let mut v___x_1356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut LeanObject = core::ptr::null_mut();
    v___x_1356_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__15), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__15_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__15);
    v___x_1357_ = l_Nat_reprFast(v___x_1356_);
    return v___x_1357_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__17()
-> *mut LeanObject {
    let mut v___x_1358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut LeanObject = core::ptr::null_mut();
    v___x_1358_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__16), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__16_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__16);
    v___x_1359_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__1;
    v___x_1360_ = lean_string_append(v___x_1359_, v___x_1358_);
    return v___x_1360_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__18()
-> *mut LeanObject {
    let mut v___x_1361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut LeanObject = core::ptr::null_mut();
    v___x_1361_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__5;
    v___x_1362_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__17), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__17_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__17);
    v___x_1363_ = lean_string_append(v___x_1362_, v___x_1361_);
    return v___x_1363_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__19()
-> *mut LeanObject {
    let mut v___x_1364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut LeanObject = core::ptr::null_mut();
    v___x_1364_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__18), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__18_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__18);
    v___x_1365_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1365_, 0, v___x_1364_);
    return v___x_1365_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit(
    mut v_a_1366_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_array_1367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_1368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: u8 = 0;
    let mut v___x_1371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: u8 = 0;
    let mut v_got_1374_: u8 = 0;
    let mut v___x_1375_: u8 = 0;
    let mut v___x_1376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1380_: u8 = 0;
    let mut v___x_1381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1388_: u8 = 0;
    let mut v___x_1389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: u8 = 0;
    let mut v___x_1392_: u8 = 0;
    let mut v___x_1393_: u8 = 0;
    let mut v___x_1394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: u8 = 0;
    let mut v___x_1397_: u8 = 0;
    let mut v___x_1398_: u8 = 0;
    let mut v___x_1399_: u8 = 0;
    let mut v___x_1400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_it_x27_1401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: u32 = 0;
    let mut v___x_1403_: u8 = 0;
    let mut v___x_1404_: u8 = 0;
    let mut v___x_1405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1411_: u8 = 0;
    let mut v___x_1412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: u8 = 0;
    let mut v___x_1414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1422_: u8 = 0;
    let mut v___x_1423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: u8 = 0;
    let mut v___x_1433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_1435_: u8 = 0;
    let mut v___x_1436_: u8 = 0;
    let mut v___x_1437_: u8 = 0;
    let mut v___x_1438_: u8 = 0;
    let mut v___x_1439_: u8 = 0;
    let mut v___x_1440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_it_x27_1441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: u32 = 0;
    let mut v___x_1443_: u8 = 0;
    let mut v___x_1444_: u8 = 0;
    let mut v___x_1445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1451_: u8 = 0;
    let mut v___x_1452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: u8 = 0;
    let mut v___x_1454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1463_: u8 = 0;
    let mut v_reuseFailAlloc_1464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1465_: u8 = 0;
    let mut v_unused_1466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1467_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_1367_ = lean_ctor_get(v_a_1366_, 0);
                v_idx_1368_ = lean_ctor_get(v_a_1366_, 1);
                v___x_1369_ = lean_byte_array_size(v_array_1367_);
                v___x_1370_ = lean_nat_dec_lt(v_idx_1368_, v___x_1369_);
                if v___x_1370_ == 0 {
                    v___x_1371_ = lean_box(0);
                    v___x_1372_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_1372_, 0, v_a_1366_);
                    lean_ctor_set(v___x_1372_, 1, v___x_1371_);
                    return v___x_1372_;
                } else {
                    v___x_1373_ = lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__0_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__0);
                    v_got_1374_ = lean_byte_array_fget(v_array_1367_, v_idx_1368_);
                    v___x_1375_ = lean_uint8_dec_eq(v_got_1374_, v___x_1373_);
                    if v___x_1375_ == 0 {
                        v___x_1376_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__7_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__7);
                        v___x_1377_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_1377_, 0, v_a_1366_);
                        lean_ctor_set(v___x_1377_, 1, v___x_1376_);
                        return v___x_1377_;
                    } else {
                        lean_inc(v_idx_1368_);
                        lean_inc_ref(v_array_1367_);
                        v_isSharedCheck_1465_ = (!lean_is_exclusive(v_a_1366_)) as u8;
                        if v_isSharedCheck_1465_ == 0 {
                            v_unused_1466_ = lean_ctor_get(v_a_1366_, 1);
                            lean_dec(v_unused_1466_);
                            v_unused_1467_ = lean_ctor_get(v_a_1366_, 0);
                            lean_dec(v_unused_1467_);
                            v___x_1379_ = v_a_1366_;
                            v_isShared_1380_ = v_isSharedCheck_1465_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_a_1366_);
                            v___x_1379_ = lean_box(0);
                            v_isShared_1380_ = v_isSharedCheck_1465_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1381_ = lean_unsigned_to_nat(1);
                v___x_1382_ = lean_nat_add(v_idx_1368_, v___x_1381_);
                lean_dec(v_idx_1368_);
                lean_inc(v___x_1382_);
                lean_inc_ref(v_array_1367_);
                if v_isShared_1380_ == 0 {
                    lean_ctor_set(v___x_1379_, 1, v___x_1382_);
                    v___x_1384_ = v___x_1379_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1464_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_array_1367_);
                    lean_ctor_set(v_reuseFailAlloc_1464_, 1, v___x_1382_);
                    v___x_1384_ = v_reuseFailAlloc_1464_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1388_ = lean_nat_dec_lt(v___x_1382_, v___x_1369_);
                if v___x_1388_ == 0 {
                    lean_dec(v___x_1382_);
                    lean_dec_ref(v_array_1367_);
                    v___x_1389_ = lean_box(0);
                    v___x_1390_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_1390_, 0, v___x_1384_);
                    lean_ctor_set(v___x_1390_, 1, v___x_1389_);
                    return v___x_1390_;
                } else {
                    v___x_1391_ = lean_byte_array_fget(v_array_1367_, v___x_1382_);
                    v___x_1392_ = lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__10_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__10);
                    v___x_1393_ = lean_uint8_dec_eq(v___x_1391_, v___x_1392_);
                    if v___x_1393_ == 0 {
                        if v___x_1388_ == 0 {
                            lean_dec(v___x_1382_);
                            lean_dec_ref(v_array_1367_);
                            v___x_1394_ = lean_box(0);
                            v___x_1395_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v___x_1395_, 0, v___x_1384_);
                            lean_ctor_set(v___x_1395_, 1, v___x_1394_);
                            return v___x_1395_;
                        } else {
                            v___x_1396_ = lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__11_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__11);
                            v___x_1397_ = lean_uint8_dec_le(v___x_1396_, v___x_1391_);
                            if v___x_1397_ == 0 {
                                lean_dec(v___x_1382_);
                                lean_dec_ref(v_array_1367_);
                                state = 3;
                                continue;
                            } else {
                                v___x_1398_ = lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__12), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__12_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__12);
                                v___x_1399_ = lean_uint8_dec_le(v___x_1391_, v___x_1398_);
                                if v___x_1399_ == 0 {
                                    lean_dec(v___x_1382_);
                                    lean_dec_ref(v_array_1367_);
                                    state = 3;
                                    continue;
                                } else {
                                    lean_dec_ref(v___x_1384_);
                                    v___x_1400_ = lean_nat_add(v___x_1382_, v___x_1381_);
                                    lean_dec(v___x_1382_);
                                    v_it_x27_1401_ = lean_alloc_ctor(0, 2, (0) as u32);
                                    lean_ctor_set(v_it_x27_1401_, 0, v_array_1367_);
                                    lean_ctor_set(v_it_x27_1401_, 1, v___x_1400_);
                                    v___x_1402_ = lean_uint8_to_uint32(v___x_1391_);
                                    v___x_1403_ = lean_uint32_to_uint8(v___x_1402_);
                                    v___x_1404_ = lean_uint8_sub(v___x_1403_, v___x_1396_);
                                    v___x_1405_ = lean_uint8_to_nat(v___x_1404_);
                                    v___x_1406_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_1401_, v___x_1405_);
                                    v_fst_1407_ = lean_ctor_get(v___x_1406_, 0);
                                    v_snd_1408_ = lean_ctor_get(v___x_1406_, 1);
                                    v_isSharedCheck_1422_ = (!lean_is_exclusive(v___x_1406_)) as u8;
                                    if v_isSharedCheck_1422_ == 0 {
                                        v___x_1410_ = v___x_1406_;
                                        v_isShared_1411_ = v_isSharedCheck_1422_;
                                        state = 4;
                                        continue;
                                    } else {
                                        lean_inc(v_snd_1408_);
                                        lean_inc(v_fst_1407_);
                                        lean_dec(v___x_1406_);
                                        v___x_1410_ = lean_box(0);
                                        v_isShared_1411_ = v_isSharedCheck_1422_;
                                        state = 4;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        if v___x_1388_ == 0 {
                            lean_dec(v___x_1382_);
                            lean_dec_ref(v_array_1367_);
                            v___x_1423_ = lean_box(0);
                            v___x_1424_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v___x_1424_, 0, v___x_1384_);
                            lean_ctor_set(v___x_1424_, 1, v___x_1423_);
                            return v___x_1424_;
                        } else {
                            if v___x_1393_ == 0 {
                                lean_dec(v___x_1382_);
                                lean_dec_ref(v_array_1367_);
                                v___x_1425_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__19), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__19_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__19);
                                v___x_1426_ = lean_alloc_ctor(1, 2, (0) as u32);
                                lean_ctor_set(v___x_1426_, 0, v___x_1384_);
                                lean_ctor_set(v___x_1426_, 1, v___x_1425_);
                                return v___x_1426_;
                            } else {
                                lean_dec_ref(v___x_1384_);
                                v___x_1427_ = lean_nat_add(v___x_1382_, v___x_1381_);
                                lean_dec(v___x_1382_);
                                lean_inc(v___x_1427_);
                                lean_inc_ref(v_array_1367_);
                                v___x_1428_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v___x_1428_, 0, v_array_1367_);
                                lean_ctor_set(v___x_1428_, 1, v___x_1427_);
                                v___x_1432_ = lean_nat_dec_lt(v___x_1427_, v___x_1369_);
                                if v___x_1432_ == 0 {
                                    lean_dec(v___x_1427_);
                                    lean_dec_ref(v_array_1367_);
                                    v___x_1433_ = lean_box(0);
                                    v___x_1434_ = lean_alloc_ctor(1, 2, (0) as u32);
                                    lean_ctor_set(v___x_1434_, 0, v___x_1428_);
                                    lean_ctor_set(v___x_1434_, 1, v___x_1433_);
                                    return v___x_1434_;
                                } else {
                                    v_c_1435_ = lean_byte_array_fget(v_array_1367_, v___x_1427_);
                                    v___x_1436_ = lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__11_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__11);
                                    v___x_1437_ = lean_uint8_dec_le(v___x_1436_, v_c_1435_);
                                    if v___x_1437_ == 0 {
                                        lean_dec(v___x_1427_);
                                        lean_dec_ref(v_array_1367_);
                                        state = 7;
                                        continue;
                                    } else {
                                        v___x_1438_ = lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__12), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__12_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__12);
                                        v___x_1439_ = lean_uint8_dec_le(v_c_1435_, v___x_1438_);
                                        if v___x_1439_ == 0 {
                                            lean_dec(v___x_1427_);
                                            lean_dec_ref(v_array_1367_);
                                            state = 7;
                                            continue;
                                        } else {
                                            lean_dec_ref_known(v___x_1428_, 2);
                                            v___x_1440_ = lean_nat_add(v___x_1427_, v___x_1381_);
                                            lean_dec(v___x_1427_);
                                            v_it_x27_1441_ = lean_alloc_ctor(0, 2, (0) as u32);
                                            lean_ctor_set(v_it_x27_1441_, 0, v_array_1367_);
                                            lean_ctor_set(v_it_x27_1441_, 1, v___x_1440_);
                                            v___x_1442_ = lean_uint8_to_uint32(v_c_1435_);
                                            v___x_1443_ = lean_uint32_to_uint8(v___x_1442_);
                                            v___x_1444_ = lean_uint8_sub(v___x_1443_, v___x_1436_);
                                            v___x_1445_ = lean_uint8_to_nat(v___x_1444_);
                                            v___x_1446_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_1441_, v___x_1445_);
                                            v_fst_1447_ = lean_ctor_get(v___x_1446_, 0);
                                            v_snd_1448_ = lean_ctor_get(v___x_1446_, 1);
                                            v_isSharedCheck_1463_ =
                                                (!lean_is_exclusive(v___x_1446_)) as u8;
                                            if v_isSharedCheck_1463_ == 0 {
                                                v___x_1450_ = v___x_1446_;
                                                v_isShared_1451_ = v_isSharedCheck_1463_;
                                                state = 8;
                                                continue;
                                            } else {
                                                lean_inc(v_snd_1448_);
                                                lean_inc(v_fst_1447_);
                                                lean_dec(v___x_1446_);
                                                v___x_1450_ = lean_box(0);
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
                v___x_1387_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1387_, 0, v___x_1384_);
                lean_ctor_set(v___x_1387_, 1, v___x_1386_);
                return v___x_1387_;
            }
            4 => {
                v___x_1412_ = lean_unsigned_to_nat(0);
                v___x_1413_ = lean_nat_dec_eq(v_fst_1407_, v___x_1412_);
                if v___x_1413_ == 0 {
                    v___x_1414_ = lean_nat_to_int(v_fst_1407_);
                    if v_isShared_1411_ == 0 {
                        lean_ctor_set(v___x_1410_, 1, v___x_1414_);
                        lean_ctor_set(v___x_1410_, 0, v_snd_1408_);
                        v___x_1416_ = v___x_1410_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1417_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1417_, 0, v_snd_1408_);
                        lean_ctor_set(v_reuseFailAlloc_1417_, 1, v___x_1414_);
                        v___x_1416_ = v_reuseFailAlloc_1417_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_dec(v_fst_1407_);
                    v___x_1418_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__14;
                    if v_isShared_1411_ == 0 {
                        lean_ctor_set_tag(v___x_1410_, 1);
                        lean_ctor_set(v___x_1410_, 1, v___x_1418_);
                        lean_ctor_set(v___x_1410_, 0, v_snd_1408_);
                        v___x_1420_ = v___x_1410_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1421_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1421_, 0, v_snd_1408_);
                        lean_ctor_set(v_reuseFailAlloc_1421_, 1, v___x_1418_);
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
                v___x_1431_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1431_, 0, v___x_1428_);
                lean_ctor_set(v___x_1431_, 1, v___x_1430_);
                return v___x_1431_;
            }
            8 => {
                v___x_1452_ = lean_unsigned_to_nat(0);
                v___x_1453_ = lean_nat_dec_eq(v_fst_1447_, v___x_1452_);
                if v___x_1453_ == 0 {
                    v___x_1454_ = lean_nat_to_int(v_fst_1447_);
                    v___x_1455_ = lean_int_neg(v___x_1454_);
                    lean_dec(v___x_1454_);
                    if v_isShared_1451_ == 0 {
                        lean_ctor_set(v___x_1450_, 1, v___x_1455_);
                        lean_ctor_set(v___x_1450_, 0, v_snd_1448_);
                        v___x_1457_ = v___x_1450_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_1458_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1458_, 0, v_snd_1448_);
                        lean_ctor_set(v_reuseFailAlloc_1458_, 1, v___x_1455_);
                        v___x_1457_ = v_reuseFailAlloc_1458_;
                        state = 9;
                        continue;
                    }
                } else {
                    lean_dec(v_fst_1447_);
                    v___x_1459_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__14;
                    if v_isShared_1451_ == 0 {
                        lean_ctor_set_tag(v___x_1450_, 1);
                        lean_ctor_set(v___x_1450_, 1, v___x_1459_);
                        lean_ctor_set(v___x_1450_, 0, v_snd_1448_);
                        v___x_1461_ = v___x_1450_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_1462_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_snd_1448_);
                        lean_ctor_set(v_reuseFailAlloc_1462_, 1, v___x_1459_);
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
    mut v_a_1468_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1469_: *mut LeanObject = core::ptr::null_mut();
    v___x_1469_ = lean_nat_to_int(v_a_1468_);
    return v___x_1469_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__2___closed__0()
-> *mut LeanObject {
    let mut v___x_1470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: *mut LeanObject = core::ptr::null_mut();
    v___x_1470_ = lean_unsigned_to_nat(0);
    v___x_1471_ = lean_nat_to_int(v___x_1470_);
    return v___x_1471_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__2(
    mut v_idx_1472_: *mut LeanObject,
    mut v___x_1473_: *mut LeanObject,
    mut v_sz_1474_: usize,
    mut v_i_1475_: usize,
    mut v_bs_1476_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1477_: u8 = 0;
    let mut v_v_1478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: usize = 0;
    let mut v___x_1484_: usize = 0;
    let mut v___x_1485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: u8 = 0;
    let mut v___x_1489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: u8 = 0;
    let mut v___x_1493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1477_ = lean_usize_dec_lt(v_i_1475_, v_sz_1474_);
                if v___x_1477_ == 0 {
                    return v_bs_1476_;
                } else {
                    v_v_1478_ = lean_array_uget(v_bs_1476_, v_i_1475_);
                    v___x_1479_ = lean_unsigned_to_nat(0);
                    v_bs_x27_1480_ = lean_array_uset(v_bs_1476_, v_i_1475_, v___x_1479_);
                    v___x_1487_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__2___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__2___closed__0_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__2___closed__0);
                    v___x_1488_ = lean_int_dec_lt(v___x_1487_, v_v_1478_);
                    if v___x_1488_ == 0 {
                        v___x_1489_ = lean_nat_abs(v_v_1478_);
                        lean_dec(v_v_1478_);
                        v___x_1490_ = lean_box((v___x_1488_) as usize);
                        v___x_1491_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_1491_, 0, v___x_1490_);
                        lean_ctor_set(v___x_1491_, 1, v___x_1489_);
                        v___y_1482_ = v___x_1491_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1492_ = lean_nat_dec_lt(v_idx_1472_, v___x_1473_);
                        v___x_1493_ = lean_nat_abs(v_v_1478_);
                        lean_dec(v_v_1478_);
                        v___x_1494_ = lean_box((v___x_1492_) as usize);
                        v___x_1495_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_1495_, 0, v___x_1494_);
                        lean_ctor_set(v___x_1495_, 1, v___x_1493_);
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
    mut v_idx_1496_: *mut LeanObject,
    mut v___x_1497_: *mut LeanObject,
    mut v_sz_1498_: *mut LeanObject,
    mut v_i_1499_: *mut LeanObject,
    mut v_bs_1500_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1501_: usize = 0;
    let mut v_i_boxed_1502_: usize = 0;
    let mut v_res_1503_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1501_ = lean_unbox_usize(v_sz_1498_);
    lean_dec(v_sz_1498_);
    v_i_boxed_1502_ = lean_unbox_usize(v_i_1499_);
    lean_dec(v_i_1499_);
    v_res_1503_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__2(v_idx_1496_, v___x_1497_, v_sz_boxed_1501_, v_i_boxed_1502_, v_bs_1500_);
    lean_dec(v___x_1497_);
    lean_dec(v_idx_1496_);
    return v_res_1503_;
}
pub unsafe fn l_Std_Internal_Parsec_manyCore___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__1(
    mut v_acc_1504_: *mut LeanObject,
    mut v_a_1505_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pos_1507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_1508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_array_1511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_1512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_1514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_1515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_1516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: u8 = 0;
    let mut v___x_1518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: u8 = 0;
    let mut v___x_1526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: u8 = 0;
    let mut v_got_1528_: u8 = 0;
    let mut v___x_1529_: u8 = 0;
    let mut v___x_1530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: u8 = 0;
    let mut v___x_1534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: u8 = 0;
    let mut v___x_1536_: u8 = 0;
    let mut v___x_1537_: u8 = 0;
    let mut v___x_1538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: u8 = 0;
    let mut v___x_1540_: u8 = 0;
    let mut v___x_1541_: u8 = 0;
    let mut v___x_1542_: u8 = 0;
    let mut v___x_1543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_it_x27_1544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: u32 = 0;
    let mut v___x_1546_: u8 = 0;
    let mut v___x_1547_: u8 = 0;
    let mut v___x_1548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: u8 = 0;
    let mut v___x_1554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: u8 = 0;
    let mut v___x_1560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_1561_: u8 = 0;
    let mut v___x_1562_: u8 = 0;
    let mut v___x_1563_: u8 = 0;
    let mut v___x_1564_: u8 = 0;
    let mut v___x_1565_: u8 = 0;
    let mut v___x_1566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_it_x27_1567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: u32 = 0;
    let mut v___x_1569_: u8 = 0;
    let mut v___x_1570_: u8 = 0;
    let mut v___x_1571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: u8 = 0;
    let mut v___x_1577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_1511_ = lean_ctor_get(v_a_1505_, 0);
                v_idx_1512_ = lean_ctor_get(v_a_1505_, 1);
                lean_inc(v_idx_1512_);
                v___x_1524_ = lean_byte_array_size(v_array_1511_);
                v___x_1525_ = lean_nat_dec_lt(v_idx_1512_, v___x_1524_);
                if v___x_1525_ == 0 {
                    v___x_1526_ = lean_box(0);
                    lean_inc(v_idx_1512_);
                    v_pos_1514_ = v_a_1505_;
                    v_idx_1515_ = v_idx_1512_;
                    v_err_1516_ = v___x_1526_;
                    state = 2;
                    continue;
                } else {
                    v___x_1527_ = lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__0_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__0);
                    v_got_1528_ = lean_byte_array_fget(v_array_1511_, v_idx_1512_);
                    v___x_1529_ = lean_uint8_dec_eq(v_got_1528_, v___x_1527_);
                    if v___x_1529_ == 0 {
                        v___x_1530_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__7_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__7);
                        lean_inc(v_idx_1512_);
                        v_pos_1514_ = v_a_1505_;
                        v_idx_1515_ = v_idx_1512_;
                        v_err_1516_ = v___x_1530_;
                        state = 2;
                        continue;
                    } else {
                        v___x_1531_ = lean_unsigned_to_nat(1);
                        v___x_1532_ = lean_nat_add(v_idx_1512_, v___x_1531_);
                        v___x_1533_ = lean_nat_dec_lt(v___x_1532_, v___x_1524_);
                        if v___x_1533_ == 0 {
                            lean_dec(v___x_1532_);
                            v___x_1534_ = lean_box(0);
                            lean_inc(v_idx_1512_);
                            v_pos_1514_ = v_a_1505_;
                            v_idx_1515_ = v_idx_1512_;
                            v_err_1516_ = v___x_1534_;
                            state = 2;
                            continue;
                        } else {
                            v___x_1535_ = lean_byte_array_fget(v_array_1511_, v___x_1532_);
                            v___x_1536_ = lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__10_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__10);
                            v___x_1537_ = lean_uint8_dec_eq(v___x_1535_, v___x_1536_);
                            if v___x_1537_ == 0 {
                                if v___x_1533_ == 0 {
                                    lean_dec(v___x_1532_);
                                    v___x_1538_ = lean_box(0);
                                    lean_inc(v_idx_1512_);
                                    v_pos_1514_ = v_a_1505_;
                                    v_idx_1515_ = v_idx_1512_;
                                    v_err_1516_ = v___x_1538_;
                                    state = 2;
                                    continue;
                                } else {
                                    v___x_1539_ = lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__11_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__11);
                                    v___x_1540_ = lean_uint8_dec_le(v___x_1539_, v___x_1535_);
                                    if v___x_1540_ == 0 {
                                        lean_dec(v___x_1532_);
                                        state = 4;
                                        continue;
                                    } else {
                                        v___x_1541_ = lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__12), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__12_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__12);
                                        v___x_1542_ = lean_uint8_dec_le(v___x_1535_, v___x_1541_);
                                        if v___x_1542_ == 0 {
                                            lean_dec(v___x_1532_);
                                            state = 4;
                                            continue;
                                        } else {
                                            v___x_1543_ = lean_nat_add(v___x_1532_, v___x_1531_);
                                            lean_dec(v___x_1532_);
                                            lean_inc_ref(v_array_1511_);
                                            v_it_x27_1544_ = lean_alloc_ctor(0, 2, (0) as u32);
                                            lean_ctor_set(v_it_x27_1544_, 0, v_array_1511_);
                                            lean_ctor_set(v_it_x27_1544_, 1, v___x_1543_);
                                            v___x_1545_ = lean_uint8_to_uint32(v___x_1535_);
                                            v___x_1546_ = lean_uint32_to_uint8(v___x_1545_);
                                            v___x_1547_ = lean_uint8_sub(v___x_1546_, v___x_1539_);
                                            v___x_1548_ = lean_uint8_to_nat(v___x_1547_);
                                            v___x_1549_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_1544_, v___x_1548_);
                                            v_fst_1550_ = lean_ctor_get(v___x_1549_, 0);
                                            lean_inc(v_fst_1550_);
                                            v_snd_1551_ = lean_ctor_get(v___x_1549_, 1);
                                            lean_inc(v_snd_1551_);
                                            lean_dec_ref(v___x_1549_);
                                            v___x_1552_ = lean_unsigned_to_nat(0);
                                            v___x_1553_ = lean_nat_dec_eq(v_fst_1550_, v___x_1552_);
                                            if v___x_1553_ == 0 {
                                                lean_dec(v_idx_1512_);
                                                lean_dec_ref(v_a_1505_);
                                                v___x_1554_ = lean_nat_to_int(v_fst_1550_);
                                                v_pos_1507_ = v_snd_1551_;
                                                v_res_1508_ = v___x_1554_;
                                                state = 1;
                                                continue;
                                            } else {
                                                lean_dec(v_snd_1551_);
                                                lean_dec(v_fst_1550_);
                                                v___x_1555_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__14;
                                                lean_inc(v_idx_1512_);
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
                                    lean_dec(v___x_1532_);
                                    v___x_1556_ = lean_box(0);
                                    lean_inc(v_idx_1512_);
                                    v_pos_1514_ = v_a_1505_;
                                    v_idx_1515_ = v_idx_1512_;
                                    v_err_1516_ = v___x_1556_;
                                    state = 2;
                                    continue;
                                } else {
                                    if v___x_1537_ == 0 {
                                        lean_dec(v___x_1532_);
                                        v___x_1557_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__19), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__19_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__19);
                                        lean_inc(v_idx_1512_);
                                        v_pos_1514_ = v_a_1505_;
                                        v_idx_1515_ = v_idx_1512_;
                                        v_err_1516_ = v___x_1557_;
                                        state = 2;
                                        continue;
                                    } else {
                                        v___x_1558_ = lean_nat_add(v___x_1532_, v___x_1531_);
                                        lean_dec(v___x_1532_);
                                        v___x_1559_ = lean_nat_dec_lt(v___x_1558_, v___x_1524_);
                                        if v___x_1559_ == 0 {
                                            lean_dec(v___x_1558_);
                                            v___x_1560_ = lean_box(0);
                                            lean_inc(v_idx_1512_);
                                            v_pos_1514_ = v_a_1505_;
                                            v_idx_1515_ = v_idx_1512_;
                                            v_err_1516_ = v___x_1560_;
                                            state = 2;
                                            continue;
                                        } else {
                                            v_c_1561_ =
                                                lean_byte_array_fget(v_array_1511_, v___x_1558_);
                                            v___x_1562_ = lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__11_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__11);
                                            v___x_1563_ = lean_uint8_dec_le(v___x_1562_, v_c_1561_);
                                            if v___x_1563_ == 0 {
                                                lean_dec(v___x_1558_);
                                                state = 3;
                                                continue;
                                            } else {
                                                v___x_1564_ = lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__12), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__12_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__12);
                                                v___x_1565_ =
                                                    lean_uint8_dec_le(v_c_1561_, v___x_1564_);
                                                if v___x_1565_ == 0 {
                                                    lean_dec(v___x_1558_);
                                                    state = 3;
                                                    continue;
                                                } else {
                                                    v___x_1566_ =
                                                        lean_nat_add(v___x_1558_, v___x_1531_);
                                                    lean_dec(v___x_1558_);
                                                    lean_inc_ref(v_array_1511_);
                                                    v_it_x27_1567_ =
                                                        lean_alloc_ctor(0, 2, (0) as u32);
                                                    lean_ctor_set(v_it_x27_1567_, 0, v_array_1511_);
                                                    lean_ctor_set(v_it_x27_1567_, 1, v___x_1566_);
                                                    v___x_1568_ = lean_uint8_to_uint32(v_c_1561_);
                                                    v___x_1569_ = lean_uint32_to_uint8(v___x_1568_);
                                                    v___x_1570_ =
                                                        lean_uint8_sub(v___x_1569_, v___x_1562_);
                                                    v___x_1571_ = lean_uint8_to_nat(v___x_1570_);
                                                    v___x_1572_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_1567_, v___x_1571_);
                                                    v_fst_1573_ = lean_ctor_get(v___x_1572_, 0);
                                                    lean_inc(v_fst_1573_);
                                                    v_snd_1574_ = lean_ctor_get(v___x_1572_, 1);
                                                    lean_inc(v_snd_1574_);
                                                    lean_dec_ref(v___x_1572_);
                                                    v___x_1575_ = lean_unsigned_to_nat(0);
                                                    v___x_1576_ =
                                                        lean_nat_dec_eq(v_fst_1573_, v___x_1575_);
                                                    if v___x_1576_ == 0 {
                                                        lean_dec(v_idx_1512_);
                                                        lean_dec_ref(v_a_1505_);
                                                        v___x_1577_ = lean_nat_to_int(v_fst_1573_);
                                                        v___x_1578_ = lean_int_neg(v___x_1577_);
                                                        lean_dec(v___x_1577_);
                                                        v_pos_1507_ = v_snd_1574_;
                                                        v_res_1508_ = v___x_1578_;
                                                        state = 1;
                                                        continue;
                                                    } else {
                                                        lean_dec(v_snd_1574_);
                                                        lean_dec(v_fst_1573_);
                                                        v___x_1579_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__14;
                                                        lean_inc(v_idx_1512_);
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
                lean_dec(v_idx_1515_);
                lean_dec(v_idx_1512_);
                if v___x_1517_ == 0 {
                    lean_dec_ref(v_acc_1504_);
                    lean_inc(v_err_1516_);
                    v___x_1518_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_1518_, 0, v_pos_1514_);
                    lean_ctor_set(v___x_1518_, 1, v_err_1516_);
                    return v___x_1518_;
                } else {
                    v___x_1519_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1519_, 0, v_pos_1514_);
                    lean_ctor_set(v___x_1519_, 1, v_acc_1504_);
                    return v___x_1519_;
                }
            }
            3 => {
                v___x_1521_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__9;
                lean_inc(v_idx_1512_);
                v_pos_1514_ = v_a_1505_;
                v_idx_1515_ = v_idx_1512_;
                v_err_1516_ = v___x_1521_;
                state = 2;
                continue;
            }
            4 => {
                v___x_1523_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__9;
                lean_inc(v_idx_1512_);
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
-> *mut LeanObject {
    let mut v___x_1582_: u8 = 0;
    let mut v___x_1583_: *mut LeanObject = core::ptr::null_mut();
    v___x_1582_ = lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__0_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__0);
    v___x_1583_ = lean_uint8_to_nat(v___x_1582_);
    return v___x_1583_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__2()
-> *mut LeanObject {
    let mut v___x_1584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut LeanObject = core::ptr::null_mut();
    v___x_1584_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__1_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__1);
    v___x_1585_ = l_Nat_reprFast(v___x_1584_);
    return v___x_1585_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__3()
-> *mut LeanObject {
    let mut v___x_1586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut LeanObject = core::ptr::null_mut();
    v___x_1586_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__2_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__2);
    v___x_1587_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__1;
    v___x_1588_ = lean_string_append(v___x_1587_, v___x_1586_);
    return v___x_1588_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__4()
-> *mut LeanObject {
    let mut v___x_1589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut LeanObject = core::ptr::null_mut();
    v___x_1589_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__5;
    v___x_1590_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__3_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__3);
    v___x_1591_ = lean_string_append(v___x_1590_, v___x_1589_);
    return v___x_1591_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__5()
-> *mut LeanObject {
    let mut v___x_1592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut LeanObject = core::ptr::null_mut();
    v___x_1592_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__4_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__4);
    v___x_1593_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1593_, 0, v___x_1592_);
    return v___x_1593_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__8()
-> *mut LeanObject {
    let mut v___x_1597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_utf8_1598_: *mut LeanObject = core::ptr::null_mut();
    v___x_1597_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__7;
    v_utf8_1598_ = lean_string_to_utf8(v___x_1597_);
    return v_utf8_1598_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__10()
-> *mut LeanObject {
    let mut v___x_1600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_utf8_1601_: *mut LeanObject = core::ptr::null_mut();
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
-> *mut LeanObject {
    let mut v___x_1604_: u8 = 0;
    let mut v___x_1605_: *mut LeanObject = core::ptr::null_mut();
    v___x_1604_ = lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__11_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__11);
    v___x_1605_ = lean_uint8_to_nat(v___x_1604_);
    return v___x_1605_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__13()
-> *mut LeanObject {
    let mut v___x_1606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut LeanObject = core::ptr::null_mut();
    v___x_1606_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__12), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__12_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__12);
    v___x_1607_ = l_Nat_reprFast(v___x_1606_);
    return v___x_1607_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__14()
-> *mut LeanObject {
    let mut v___x_1608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut LeanObject = core::ptr::null_mut();
    v___x_1608_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__13), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__13_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__13);
    v___x_1609_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__1;
    v___x_1610_ = lean_string_append(v___x_1609_, v___x_1608_);
    return v___x_1610_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__15()
-> *mut LeanObject {
    let mut v___x_1611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1613_: *mut LeanObject = core::ptr::null_mut();
    v___x_1611_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__5;
    v___x_1612_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__14), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__14_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__14);
    v___x_1613_ = lean_string_append(v___x_1612_, v___x_1611_);
    return v___x_1613_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__16()
-> *mut LeanObject {
    let mut v___x_1614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut LeanObject = core::ptr::null_mut();
    v___x_1614_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__15), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__15_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__15);
    v___x_1615_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1615_, 0, v___x_1614_);
    return v___x_1615_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment(
    mut v_a_1616_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_array_1617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_1618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: u8 = 0;
    let mut v___x_1621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: u8 = 0;
    let mut v_got_1624_: u8 = 0;
    let mut v___x_1625_: u8 = 0;
    let mut v___x_1626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1630_: u8 = 0;
    let mut v___x_1631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_1637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_1638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1641_: u8 = 0;
    let mut v_sz_1642_: usize = 0;
    let mut v___x_1643_: usize = 0;
    let mut v___x_1644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_1646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_1653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: u8 = 0;
    let mut v___x_1655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_1660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_1661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_1662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1665_: u8 = 0;
    let mut v___x_1667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1669_: u8 = 0;
    let mut v_utf8_1670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_1672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_1673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_1674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_1675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1678_: u8 = 0;
    let mut v_idx_1679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_array_1680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_1681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_1684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_1685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: u8 = 0;
    let mut v_utf8_1687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_1689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: u8 = 0;
    let mut v___x_1692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: u8 = 0;
    let mut v___x_1696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: u8 = 0;
    let mut v_got_1701_: u8 = 0;
    let mut v___x_1702_: u8 = 0;
    let mut v___x_1703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1709_: u8 = 0;
    let mut v___x_1710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1714_: u8 = 0;
    let mut v_unused_1715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1717_: u8 = 0;
    let mut v_isSharedCheck_1718_: u8 = 0;
    let mut v_pos_1719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_1720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1723_: u8 = 0;
    let mut v___x_1725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1727_: u8 = 0;
    let mut v_reuseFailAlloc_1728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1729_: u8 = 0;
    let mut v_unused_1730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1731_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_1617_ = lean_ctor_get(v_a_1616_, 0);
                v_idx_1618_ = lean_ctor_get(v_a_1616_, 1);
                v___x_1619_ = lean_byte_array_size(v_array_1617_);
                v___x_1620_ = lean_nat_dec_lt(v_idx_1618_, v___x_1619_);
                if v___x_1620_ == 0 {
                    v___x_1621_ = lean_box(0);
                    v___x_1622_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_1622_, 0, v_a_1616_);
                    lean_ctor_set(v___x_1622_, 1, v___x_1621_);
                    return v___x_1622_;
                } else {
                    v___x_1623_ = lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__0_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__0);
                    v_got_1624_ = lean_byte_array_fget(v_array_1617_, v_idx_1618_);
                    v___x_1625_ = lean_uint8_dec_eq(v_got_1624_, v___x_1623_);
                    if v___x_1625_ == 0 {
                        v___x_1626_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__5_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__5);
                        v___x_1627_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_1627_, 0, v_a_1616_);
                        lean_ctor_set(v___x_1627_, 1, v___x_1626_);
                        return v___x_1627_;
                    } else {
                        lean_inc(v_idx_1618_);
                        lean_inc_ref(v_array_1617_);
                        v_isSharedCheck_1729_ = (!lean_is_exclusive(v_a_1616_)) as u8;
                        if v_isSharedCheck_1729_ == 0 {
                            v_unused_1730_ = lean_ctor_get(v_a_1616_, 1);
                            lean_dec(v_unused_1730_);
                            v_unused_1731_ = lean_ctor_get(v_a_1616_, 0);
                            lean_dec(v_unused_1731_);
                            v___x_1629_ = v_a_1616_;
                            v_isShared_1630_ = v_isSharedCheck_1729_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_a_1616_);
                            v___x_1629_ = lean_box(0);
                            v_isShared_1630_ = v_isSharedCheck_1729_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1631_ = lean_unsigned_to_nat(1);
                v___x_1632_ = lean_nat_add(v_idx_1618_, v___x_1631_);
                if v_isShared_1630_ == 0 {
                    lean_ctor_set(v___x_1629_, 1, v___x_1632_);
                    v___x_1634_ = v___x_1629_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1728_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1728_, 0, v_array_1617_);
                    lean_ctor_set(v_reuseFailAlloc_1728_, 1, v___x_1632_);
                    v___x_1634_ = v_reuseFailAlloc_1728_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1635_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__6;
                v___x_1636_ = l_Std_Internal_Parsec_manyCore___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__1(v___x_1635_, v___x_1634_);
                if lean_obj_tag(v___x_1636_) == 0 {
                    v_pos_1637_ = lean_ctor_get(v___x_1636_, 0);
                    v_res_1638_ = lean_ctor_get(v___x_1636_, 1);
                    v_isSharedCheck_1718_ = (!lean_is_exclusive(v___x_1636_)) as u8;
                    if v_isSharedCheck_1718_ == 0 {
                        v___x_1640_ = v___x_1636_;
                        v_isShared_1641_ = v_isSharedCheck_1718_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_res_1638_);
                        lean_inc(v_pos_1637_);
                        lean_dec(v___x_1636_);
                        v___x_1640_ = lean_box(0);
                        v_isShared_1641_ = v_isSharedCheck_1718_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_idx_1618_);
                    v_pos_1719_ = lean_ctor_get(v___x_1636_, 0);
                    v_err_1720_ = lean_ctor_get(v___x_1636_, 1);
                    v_isSharedCheck_1727_ = (!lean_is_exclusive(v___x_1636_)) as u8;
                    if v_isSharedCheck_1727_ == 0 {
                        v___x_1722_ = v___x_1636_;
                        v_isShared_1723_ = v_isSharedCheck_1727_;
                        state = 17;
                        continue;
                    } else {
                        lean_inc(v_err_1720_);
                        lean_inc(v_pos_1719_);
                        lean_dec(v___x_1636_);
                        v___x_1722_ = lean_box(0);
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
                lean_dec(v_idx_1618_);
                v_utf8_1670_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__8_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__8);
                lean_inc(v_pos_1637_);
                v___x_1671_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_1670_, v_pos_1637_);
                if lean_obj_tag(v___x_1671_) == 0 {
                    lean_dec(v_pos_1637_);
                    v_pos_1672_ = lean_ctor_get(v___x_1671_, 0);
                    lean_inc(v_pos_1672_);
                    lean_dec_ref_known(v___x_1671_, 2);
                    v_pos_1646_ = v_pos_1672_;
                    state = 4;
                    continue;
                } else {
                    if lean_obj_tag(v___x_1671_) == 0 {
                        lean_dec(v_pos_1637_);
                        v_pos_1673_ = lean_ctor_get(v___x_1671_, 0);
                        lean_inc(v_pos_1673_);
                        lean_dec_ref_known(v___x_1671_, 2);
                        v_pos_1646_ = v_pos_1673_;
                        state = 4;
                        continue;
                    } else {
                        lean_del_object(v___x_1640_);
                        v_pos_1674_ = lean_ctor_get(v___x_1671_, 0);
                        v_err_1675_ = lean_ctor_get(v___x_1671_, 1);
                        v_isSharedCheck_1717_ = (!lean_is_exclusive(v___x_1671_)) as u8;
                        if v_isSharedCheck_1717_ == 0 {
                            v___x_1677_ = v___x_1671_;
                            v_isShared_1678_ = v_isSharedCheck_1717_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_err_1675_);
                            lean_inc(v_pos_1674_);
                            lean_dec(v___x_1671_);
                            v___x_1677_ = lean_box(0);
                            v_isShared_1678_ = v_isSharedCheck_1717_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            4 => {
                v___x_1647_ = lean_box((v___x_1620_) as usize);
                v___x_1648_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1648_, 0, v___x_1647_);
                lean_ctor_set(v___x_1648_, 1, v___x_1644_);
                if v_isShared_1641_ == 0 {
                    lean_ctor_set(v___x_1640_, 1, v___x_1648_);
                    lean_ctor_set(v___x_1640_, 0, v_pos_1646_);
                    v___x_1650_ = v___x_1640_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1651_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1651_, 0, v_pos_1646_);
                    lean_ctor_set(v_reuseFailAlloc_1651_, 1, v___x_1648_);
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
                v___x_1655_ = lean_box((v___x_1654_) as usize);
                v___x_1656_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1656_, 0, v___x_1655_);
                lean_ctor_set(v___x_1656_, 1, v___x_1644_);
                v___x_1657_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1657_, 0, v_pos_1653_);
                lean_ctor_set(v___x_1657_, 1, v___x_1656_);
                return v___x_1657_;
            }
            7 => {
                if lean_obj_tag(v___y_1659_) == 0 {
                    v_pos_1660_ = lean_ctor_get(v___y_1659_, 0);
                    lean_inc(v_pos_1660_);
                    lean_dec_ref_known(v___y_1659_, 2);
                    v_pos_1653_ = v_pos_1660_;
                    state = 6;
                    continue;
                } else {
                    lean_dec_ref(v___x_1644_);
                    v_pos_1661_ = lean_ctor_get(v___y_1659_, 0);
                    v_err_1662_ = lean_ctor_get(v___y_1659_, 1);
                    v_isSharedCheck_1669_ = (!lean_is_exclusive(v___y_1659_)) as u8;
                    if v_isSharedCheck_1669_ == 0 {
                        v___x_1664_ = v___y_1659_;
                        v_isShared_1665_ = v_isSharedCheck_1669_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_err_1662_);
                        lean_inc(v_pos_1661_);
                        lean_dec(v___y_1659_);
                        v___x_1664_ = lean_box(0);
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
                    v_reuseFailAlloc_1668_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_pos_1661_);
                    lean_ctor_set(v_reuseFailAlloc_1668_, 1, v_err_1662_);
                    v___x_1667_ = v_reuseFailAlloc_1668_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1667_;
            }
            10 => {
                v_idx_1679_ = lean_ctor_get(v_pos_1637_, 1);
                lean_inc(v_idx_1679_);
                lean_dec(v_pos_1637_);
                v_array_1680_ = lean_ctor_get(v_pos_1674_, 0);
                v_idx_1681_ = lean_ctor_get(v_pos_1674_, 1);
                v___x_1690_ = lean_nat_dec_eq(v_idx_1679_, v_idx_1681_);
                lean_dec(v_idx_1679_);
                if v___x_1690_ == 0 {
                    lean_dec_ref(v___x_1644_);
                    if v_isShared_1678_ == 0 {
                        v___x_1692_ = v___x_1677_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_1693_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1693_, 0, v_pos_1674_);
                        lean_ctor_set(v_reuseFailAlloc_1693_, 1, v_err_1675_);
                        v___x_1692_ = v_reuseFailAlloc_1693_;
                        state = 12;
                        continue;
                    }
                } else {
                    lean_inc(v_idx_1681_);
                    lean_dec(v_err_1675_);
                    v___x_1694_ = lean_byte_array_size(v_array_1680_);
                    v___x_1695_ = lean_nat_dec_lt(v_idx_1681_, v___x_1694_);
                    if v___x_1695_ == 0 {
                        v___x_1696_ = lean_box(0);
                        lean_inc(v_pos_1674_);
                        if v_isShared_1678_ == 0 {
                            lean_ctor_set(v___x_1677_, 1, v___x_1696_);
                            v___x_1698_ = v___x_1677_;
                            state = 13;
                            continue;
                        } else {
                            v_reuseFailAlloc_1699_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1699_, 0, v_pos_1674_);
                            lean_ctor_set(v_reuseFailAlloc_1699_, 1, v___x_1696_);
                            v___x_1698_ = v_reuseFailAlloc_1699_;
                            state = 13;
                            continue;
                        }
                    } else {
                        v___x_1700_ = lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__11_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__11);
                        v_got_1701_ = lean_byte_array_fget(v_array_1680_, v_idx_1681_);
                        v___x_1702_ = lean_uint8_dec_eq(v_got_1701_, v___x_1700_);
                        if v___x_1702_ == 0 {
                            v___x_1703_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__16), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__16_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__16);
                            lean_inc(v_pos_1674_);
                            if v_isShared_1678_ == 0 {
                                lean_ctor_set(v___x_1677_, 1, v___x_1703_);
                                v___x_1705_ = v___x_1677_;
                                state = 14;
                                continue;
                            } else {
                                v_reuseFailAlloc_1706_ = lean_alloc_ctor(1, 2, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_1706_, 0, v_pos_1674_);
                                lean_ctor_set(v_reuseFailAlloc_1706_, 1, v___x_1703_);
                                v___x_1705_ = v_reuseFailAlloc_1706_;
                                state = 14;
                                continue;
                            }
                        } else {
                            lean_inc_ref(v_array_1680_);
                            lean_del_object(v___x_1677_);
                            v_isSharedCheck_1714_ = (!lean_is_exclusive(v_pos_1674_)) as u8;
                            if v_isSharedCheck_1714_ == 0 {
                                v_unused_1715_ = lean_ctor_get(v_pos_1674_, 1);
                                lean_dec(v_unused_1715_);
                                v_unused_1716_ = lean_ctor_get(v_pos_1674_, 0);
                                lean_dec(v_unused_1716_);
                                v___x_1708_ = v_pos_1674_;
                                v_isShared_1709_ = v_isSharedCheck_1714_;
                                state = 15;
                                continue;
                            } else {
                                lean_dec(v_pos_1674_);
                                v___x_1708_ = lean_box(0);
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
                lean_dec(v_idx_1685_);
                lean_dec(v_idx_1681_);
                if v___x_1686_ == 0 {
                    lean_dec_ref(v_pos_1684_);
                    v___y_1659_ = v___y_1683_;
                    state = 7;
                    continue;
                } else {
                    lean_dec_ref(v___y_1683_);
                    v_utf8_1687_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__10_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__10);
                    v___x_1688_ =
                        l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_1687_, v_pos_1684_);
                    if lean_obj_tag(v___x_1688_) == 0 {
                        v_pos_1689_ = lean_ctor_get(v___x_1688_, 0);
                        lean_inc(v_pos_1689_);
                        lean_dec_ref_known(v___x_1688_, 2);
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
                lean_inc(v_idx_1681_);
                v___y_1683_ = v___x_1698_;
                v_pos_1684_ = v_pos_1674_;
                v_idx_1685_ = v_idx_1681_;
                state = 11;
                continue;
            }
            14 => {
                lean_inc(v_idx_1681_);
                v___y_1683_ = v___x_1705_;
                v_pos_1684_ = v_pos_1674_;
                v_idx_1685_ = v_idx_1681_;
                state = 11;
                continue;
            }
            15 => {
                v___x_1710_ = lean_nat_add(v_idx_1681_, v___x_1631_);
                lean_dec(v_idx_1681_);
                if v_isShared_1709_ == 0 {
                    lean_ctor_set(v___x_1708_, 1, v___x_1710_);
                    v___x_1712_ = v___x_1708_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1713_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1713_, 0, v_array_1680_);
                    lean_ctor_set(v_reuseFailAlloc_1713_, 1, v___x_1710_);
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
                    v_reuseFailAlloc_1726_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1726_, 0, v_pos_1719_);
                    lean_ctor_set(v_reuseFailAlloc_1726_, 1, v_err_1720_);
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
    mut v_acc_1732_: *mut LeanObject,
    mut v_a_1733_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_1735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_1736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1739_: u8 = 0;
    let mut v_fst_1740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: u8 = 0;
    let mut v___x_1746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1748_: u8 = 0;
    let mut v_pos_1749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_1750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1753_: u8 = 0;
    let mut v___x_1755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1757_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1734_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment(v_a_1733_);
                if lean_obj_tag(v___x_1734_) == 0 {
                    v_res_1735_ = lean_ctor_get(v___x_1734_, 1);
                    v_pos_1736_ = lean_ctor_get(v___x_1734_, 0);
                    v_isSharedCheck_1748_ = (!lean_is_exclusive(v___x_1734_)) as u8;
                    if v_isSharedCheck_1748_ == 0 {
                        v___x_1738_ = v___x_1734_;
                        v_isShared_1739_ = v_isSharedCheck_1748_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_res_1735_);
                        lean_inc(v_pos_1736_);
                        lean_dec(v___x_1734_);
                        v___x_1738_ = lean_box(0);
                        v_isShared_1739_ = v_isSharedCheck_1748_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_acc_1732_);
                    v_pos_1749_ = lean_ctor_get(v___x_1734_, 0);
                    v_err_1750_ = lean_ctor_get(v___x_1734_, 1);
                    v_isSharedCheck_1757_ = (!lean_is_exclusive(v___x_1734_)) as u8;
                    if v_isSharedCheck_1757_ == 0 {
                        v___x_1752_ = v___x_1734_;
                        v_isShared_1753_ = v_isSharedCheck_1757_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_err_1750_);
                        lean_inc(v_pos_1749_);
                        lean_dec(v___x_1734_);
                        v___x_1752_ = lean_box(0);
                        v_isShared_1753_ = v_isSharedCheck_1757_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1740_ = lean_ctor_get(v_res_1735_, 0);
                lean_inc(v_fst_1740_);
                v_snd_1741_ = lean_ctor_get(v_res_1735_, 1);
                lean_inc(v_snd_1741_);
                lean_dec(v_res_1735_);
                v___x_1742_ = l_Array_append___redArg(v_acc_1732_, v_snd_1741_);
                lean_dec(v_snd_1741_);
                v___x_1743_ = (lean_unbox(v_fst_1740_) as u8);
                lean_dec(v_fst_1740_);
                if v___x_1743_ == 0 {
                    lean_del_object(v___x_1738_);
                    v_acc_1732_ = v___x_1742_;
                    v_a_1733_ = v_pos_1736_;
                    state = 0;
                    continue;
                } else {
                    if v_isShared_1739_ == 0 {
                        lean_ctor_set(v___x_1738_, 1, v___x_1742_);
                        v___x_1746_ = v___x_1738_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1747_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1747_, 0, v_pos_1736_);
                        lean_ctor_set(v_reuseFailAlloc_1747_, 1, v___x_1742_);
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
                    v_reuseFailAlloc_1756_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1756_, 0, v_pos_1749_);
                    lean_ctor_set(v_reuseFailAlloc_1756_, 1, v_err_1750_);
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
    mut v_a_1760_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut LeanObject = core::ptr::null_mut();
    v___x_1761_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseLines___closed__0;
    v___x_1762_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseLines_go(v___x_1761_, v_a_1760_);
    return v___x_1762_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseHeader___closed__1()
-> *mut LeanObject {
    let mut v___x_1764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_utf8_1765_: *mut LeanObject = core::ptr::null_mut();
    v___x_1764_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseHeader___closed__0;
    v_utf8_1765_ = lean_string_to_utf8(v___x_1764_);
    return v_utf8_1765_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseHeader(
    mut v_a_1766_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_idx_1768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_1770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_1771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: u8 = 0;
    let mut v_utf8_1773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_1775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1778_: u8 = 0;
    let mut v___x_1779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1783_: u8 = 0;
    let mut v_unused_1784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_1786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_array_1787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_1788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: u8 = 0;
    let mut v___x_1791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: u8 = 0;
    let mut v_got_1794_: u8 = 0;
    let mut v___x_1795_: u8 = 0;
    let mut v___x_1796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1800_: u8 = 0;
    let mut v___x_1801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1808_: u8 = 0;
    let mut v_unused_1809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_utf8_1811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_1813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_1814_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_utf8_1811_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseHeader___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseHeader___closed__1_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseHeader___closed__1);
                v___x_1812_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_1811_, v_a_1766_);
                if lean_obj_tag(v___x_1812_) == 0 {
                    v_pos_1813_ = lean_ctor_get(v___x_1812_, 0);
                    lean_inc(v_pos_1813_);
                    lean_dec_ref_known(v___x_1812_, 2);
                    v_pos_1786_ = v_pos_1813_;
                    state = 4;
                    continue;
                } else {
                    if lean_obj_tag(v___x_1812_) == 0 {
                        v_pos_1814_ = lean_ctor_get(v___x_1812_, 0);
                        lean_inc(v_pos_1814_);
                        lean_dec_ref_known(v___x_1812_, 2);
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
                lean_dec(v_idx_1771_);
                lean_dec(v_idx_1768_);
                if v___x_1772_ == 0 {
                    lean_dec_ref(v_pos_1770_);
                    return v___y_1769_;
                } else {
                    lean_dec_ref(v___y_1769_);
                    v_utf8_1773_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__10_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__10);
                    v___x_1774_ =
                        l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_1773_, v_pos_1770_);
                    if lean_obj_tag(v___x_1774_) == 0 {
                        v_pos_1775_ = lean_ctor_get(v___x_1774_, 0);
                        v_isSharedCheck_1783_ = (!lean_is_exclusive(v___x_1774_)) as u8;
                        if v_isSharedCheck_1783_ == 0 {
                            v_unused_1784_ = lean_ctor_get(v___x_1774_, 1);
                            lean_dec(v_unused_1784_);
                            v___x_1777_ = v___x_1774_;
                            v_isShared_1778_ = v_isSharedCheck_1783_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_pos_1775_);
                            lean_dec(v___x_1774_);
                            v___x_1777_ = lean_box(0);
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
                v___x_1779_ = lean_box(0);
                if v_isShared_1778_ == 0 {
                    lean_ctor_set(v___x_1777_, 1, v___x_1779_);
                    v___x_1781_ = v___x_1777_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1782_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1782_, 0, v_pos_1775_);
                    lean_ctor_set(v_reuseFailAlloc_1782_, 1, v___x_1779_);
                    v___x_1781_ = v_reuseFailAlloc_1782_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1781_;
            }
            4 => {
                v_array_1787_ = lean_ctor_get(v_pos_1786_, 0);
                v_idx_1788_ = lean_ctor_get(v_pos_1786_, 1);
                lean_inc(v_idx_1788_);
                v___x_1789_ = lean_byte_array_size(v_array_1787_);
                v___x_1790_ = lean_nat_dec_lt(v_idx_1788_, v___x_1789_);
                if v___x_1790_ == 0 {
                    v___x_1791_ = lean_box(0);
                    lean_inc_ref(v_pos_1786_);
                    v___x_1792_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_1792_, 0, v_pos_1786_);
                    lean_ctor_set(v___x_1792_, 1, v___x_1791_);
                    lean_inc(v_idx_1788_);
                    v_idx_1768_ = v_idx_1788_;
                    v___y_1769_ = v___x_1792_;
                    v_pos_1770_ = v_pos_1786_;
                    v_idx_1771_ = v_idx_1788_;
                    state = 1;
                    continue;
                } else {
                    v___x_1793_ = lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__11_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__11);
                    v_got_1794_ = lean_byte_array_fget(v_array_1787_, v_idx_1788_);
                    v___x_1795_ = lean_uint8_dec_eq(v_got_1794_, v___x_1793_);
                    if v___x_1795_ == 0 {
                        v___x_1796_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__16), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__16_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__16);
                        lean_inc_ref(v_pos_1786_);
                        v___x_1797_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_1797_, 0, v_pos_1786_);
                        lean_ctor_set(v___x_1797_, 1, v___x_1796_);
                        lean_inc(v_idx_1788_);
                        v_idx_1768_ = v_idx_1788_;
                        v___y_1769_ = v___x_1797_;
                        v_pos_1770_ = v_pos_1786_;
                        v_idx_1771_ = v_idx_1788_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc_ref(v_array_1787_);
                        v_isSharedCheck_1808_ = (!lean_is_exclusive(v_pos_1786_)) as u8;
                        if v_isSharedCheck_1808_ == 0 {
                            v_unused_1809_ = lean_ctor_get(v_pos_1786_, 1);
                            lean_dec(v_unused_1809_);
                            v_unused_1810_ = lean_ctor_get(v_pos_1786_, 0);
                            lean_dec(v_unused_1810_);
                            v___x_1799_ = v_pos_1786_;
                            v_isShared_1800_ = v_isSharedCheck_1808_;
                            state = 5;
                            continue;
                        } else {
                            lean_dec(v_pos_1786_);
                            v___x_1799_ = lean_box(0);
                            v_isShared_1800_ = v_isSharedCheck_1808_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            5 => {
                v___x_1801_ = lean_unsigned_to_nat(1);
                v___x_1802_ = lean_nat_add(v_idx_1788_, v___x_1801_);
                lean_dec(v_idx_1788_);
                if v_isShared_1800_ == 0 {
                    lean_ctor_set(v___x_1799_, 1, v___x_1802_);
                    v___x_1804_ = v___x_1799_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1807_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1807_, 0, v_array_1787_);
                    lean_ctor_set(v_reuseFailAlloc_1807_, 1, v___x_1802_);
                    v___x_1804_ = v_reuseFailAlloc_1807_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_1805_ = lean_box(0);
                v___x_1806_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1806_, 0, v___x_1804_);
                lean_ctor_set(v___x_1806_, 1, v___x_1805_);
                return v___x_1806_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parse(
    mut v_a_1815_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_1818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_1820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_1821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1824_: u8 = 0;
    let mut v___x_1826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1828_: u8 = 0;
    let mut v_idx_1830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_1832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_1833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: u8 = 0;
    let mut v_utf8_1835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_1837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_1840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_array_1841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_1842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: u8 = 0;
    let mut v___x_1845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: u8 = 0;
    let mut v_got_1848_: u8 = 0;
    let mut v___x_1849_: u8 = 0;
    let mut v___x_1850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1854_: u8 = 0;
    let mut v___x_1855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1861_: u8 = 0;
    let mut v_unused_1862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_utf8_1864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_1866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_1867_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_utf8_1864_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseHeader___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseHeader___closed__1_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseHeader___closed__1);
                v___x_1865_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_1864_, v_a_1815_);
                if lean_obj_tag(v___x_1865_) == 0 {
                    v_pos_1866_ = lean_ctor_get(v___x_1865_, 0);
                    lean_inc(v_pos_1866_);
                    lean_dec_ref_known(v___x_1865_, 2);
                    v_pos_1840_ = v_pos_1866_;
                    state = 5;
                    continue;
                } else {
                    if lean_obj_tag(v___x_1865_) == 0 {
                        v_pos_1867_ = lean_ctor_get(v___x_1865_, 0);
                        lean_inc(v_pos_1867_);
                        lean_dec_ref_known(v___x_1865_, 2);
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
                if lean_obj_tag(v___y_1817_) == 0 {
                    v_pos_1818_ = lean_ctor_get(v___y_1817_, 0);
                    lean_inc(v_pos_1818_);
                    lean_dec_ref_known(v___y_1817_, 2);
                    v___x_1819_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseLines(v_pos_1818_);
                    return v___x_1819_;
                } else {
                    v_pos_1820_ = lean_ctor_get(v___y_1817_, 0);
                    v_err_1821_ = lean_ctor_get(v___y_1817_, 1);
                    v_isSharedCheck_1828_ = (!lean_is_exclusive(v___y_1817_)) as u8;
                    if v_isSharedCheck_1828_ == 0 {
                        v___x_1823_ = v___y_1817_;
                        v_isShared_1824_ = v_isSharedCheck_1828_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_err_1821_);
                        lean_inc(v_pos_1820_);
                        lean_dec(v___y_1817_);
                        v___x_1823_ = lean_box(0);
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
                    v_reuseFailAlloc_1827_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_pos_1820_);
                    lean_ctor_set(v_reuseFailAlloc_1827_, 1, v_err_1821_);
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
                lean_dec(v_idx_1833_);
                lean_dec(v_idx_1830_);
                if v___x_1834_ == 0 {
                    lean_dec_ref(v_pos_1832_);
                    v___y_1817_ = v___y_1831_;
                    state = 1;
                    continue;
                } else {
                    lean_dec_ref(v___y_1831_);
                    v_utf8_1835_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__10_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__10);
                    v___x_1836_ =
                        l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_1835_, v_pos_1832_);
                    if lean_obj_tag(v___x_1836_) == 0 {
                        v_pos_1837_ = lean_ctor_get(v___x_1836_, 0);
                        lean_inc(v_pos_1837_);
                        lean_dec_ref_known(v___x_1836_, 2);
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
                v_array_1841_ = lean_ctor_get(v_pos_1840_, 0);
                v_idx_1842_ = lean_ctor_get(v_pos_1840_, 1);
                lean_inc(v_idx_1842_);
                v___x_1843_ = lean_byte_array_size(v_array_1841_);
                v___x_1844_ = lean_nat_dec_lt(v_idx_1842_, v___x_1843_);
                if v___x_1844_ == 0 {
                    v___x_1845_ = lean_box(0);
                    lean_inc_ref(v_pos_1840_);
                    v___x_1846_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_1846_, 0, v_pos_1840_);
                    lean_ctor_set(v___x_1846_, 1, v___x_1845_);
                    lean_inc(v_idx_1842_);
                    v_idx_1830_ = v_idx_1842_;
                    v___y_1831_ = v___x_1846_;
                    v_pos_1832_ = v_pos_1840_;
                    v_idx_1833_ = v_idx_1842_;
                    state = 4;
                    continue;
                } else {
                    v___x_1847_ = lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__11_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__11);
                    v_got_1848_ = lean_byte_array_fget(v_array_1841_, v_idx_1842_);
                    v___x_1849_ = lean_uint8_dec_eq(v_got_1848_, v___x_1847_);
                    if v___x_1849_ == 0 {
                        v___x_1850_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__16), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__16_once), _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__16);
                        lean_inc_ref(v_pos_1840_);
                        v___x_1851_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_1851_, 0, v_pos_1840_);
                        lean_ctor_set(v___x_1851_, 1, v___x_1850_);
                        lean_inc(v_idx_1842_);
                        v_idx_1830_ = v_idx_1842_;
                        v___y_1831_ = v___x_1851_;
                        v_pos_1832_ = v_pos_1840_;
                        v_idx_1833_ = v_idx_1842_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc_ref(v_array_1841_);
                        v_isSharedCheck_1861_ = (!lean_is_exclusive(v_pos_1840_)) as u8;
                        if v_isSharedCheck_1861_ == 0 {
                            v_unused_1862_ = lean_ctor_get(v_pos_1840_, 1);
                            lean_dec(v_unused_1862_);
                            v_unused_1863_ = lean_ctor_get(v_pos_1840_, 0);
                            lean_dec(v_unused_1863_);
                            v___x_1853_ = v_pos_1840_;
                            v_isShared_1854_ = v_isSharedCheck_1861_;
                            state = 6;
                            continue;
                        } else {
                            lean_dec(v_pos_1840_);
                            v___x_1853_ = lean_box(0);
                            v_isShared_1854_ = v_isSharedCheck_1861_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            6 => {
                v___x_1855_ = lean_unsigned_to_nat(1);
                v___x_1856_ = lean_nat_add(v_idx_1842_, v___x_1855_);
                lean_dec(v_idx_1842_);
                if v_isShared_1854_ == 0 {
                    lean_ctor_set(v___x_1853_, 1, v___x_1856_);
                    v___x_1858_ = v___x_1853_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1860_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1860_, 0, v_array_1841_);
                    lean_ctor_set(v_reuseFailAlloc_1860_, 1, v___x_1856_);
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
    mut v_x_1868_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1868_) == 0 {
        let mut v___x_1869_: *mut LeanObject = core::ptr::null_mut();
        v___x_1869_ = lean_unsigned_to_nat(0);
        return v___x_1869_;
    } else {
        let mut v___x_1870_: *mut LeanObject = core::ptr::null_mut();
        v___x_1870_ = lean_unsigned_to_nat(1);
        return v___x_1870_;
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorIdx___redArg___boxed(
    mut v_x_1871_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1872_: *mut LeanObject = core::ptr::null_mut();
    v_res_1872_ = l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorIdx___redArg(v_x_1871_);
    lean_dec(v_x_1871_);
    return v_res_1872_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorIdx(
    mut v_00_u03b1_1873_: *mut LeanObject,
    mut v_x_1874_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1875_: *mut LeanObject = core::ptr::null_mut();
    v___x_1875_ = l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorIdx___redArg(v_x_1874_);
    return v___x_1875_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorIdx___boxed(
    mut v_00_u03b1_1876_: *mut LeanObject,
    mut v_x_1877_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1878_: *mut LeanObject = core::ptr::null_mut();
    v_res_1878_ =
        l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorIdx(v_00_u03b1_1876_, v_x_1877_);
    lean_dec(v_x_1877_);
    return v_res_1878_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorElim___redArg(
    mut v_t_1879_: *mut LeanObject,
    mut v_k_1880_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_1879_) == 0 {
        let mut v_x_1881_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1882_: *mut LeanObject = core::ptr::null_mut();
        v_x_1881_ = lean_ctor_get(v_t_1879_, 0);
        lean_inc(v_x_1881_);
        lean_dec_ref_known(v_t_1879_, 1);
        v___x_1882_ = lean_apply_1(v_k_1880_, v_x_1881_);
        return v___x_1882_;
    } else {
        return v_k_1880_;
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorElim(
    mut v_00_u03b1_1883_: *mut LeanObject,
    mut v_motive_1884_: *mut LeanObject,
    mut v_ctorIdx_1885_: *mut LeanObject,
    mut v_t_1886_: *mut LeanObject,
    mut v_h_1887_: *mut LeanObject,
    mut v_k_1888_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1889_: *mut LeanObject = core::ptr::null_mut();
    v___x_1889_ =
        l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorElim___redArg(v_t_1886_, v_k_1888_);
    return v___x_1889_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorElim___boxed(
    mut v_00_u03b1_1890_: *mut LeanObject,
    mut v_motive_1891_: *mut LeanObject,
    mut v_ctorIdx_1892_: *mut LeanObject,
    mut v_t_1893_: *mut LeanObject,
    mut v_h_1894_: *mut LeanObject,
    mut v_k_1895_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1896_: *mut LeanObject = core::ptr::null_mut();
    v_res_1896_ = l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorElim(
        v_00_u03b1_1890_,
        v_motive_1891_,
        v_ctorIdx_1892_,
        v_t_1893_,
        v_h_1894_,
        v_k_1895_,
    );
    lean_dec(v_ctorIdx_1892_);
    return v_res_1896_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_External_TimedOut_success_elim___redArg(
    mut v_t_1897_: *mut LeanObject,
    mut v_success_1898_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1899_: *mut LeanObject = core::ptr::null_mut();
    v___x_1899_ =
        l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorElim___redArg(v_t_1897_, v_success_1898_);
    return v___x_1899_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_External_TimedOut_success_elim(
    mut v_00_u03b1_1900_: *mut LeanObject,
    mut v_motive_1901_: *mut LeanObject,
    mut v_t_1902_: *mut LeanObject,
    mut v_h_1903_: *mut LeanObject,
    mut v_success_1904_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1905_: *mut LeanObject = core::ptr::null_mut();
    v___x_1905_ =
        l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorElim___redArg(v_t_1902_, v_success_1904_);
    return v___x_1905_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_External_TimedOut_timeout_elim___redArg(
    mut v_t_1906_: *mut LeanObject,
    mut v_timeout_1907_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1908_: *mut LeanObject = core::ptr::null_mut();
    v___x_1908_ =
        l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorElim___redArg(v_t_1906_, v_timeout_1907_);
    return v___x_1908_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_External_TimedOut_timeout_elim(
    mut v_00_u03b1_1909_: *mut LeanObject,
    mut v_motive_1910_: *mut LeanObject,
    mut v_t_1911_: *mut LeanObject,
    mut v_h_1912_: *mut LeanObject,
    mut v_timeout_1913_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1914_: *mut LeanObject = core::ptr::null_mut();
    v___x_1914_ =
        l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorElim___redArg(v_t_1911_, v_timeout_1913_);
    return v___x_1914_;
}
pub unsafe fn _init_l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_1915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut LeanObject = core::ptr::null_mut();
    v___x_1915_ = lean_box(0);
    v___x_1916_ = l_Lean_interruptExceptionId;
    v___x_1917_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1917_, 0, v___x_1916_);
    lean_ctor_set(v___x_1917_, 1, v___x_1915_);
    return v___x_1917_;
}
pub unsafe fn l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0___redArg()
-> *mut LeanObject {
    let mut v___x_1919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1920_: *mut LeanObject = core::ptr::null_mut();
    v___x_1919_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0___redArg___closed__0_once), _init_l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0___redArg___closed__0);
    v___x_1920_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1920_, 0, v___x_1919_);
    return v___x_1920_;
}
pub unsafe fn l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0___redArg___boxed(
    mut v___y_1921_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1922_: *mut LeanObject = core::ptr::null_mut();
    v_res_1922_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0___redArg();
    return v_res_1922_;
}
pub unsafe fn l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0(
    mut v_00_u03b1_1923_: *mut LeanObject,
    mut v___y_1924_: *mut LeanObject,
    mut v___y_1925_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1927_: *mut LeanObject = core::ptr::null_mut();
    v___x_1927_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0___redArg();
    return v___x_1927_;
}
pub unsafe fn l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0___boxed(
    mut v_00_u03b1_1928_: *mut LeanObject,
    mut v___y_1929_: *mut LeanObject,
    mut v___y_1930_: *mut LeanObject,
    mut v___y_1931_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1932_: *mut LeanObject = core::ptr::null_mut();
    v_res_1932_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0(v_00_u03b1_1928_, v___y_1929_, v___y_1930_);
    lean_dec(v___y_1930_);
    lean_dec_ref(v___y_1929_);
    return v_res_1932_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck___redArg(
    mut v_cleanup_1933_: *mut LeanObject,
    mut v_x_1934_: *mut LeanObject,
    mut v_a_1935_: *mut LeanObject,
    mut v_a_1936_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cancelTk_x3f_1938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: u8 = 0;
    let mut v___x_1941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1947_: u8 = 0;
    let mut v___x_1949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1951_: u8 = 0;
    let mut v_a_1952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1955_: u8 = 0;
    let mut v___x_1957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1959_: u8 = 0;
    let mut v___x_1960_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_cancelTk_x3f_1938_ = lean_ctor_get(v_a_1935_, 12);
                if lean_obj_tag(v_cancelTk_x3f_1938_) == 1 {
                    v_val_1939_ = lean_ctor_get(v_cancelTk_x3f_1938_, 0);
                    v___x_1940_ = l_IO_CancelToken_isSet(v_val_1939_);
                    if v___x_1940_ == 0 {
                        lean_dec_ref(v_cleanup_1933_);
                        lean_inc(v_a_1936_);
                        lean_inc_ref(v_a_1935_);
                        v___x_1941_ = lean_apply_3(v_x_1934_, v_a_1935_, v_a_1936_, lean_box(0));
                        return v___x_1941_;
                    } else {
                        lean_dec_ref(v_x_1934_);
                        lean_inc(v_a_1936_);
                        lean_inc_ref(v_a_1935_);
                        v___x_1942_ =
                            lean_apply_3(v_cleanup_1933_, v_a_1935_, v_a_1936_, lean_box(0));
                        if lean_obj_tag(v___x_1942_) == 0 {
                            lean_dec_ref_known(v___x_1942_, 1);
                            v___x_1943_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0___redArg();
                            v_a_1944_ = lean_ctor_get(v___x_1943_, 0);
                            v_isSharedCheck_1951_ = (!lean_is_exclusive(v___x_1943_)) as u8;
                            if v_isSharedCheck_1951_ == 0 {
                                v___x_1946_ = v___x_1943_;
                                v_isShared_1947_ = v_isSharedCheck_1951_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_1944_);
                                lean_dec(v___x_1943_);
                                v___x_1946_ = lean_box(0);
                                v_isShared_1947_ = v_isSharedCheck_1951_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_1952_ = lean_ctor_get(v___x_1942_, 0);
                            v_isSharedCheck_1959_ = (!lean_is_exclusive(v___x_1942_)) as u8;
                            if v_isSharedCheck_1959_ == 0 {
                                v___x_1954_ = v___x_1942_;
                                v_isShared_1955_ = v_isSharedCheck_1959_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_1952_);
                                lean_dec(v___x_1942_);
                                v___x_1954_ = lean_box(0);
                                v_isShared_1955_ = v_isSharedCheck_1959_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_cleanup_1933_);
                    lean_inc(v_a_1936_);
                    lean_inc_ref(v_a_1935_);
                    v___x_1960_ = lean_apply_3(v_x_1934_, v_a_1935_, v_a_1936_, lean_box(0));
                    return v___x_1960_;
                }
            }
            1 => {
                if v_isShared_1947_ == 0 {
                    v___x_1949_ = v___x_1946_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1950_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1950_, 0, v_a_1944_);
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
                    v_reuseFailAlloc_1958_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_a_1952_);
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
    mut v_cleanup_1961_: *mut LeanObject,
    mut v_x_1962_: *mut LeanObject,
    mut v_a_1963_: *mut LeanObject,
    mut v_a_1964_: *mut LeanObject,
    mut v_a_1965_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1966_: *mut LeanObject = core::ptr::null_mut();
    v_res_1966_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck___redArg(v_cleanup_1961_, v_x_1962_, v_a_1963_, v_a_1964_);
    lean_dec(v_a_1964_);
    lean_dec_ref(v_a_1963_);
    return v_res_1966_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck(
    mut v_00_u03b1_1967_: *mut LeanObject,
    mut v_cleanup_1968_: *mut LeanObject,
    mut v_x_1969_: *mut LeanObject,
    mut v_a_1970_: *mut LeanObject,
    mut v_a_1971_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1973_: *mut LeanObject = core::ptr::null_mut();
    v___x_1973_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck___redArg(v_cleanup_1968_, v_x_1969_, v_a_1970_, v_a_1971_);
    return v___x_1973_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck___boxed(
    mut v_00_u03b1_1974_: *mut LeanObject,
    mut v_cleanup_1975_: *mut LeanObject,
    mut v_x_1976_: *mut LeanObject,
    mut v_a_1977_: *mut LeanObject,
    mut v_a_1978_: *mut LeanObject,
    mut v_a_1979_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1980_: *mut LeanObject = core::ptr::null_mut();
    v_res_1980_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck(v_00_u03b1_1974_, v_cleanup_1975_, v_x_1976_, v_a_1977_, v_a_1978_);
    lean_dec(v_a_1978_);
    lean_dec_ref(v_a_1977_);
    return v_res_1980_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withTimeoutCheck___redArg(
    mut v_budgetMs_1981_: *mut LeanObject,
    mut v_cleanup_1982_: *mut LeanObject,
    mut v_x_1983_: *mut LeanObject,
    mut v_a_1984_: *mut LeanObject,
    mut v_a_1985_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: u8 = 0;
    let mut v___x_1989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1993_: u8 = 0;
    let mut v___x_1994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1998_: u8 = 0;
    let mut v_unused_1999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2003_: u8 = 0;
    let mut v___x_2005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2007_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1987_ = lean_unsigned_to_nat(0);
                v___x_1988_ = lean_nat_dec_eq(v_budgetMs_1981_, v___x_1987_);
                if v___x_1988_ == 0 {
                    lean_dec_ref(v_cleanup_1982_);
                    lean_inc(v_a_1985_);
                    lean_inc_ref(v_a_1984_);
                    v___x_1989_ = lean_apply_3(v_x_1983_, v_a_1984_, v_a_1985_, lean_box(0));
                    return v___x_1989_;
                } else {
                    lean_dec_ref(v_x_1983_);
                    lean_inc(v_a_1985_);
                    lean_inc_ref(v_a_1984_);
                    v___x_1990_ = lean_apply_3(v_cleanup_1982_, v_a_1984_, v_a_1985_, lean_box(0));
                    if lean_obj_tag(v___x_1990_) == 0 {
                        v_isSharedCheck_1998_ = (!lean_is_exclusive(v___x_1990_)) as u8;
                        if v_isSharedCheck_1998_ == 0 {
                            v_unused_1999_ = lean_ctor_get(v___x_1990_, 0);
                            lean_dec(v_unused_1999_);
                            v___x_1992_ = v___x_1990_;
                            v_isShared_1993_ = v_isSharedCheck_1998_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v___x_1990_);
                            v___x_1992_ = lean_box(0);
                            v_isShared_1993_ = v_isSharedCheck_1998_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2000_ = lean_ctor_get(v___x_1990_, 0);
                        v_isSharedCheck_2007_ = (!lean_is_exclusive(v___x_1990_)) as u8;
                        if v_isSharedCheck_2007_ == 0 {
                            v___x_2002_ = v___x_1990_;
                            v_isShared_2003_ = v_isSharedCheck_2007_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2000_);
                            lean_dec(v___x_1990_);
                            v___x_2002_ = lean_box(0);
                            v_isShared_2003_ = v_isSharedCheck_2007_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1994_ = lean_box(1);
                if v_isShared_1993_ == 0 {
                    lean_ctor_set(v___x_1992_, 0, v___x_1994_);
                    v___x_1996_ = v___x_1992_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1997_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1997_, 0, v___x_1994_);
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
                    v_reuseFailAlloc_2006_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2006_, 0, v_a_2000_);
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
    mut v_budgetMs_2008_: *mut LeanObject,
    mut v_cleanup_2009_: *mut LeanObject,
    mut v_x_2010_: *mut LeanObject,
    mut v_a_2011_: *mut LeanObject,
    mut v_a_2012_: *mut LeanObject,
    mut v_a_2013_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2014_: *mut LeanObject = core::ptr::null_mut();
    v_res_2014_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withTimeoutCheck___redArg(v_budgetMs_2008_, v_cleanup_2009_, v_x_2010_, v_a_2011_, v_a_2012_);
    lean_dec(v_a_2012_);
    lean_dec_ref(v_a_2011_);
    lean_dec(v_budgetMs_2008_);
    return v_res_2014_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withTimeoutCheck(
    mut v_00_u03b1_2015_: *mut LeanObject,
    mut v_budgetMs_2016_: *mut LeanObject,
    mut v_cleanup_2017_: *mut LeanObject,
    mut v_x_2018_: *mut LeanObject,
    mut v_a_2019_: *mut LeanObject,
    mut v_a_2020_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2022_: *mut LeanObject = core::ptr::null_mut();
    v___x_2022_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withTimeoutCheck___redArg(v_budgetMs_2016_, v_cleanup_2017_, v_x_2018_, v_a_2019_, v_a_2020_);
    return v___x_2022_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withTimeoutCheck___boxed(
    mut v_00_u03b1_2023_: *mut LeanObject,
    mut v_budgetMs_2024_: *mut LeanObject,
    mut v_cleanup_2025_: *mut LeanObject,
    mut v_x_2026_: *mut LeanObject,
    mut v_a_2027_: *mut LeanObject,
    mut v_a_2028_: *mut LeanObject,
    mut v_a_2029_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2030_: *mut LeanObject = core::ptr::null_mut();
    v_res_2030_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withTimeoutCheck(v_00_u03b1_2023_, v_budgetMs_2024_, v_cleanup_2025_, v_x_2026_, v_a_2027_, v_a_2028_);
    lean_dec(v_a_2028_);
    lean_dec_ref(v_a_2027_);
    lean_dec(v_budgetMs_2024_);
    return v_res_2030_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_killAndWait(
    mut v_cfg_2031_: *mut LeanObject,
    mut v_child_2032_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2038_: u8 = 0;
    let mut v___x_2039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2043_: u8 = 0;
    let mut v_unused_2044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2048_: u8 = 0;
    let mut v___x_2050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2052_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2034_ = lean_io_process_child_kill(v_cfg_2031_, v_child_2032_);
                if lean_obj_tag(v___x_2034_) == 0 {
                    lean_dec_ref_known(v___x_2034_, 1);
                    v___x_2035_ = lean_io_process_child_wait(v_cfg_2031_, v_child_2032_);
                    if lean_obj_tag(v___x_2035_) == 0 {
                        v_isSharedCheck_2043_ = (!lean_is_exclusive(v___x_2035_)) as u8;
                        if v_isSharedCheck_2043_ == 0 {
                            v_unused_2044_ = lean_ctor_get(v___x_2035_, 0);
                            lean_dec(v_unused_2044_);
                            v___x_2037_ = v___x_2035_;
                            v_isShared_2038_ = v_isSharedCheck_2043_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v___x_2035_);
                            v___x_2037_ = lean_box(0);
                            v_isShared_2038_ = v_isSharedCheck_2043_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2045_ = lean_ctor_get(v___x_2035_, 0);
                        v_isSharedCheck_2052_ = (!lean_is_exclusive(v___x_2035_)) as u8;
                        if v_isSharedCheck_2052_ == 0 {
                            v___x_2047_ = v___x_2035_;
                            v_isShared_2048_ = v_isSharedCheck_2052_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2045_);
                            lean_dec(v___x_2035_);
                            v___x_2047_ = lean_box(0);
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
                v___x_2039_ = lean_box(0);
                if v_isShared_2038_ == 0 {
                    lean_ctor_set(v___x_2037_, 0, v___x_2039_);
                    v___x_2041_ = v___x_2037_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2042_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2042_, 0, v___x_2039_);
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
                    v_reuseFailAlloc_2051_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2051_, 0, v_a_2045_);
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
    mut v_cfg_2053_: *mut LeanObject,
    mut v_child_2054_: *mut LeanObject,
    mut v_a_2055_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2056_: *mut LeanObject = core::ptr::null_mut();
    v_res_2056_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_killAndWait(v_cfg_2053_, v_child_2054_);
    lean_dec_ref(v_child_2054_);
    lean_dec_ref(v_cfg_2053_);
    return v_res_2056_;
}
pub unsafe fn l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go_spec__0___redArg(
    mut v_e_2057_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2062_: u8 = 0;
    let mut v___x_2063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2068_: u8 = 0;
    let mut v_a_2069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2072_: u8 = 0;
    let mut v___x_2074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2076_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_e_2057_) == 0 {
                    v_a_2059_ = lean_ctor_get(v_e_2057_, 0);
                    v_isSharedCheck_2068_ = (!lean_is_exclusive(v_e_2057_)) as u8;
                    if v_isSharedCheck_2068_ == 0 {
                        v___x_2061_ = v_e_2057_;
                        v_isShared_2062_ = v_isSharedCheck_2068_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2059_);
                        lean_dec(v_e_2057_);
                        v___x_2061_ = lean_box(0);
                        v_isShared_2062_ = v_isSharedCheck_2068_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2069_ = lean_ctor_get(v_e_2057_, 0);
                    v_isSharedCheck_2076_ = (!lean_is_exclusive(v_e_2057_)) as u8;
                    if v_isSharedCheck_2076_ == 0 {
                        v___x_2071_ = v_e_2057_;
                        v_isShared_2072_ = v_isSharedCheck_2076_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2069_);
                        lean_dec(v_e_2057_);
                        v___x_2071_ = lean_box(0);
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
                    lean_ctor_set_tag(v___x_2061_, 1);
                    lean_ctor_set(v___x_2061_, 0, v___x_2064_);
                    v___x_2066_ = v___x_2061_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2067_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2067_, 0, v___x_2064_);
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
                    lean_ctor_set_tag(v___x_2071_, 0);
                    v___x_2074_ = v___x_2071_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2075_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2075_, 0, v_a_2069_);
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
    mut v_e_2077_: *mut LeanObject,
    mut v_a_2078_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2079_: *mut LeanObject = core::ptr::null_mut();
    v_res_2079_ = l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go_spec__0___redArg(v_e_2077_);
    return v_res_2079_;
}
pub unsafe fn l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go_spec__0(
    mut v_00_u03b1_2080_: *mut LeanObject,
    mut v_e_2081_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2083_: *mut LeanObject = core::ptr::null_mut();
    v___x_2083_ = l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go_spec__0___redArg(v_e_2081_);
    return v___x_2083_;
}
pub unsafe fn l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go_spec__0___boxed(
    mut v_00_u03b1_2084_: *mut LeanObject,
    mut v_e_2085_: *mut LeanObject,
    mut v_a_2086_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2087_: *mut LeanObject = core::ptr::null_mut();
    v_res_2087_ = l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go_spec__0(v_00_u03b1_2084_, v_e_2085_);
    return v_res_2087_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go___lam__1(
    mut v_cfg_2088_: *mut LeanObject,
    mut v_child_2089_: *mut LeanObject,
    mut v___y_2090_: *mut LeanObject,
    mut v___y_2091_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2097_: u8 = 0;
    let mut v___x_2099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2101_: u8 = 0;
    let mut v_a_2102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2105_: u8 = 0;
    let mut v_ref_2106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2114_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2093_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_killAndWait(v_cfg_2088_, v_child_2089_);
                if lean_obj_tag(v___x_2093_) == 0 {
                    v_a_2094_ = lean_ctor_get(v___x_2093_, 0);
                    v_isSharedCheck_2101_ = (!lean_is_exclusive(v___x_2093_)) as u8;
                    if v_isSharedCheck_2101_ == 0 {
                        v___x_2096_ = v___x_2093_;
                        v_isShared_2097_ = v_isSharedCheck_2101_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2094_);
                        lean_dec(v___x_2093_);
                        v___x_2096_ = lean_box(0);
                        v_isShared_2097_ = v_isSharedCheck_2101_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2102_ = lean_ctor_get(v___x_2093_, 0);
                    v_isSharedCheck_2114_ = (!lean_is_exclusive(v___x_2093_)) as u8;
                    if v_isSharedCheck_2114_ == 0 {
                        v___x_2104_ = v___x_2093_;
                        v_isShared_2105_ = v_isSharedCheck_2114_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2102_);
                        lean_dec(v___x_2093_);
                        v___x_2104_ = lean_box(0);
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
                    v_reuseFailAlloc_2100_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2100_, 0, v_a_2094_);
                    v___x_2099_ = v_reuseFailAlloc_2100_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2099_;
            }
            3 => {
                v_ref_2106_ = lean_ctor_get(v___y_2090_, 5);
                v___x_2107_ = lean_io_error_to_string(v_a_2102_);
                v___x_2108_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_2108_, 0, v___x_2107_);
                v___x_2109_ = l_Lean_MessageData_ofFormat(v___x_2108_);
                lean_inc(v_ref_2106_);
                v___x_2110_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2110_, 0, v_ref_2106_);
                lean_ctor_set(v___x_2110_, 1, v___x_2109_);
                if v_isShared_2105_ == 0 {
                    lean_ctor_set(v___x_2104_, 0, v___x_2110_);
                    v___x_2112_ = v___x_2104_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2113_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2113_, 0, v___x_2110_);
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
    mut v_cfg_2115_: *mut LeanObject,
    mut v_child_2116_: *mut LeanObject,
    mut v___y_2117_: *mut LeanObject,
    mut v___y_2118_: *mut LeanObject,
    mut v___y_2119_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2120_: *mut LeanObject = core::ptr::null_mut();
    v_res_2120_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go___lam__1(v_cfg_2115_, v_child_2116_, v___y_2117_, v___y_2118_);
    lean_dec(v___y_2118_);
    lean_dec_ref(v___y_2117_);
    lean_dec_ref(v_child_2116_);
    lean_dec_ref(v_cfg_2115_);
    return v_res_2120_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go___lam__0(
    mut v_cfg_2121_: *mut LeanObject,
    mut v_child_2122_: *mut LeanObject,
    mut v_budgetMs_2123_: *mut LeanObject,
    mut v_stdout_2124_: *mut LeanObject,
    mut v_stderr_2125_: *mut LeanObject,
    mut v___y_2126_: *mut LeanObject,
    mut v___y_2127_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: u32 = 0;
    let mut v___x_2132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2139_: u8 = 0;
    let mut v___x_2140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2148_: u8 = 0;
    let mut v___x_2149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: u32 = 0;
    let mut v___x_2152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2157_: u8 = 0;
    let mut v_a_2158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2161_: u8 = 0;
    let mut v_ref_2162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2172_: u8 = 0;
    let mut v_a_2173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2176_: u8 = 0;
    let mut v_ref_2177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2187_: u8 = 0;
    let mut v_isSharedCheck_2188_: u8 = 0;
    let mut v_a_2189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2192_: u8 = 0;
    let mut v_ref_2193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2201_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2129_ = lean_io_process_child_try_wait(v_cfg_2121_, v_child_2122_);
                if lean_obj_tag(v___x_2129_) == 0 {
                    v_a_2130_ = lean_ctor_get(v___x_2129_, 0);
                    lean_inc(v_a_2130_);
                    lean_dec_ref_known(v___x_2129_, 1);
                    if lean_obj_tag(v_a_2130_) == 0 {
                        v___x_2131_ = 50;
                        v___x_2132_ = l_IO_sleep(v___x_2131_);
                        v___x_2133_ = lean_unsigned_to_nat(50);
                        v___x_2134_ = lean_nat_sub(v_budgetMs_2123_, v___x_2133_);
                        v___x_2135_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go(v_cfg_2121_, v___x_2134_, v_child_2122_, v_stdout_2124_, v_stderr_2125_, v___y_2126_, v___y_2127_);
                        return v___x_2135_;
                    } else {
                        lean_dec_ref(v_child_2122_);
                        lean_dec_ref(v_cfg_2121_);
                        v_val_2136_ = lean_ctor_get(v_a_2130_, 0);
                        v_isSharedCheck_2188_ = (!lean_is_exclusive(v_a_2130_)) as u8;
                        if v_isSharedCheck_2188_ == 0 {
                            v___x_2138_ = v_a_2130_;
                            v_isShared_2139_ = v_isSharedCheck_2188_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_val_2136_);
                            lean_dec(v_a_2130_);
                            v___x_2138_ = lean_box(0);
                            v_isShared_2139_ = v_isSharedCheck_2188_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_stderr_2125_);
                    lean_dec_ref(v_stdout_2124_);
                    lean_dec_ref(v_child_2122_);
                    lean_dec_ref(v_cfg_2121_);
                    v_a_2189_ = lean_ctor_get(v___x_2129_, 0);
                    v_isSharedCheck_2201_ = (!lean_is_exclusive(v___x_2129_)) as u8;
                    if v_isSharedCheck_2201_ == 0 {
                        v___x_2191_ = v___x_2129_;
                        v_isShared_2192_ = v_isSharedCheck_2201_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_2189_);
                        lean_dec(v___x_2129_);
                        v___x_2191_ = lean_box(0);
                        v_isShared_2192_ = v_isSharedCheck_2201_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2140_ = lean_task_get_own(v_stdout_2124_);
                v___x_2141_ = l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go_spec__0___redArg(v___x_2140_);
                if lean_obj_tag(v___x_2141_) == 0 {
                    v_a_2142_ = lean_ctor_get(v___x_2141_, 0);
                    lean_inc(v_a_2142_);
                    lean_dec_ref_known(v___x_2141_, 1);
                    v___x_2143_ = lean_task_get_own(v_stderr_2125_);
                    v___x_2144_ = l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go_spec__0___redArg(v___x_2143_);
                    if lean_obj_tag(v___x_2144_) == 0 {
                        v_a_2145_ = lean_ctor_get(v___x_2144_, 0);
                        v_isSharedCheck_2157_ = (!lean_is_exclusive(v___x_2144_)) as u8;
                        if v_isSharedCheck_2157_ == 0 {
                            v___x_2147_ = v___x_2144_;
                            v_isShared_2148_ = v_isSharedCheck_2157_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_2145_);
                            lean_dec(v___x_2144_);
                            v___x_2147_ = lean_box(0);
                            v_isShared_2148_ = v_isSharedCheck_2157_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_2142_);
                        lean_dec(v_val_2136_);
                        v_a_2158_ = lean_ctor_get(v___x_2144_, 0);
                        v_isSharedCheck_2172_ = (!lean_is_exclusive(v___x_2144_)) as u8;
                        if v_isSharedCheck_2172_ == 0 {
                            v___x_2160_ = v___x_2144_;
                            v_isShared_2161_ = v_isSharedCheck_2172_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_2158_);
                            lean_dec(v___x_2144_);
                            v___x_2160_ = lean_box(0);
                            v_isShared_2161_ = v_isSharedCheck_2172_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_val_2136_);
                    lean_dec_ref(v_stderr_2125_);
                    v_a_2173_ = lean_ctor_get(v___x_2141_, 0);
                    v_isSharedCheck_2187_ = (!lean_is_exclusive(v___x_2141_)) as u8;
                    if v_isSharedCheck_2187_ == 0 {
                        v___x_2175_ = v___x_2141_;
                        v_isShared_2176_ = v_isSharedCheck_2187_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_2173_);
                        lean_dec(v___x_2141_);
                        v___x_2175_ = lean_box(0);
                        v_isShared_2176_ = v_isSharedCheck_2187_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2149_ = lean_alloc_ctor(0, 2, (4) as u32);
                lean_ctor_set(v___x_2149_, 0, v_a_2142_);
                lean_ctor_set(v___x_2149_, 1, v_a_2145_);
                v___x_2150_ = lean_unbox_uint32(v_val_2136_);
                lean_dec(v_val_2136_);
                lean_ctor_set_uint32(
                    v___x_2149_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v___x_2150_,
                );
                if v_isShared_2139_ == 0 {
                    lean_ctor_set_tag(v___x_2138_, 0);
                    lean_ctor_set(v___x_2138_, 0, v___x_2149_);
                    v___x_2152_ = v___x_2138_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2156_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2156_, 0, v___x_2149_);
                    v___x_2152_ = v_reuseFailAlloc_2156_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2148_ == 0 {
                    lean_ctor_set(v___x_2147_, 0, v___x_2152_);
                    v___x_2154_ = v___x_2147_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2155_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2155_, 0, v___x_2152_);
                    v___x_2154_ = v_reuseFailAlloc_2155_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2154_;
            }
            5 => {
                v_ref_2162_ = lean_ctor_get(v___y_2126_, 5);
                v___x_2163_ = lean_io_error_to_string(v_a_2158_);
                if v_isShared_2139_ == 0 {
                    lean_ctor_set_tag(v___x_2138_, 3);
                    lean_ctor_set(v___x_2138_, 0, v___x_2163_);
                    v___x_2165_ = v___x_2138_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2171_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2171_, 0, v___x_2163_);
                    v___x_2165_ = v_reuseFailAlloc_2171_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_2166_ = l_Lean_MessageData_ofFormat(v___x_2165_);
                lean_inc(v_ref_2162_);
                v___x_2167_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2167_, 0, v_ref_2162_);
                lean_ctor_set(v___x_2167_, 1, v___x_2166_);
                if v_isShared_2161_ == 0 {
                    lean_ctor_set(v___x_2160_, 0, v___x_2167_);
                    v___x_2169_ = v___x_2160_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2170_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2170_, 0, v___x_2167_);
                    v___x_2169_ = v_reuseFailAlloc_2170_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2169_;
            }
            8 => {
                v_ref_2177_ = lean_ctor_get(v___y_2126_, 5);
                v___x_2178_ = lean_io_error_to_string(v_a_2173_);
                if v_isShared_2139_ == 0 {
                    lean_ctor_set_tag(v___x_2138_, 3);
                    lean_ctor_set(v___x_2138_, 0, v___x_2178_);
                    v___x_2180_ = v___x_2138_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2186_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2186_, 0, v___x_2178_);
                    v___x_2180_ = v_reuseFailAlloc_2186_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_2181_ = l_Lean_MessageData_ofFormat(v___x_2180_);
                lean_inc(v_ref_2177_);
                v___x_2182_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2182_, 0, v_ref_2177_);
                lean_ctor_set(v___x_2182_, 1, v___x_2181_);
                if v_isShared_2176_ == 0 {
                    lean_ctor_set(v___x_2175_, 0, v___x_2182_);
                    v___x_2184_ = v___x_2175_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2185_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2185_, 0, v___x_2182_);
                    v___x_2184_ = v_reuseFailAlloc_2185_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2184_;
            }
            11 => {
                v_ref_2193_ = lean_ctor_get(v___y_2126_, 5);
                v___x_2194_ = lean_io_error_to_string(v_a_2189_);
                v___x_2195_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_2195_, 0, v___x_2194_);
                v___x_2196_ = l_Lean_MessageData_ofFormat(v___x_2195_);
                lean_inc(v_ref_2193_);
                v___x_2197_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2197_, 0, v_ref_2193_);
                lean_ctor_set(v___x_2197_, 1, v___x_2196_);
                if v_isShared_2192_ == 0 {
                    lean_ctor_set(v___x_2191_, 0, v___x_2197_);
                    v___x_2199_ = v___x_2191_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2200_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2200_, 0, v___x_2197_);
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
    mut v_cfg_2202_: *mut LeanObject,
    mut v_child_2203_: *mut LeanObject,
    mut v_budgetMs_2204_: *mut LeanObject,
    mut v_stdout_2205_: *mut LeanObject,
    mut v_stderr_2206_: *mut LeanObject,
    mut v___y_2207_: *mut LeanObject,
    mut v___y_2208_: *mut LeanObject,
    mut v___y_2209_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2210_: *mut LeanObject = core::ptr::null_mut();
    v_res_2210_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go___lam__0(v_cfg_2202_, v_child_2203_, v_budgetMs_2204_, v_stdout_2205_, v_stderr_2206_, v___y_2207_, v___y_2208_);
    lean_dec(v___y_2208_);
    lean_dec_ref(v___y_2207_);
    lean_dec(v_budgetMs_2204_);
    return v_res_2210_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go(
    mut v_cfg_2211_: *mut LeanObject,
    mut v_budgetMs_2212_: *mut LeanObject,
    mut v_child_2213_: *mut LeanObject,
    mut v_stdout_2214_: *mut LeanObject,
    mut v_stderr_2215_: *mut LeanObject,
    mut v_a_2216_: *mut LeanObject,
    mut v_a_2217_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_budgetMs_2212_);
    lean_inc_ref(v_child_2213_);
    lean_inc_ref(v_cfg_2211_);
    v___f_2219_ = lean_alloc_closure(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go___lam__0___boxed as *mut core::ffi::c_void, 8, 5);
    lean_closure_set(v___f_2219_, 0, v_cfg_2211_);
    lean_closure_set(v___f_2219_, 1, v_child_2213_);
    lean_closure_set(v___f_2219_, 2, v_budgetMs_2212_);
    lean_closure_set(v___f_2219_, 3, v_stdout_2214_);
    lean_closure_set(v___f_2219_, 4, v_stderr_2215_);
    v___f_2220_ = lean_alloc_closure(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go___lam__1___boxed as *mut core::ffi::c_void, 5, 2);
    lean_closure_set(v___f_2220_, 0, v_cfg_2211_);
    lean_closure_set(v___f_2220_, 1, v_child_2213_);
    lean_inc_ref(v___f_2220_);
    v___x_2221_ = lean_alloc_closure(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck___boxed as *mut core::ffi::c_void, 6, 3);
    lean_closure_set(v___x_2221_, 0, lean_box(0));
    lean_closure_set(v___x_2221_, 1, v___f_2220_);
    lean_closure_set(v___x_2221_, 2, v___f_2219_);
    v___x_2222_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withTimeoutCheck___redArg(v_budgetMs_2212_, v___f_2220_, v___x_2221_, v_a_2216_, v_a_2217_);
    lean_dec(v_budgetMs_2212_);
    return v___x_2222_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go___boxed(
    mut v_cfg_2223_: *mut LeanObject,
    mut v_budgetMs_2224_: *mut LeanObject,
    mut v_child_2225_: *mut LeanObject,
    mut v_stdout_2226_: *mut LeanObject,
    mut v_stderr_2227_: *mut LeanObject,
    mut v_a_2228_: *mut LeanObject,
    mut v_a_2229_: *mut LeanObject,
    mut v_a_2230_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2231_: *mut LeanObject = core::ptr::null_mut();
    v_res_2231_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go(v_cfg_2223_, v_budgetMs_2224_, v_child_2225_, v_stdout_2226_, v_stderr_2227_, v_a_2228_, v_a_2229_);
    lean_dec(v_a_2229_);
    lean_dec_ref(v_a_2228_);
    return v_res_2231_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___lam__0(
    mut v_stdout_2232_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2238_: u8 = 0;
    let mut v___x_2240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2242_: u8 = 0;
    let mut v_a_2243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2246_: u8 = 0;
    let mut v___x_2248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2250_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2234_ = l_IO_FS_Handle_readToEnd(v_stdout_2232_);
                if lean_obj_tag(v___x_2234_) == 0 {
                    v_a_2235_ = lean_ctor_get(v___x_2234_, 0);
                    v_isSharedCheck_2242_ = (!lean_is_exclusive(v___x_2234_)) as u8;
                    if v_isSharedCheck_2242_ == 0 {
                        v___x_2237_ = v___x_2234_;
                        v_isShared_2238_ = v_isSharedCheck_2242_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2235_);
                        lean_dec(v___x_2234_);
                        v___x_2237_ = lean_box(0);
                        v_isShared_2238_ = v_isSharedCheck_2242_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2243_ = lean_ctor_get(v___x_2234_, 0);
                    v_isSharedCheck_2250_ = (!lean_is_exclusive(v___x_2234_)) as u8;
                    if v_isSharedCheck_2250_ == 0 {
                        v___x_2245_ = v___x_2234_;
                        v_isShared_2246_ = v_isSharedCheck_2250_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2243_);
                        lean_dec(v___x_2234_);
                        v___x_2245_ = lean_box(0);
                        v_isShared_2246_ = v_isSharedCheck_2250_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2238_ == 0 {
                    lean_ctor_set_tag(v___x_2237_, 1);
                    v___x_2240_ = v___x_2237_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2241_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2241_, 0, v_a_2235_);
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
                    lean_ctor_set_tag(v___x_2245_, 0);
                    v___x_2248_ = v___x_2245_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2249_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2249_, 0, v_a_2243_);
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
    mut v_stdout_2251_: *mut LeanObject,
    mut v___y_2252_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2253_: *mut LeanObject = core::ptr::null_mut();
    v_res_2253_ = l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___lam__0(v_stdout_2251_);
    lean_dec(v_stdout_2251_);
    return v_res_2253_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___lam__1(
    mut v_stderr_2254_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2260_: u8 = 0;
    let mut v___x_2262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2264_: u8 = 0;
    let mut v_a_2265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2268_: u8 = 0;
    let mut v___x_2270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2272_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2256_ = l_IO_FS_Handle_readToEnd(v_stderr_2254_);
                if lean_obj_tag(v___x_2256_) == 0 {
                    v_a_2257_ = lean_ctor_get(v___x_2256_, 0);
                    v_isSharedCheck_2264_ = (!lean_is_exclusive(v___x_2256_)) as u8;
                    if v_isSharedCheck_2264_ == 0 {
                        v___x_2259_ = v___x_2256_;
                        v_isShared_2260_ = v_isSharedCheck_2264_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2257_);
                        lean_dec(v___x_2256_);
                        v___x_2259_ = lean_box(0);
                        v_isShared_2260_ = v_isSharedCheck_2264_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2265_ = lean_ctor_get(v___x_2256_, 0);
                    v_isSharedCheck_2272_ = (!lean_is_exclusive(v___x_2256_)) as u8;
                    if v_isSharedCheck_2272_ == 0 {
                        v___x_2267_ = v___x_2256_;
                        v_isShared_2268_ = v_isSharedCheck_2272_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2265_);
                        lean_dec(v___x_2256_);
                        v___x_2267_ = lean_box(0);
                        v_isShared_2268_ = v_isSharedCheck_2272_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2260_ == 0 {
                    lean_ctor_set_tag(v___x_2259_, 1);
                    v___x_2262_ = v___x_2259_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2263_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2263_, 0, v_a_2257_);
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
                    lean_ctor_set_tag(v___x_2267_, 0);
                    v___x_2270_ = v___x_2267_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2271_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2271_, 0, v_a_2265_);
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
    mut v_stderr_2273_: *mut LeanObject,
    mut v___y_2274_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2275_: *mut LeanObject = core::ptr::null_mut();
    v_res_2275_ = l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___lam__1(v_stderr_2273_);
    lean_dec(v_stderr_2273_);
    return v_res_2275_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_External_runInterruptible(
    mut v_timeout_2279_: *mut LeanObject,
    mut v_args_2280_: *mut LeanObject,
    mut v_a_2281_: *mut LeanObject,
    mut v_a_2282_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cmd_2285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_2286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cwd_2287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inheritEnv_2289_: u8 = 0;
    let mut v_setsid_2290_: u8 = 0;
    let mut v___x_2292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2293_: u8 = 0;
    let mut v___x_2295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stdout_2298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stderr_2299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2311_: u8 = 0;
    let mut v_ref_2312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2320_: u8 = 0;
    let mut v_reuseFailAlloc_2321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2322_: u8 = 0;
    let mut v_unused_2323_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2284_ = l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___closed__0;
                v_cmd_2285_ = lean_ctor_get(v_args_2280_, 1);
                v_args_2286_ = lean_ctor_get(v_args_2280_, 2);
                v_cwd_2287_ = lean_ctor_get(v_args_2280_, 3);
                v_env_2288_ = lean_ctor_get(v_args_2280_, 4);
                v_inheritEnv_2289_ = lean_ctor_get_uint8(
                    v_args_2280_,
                    (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                );
                v_setsid_2290_ = lean_ctor_get_uint8(
                    v_args_2280_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
                );
                v_isSharedCheck_2322_ = (!lean_is_exclusive(v_args_2280_)) as u8;
                if v_isSharedCheck_2322_ == 0 {
                    v_unused_2323_ = lean_ctor_get(v_args_2280_, 0);
                    lean_dec(v_unused_2323_);
                    v___x_2292_ = v_args_2280_;
                    v_isShared_2293_ = v_isSharedCheck_2322_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_env_2288_);
                    lean_inc(v_cwd_2287_);
                    lean_inc(v_args_2286_);
                    lean_inc(v_cmd_2285_);
                    lean_dec(v_args_2280_);
                    v___x_2292_ = lean_box(0);
                    v_isShared_2293_ = v_isSharedCheck_2322_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_2293_ == 0 {
                    lean_ctor_set(v___x_2292_, 0, v___x_2284_);
                    v___x_2295_ = v___x_2292_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2321_ = lean_alloc_ctor(0, 5, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2321_, 0, v___x_2284_);
                    lean_ctor_set(v_reuseFailAlloc_2321_, 1, v_cmd_2285_);
                    lean_ctor_set(v_reuseFailAlloc_2321_, 2, v_args_2286_);
                    lean_ctor_set(v_reuseFailAlloc_2321_, 3, v_cwd_2287_);
                    lean_ctor_set(v_reuseFailAlloc_2321_, 4, v_env_2288_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2321_,
                        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                        v_inheritEnv_2289_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2321_,
                        (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
                        v_setsid_2290_,
                    );
                    v___x_2295_ = v_reuseFailAlloc_2321_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2296_ = lean_io_process_spawn(v___x_2295_);
                if lean_obj_tag(v___x_2296_) == 0 {
                    v_a_2297_ = lean_ctor_get(v___x_2296_, 0);
                    lean_inc(v_a_2297_);
                    lean_dec_ref_known(v___x_2296_, 1);
                    v_stdout_2298_ = lean_ctor_get(v_a_2297_, 1);
                    v_stderr_2299_ = lean_ctor_get(v_a_2297_, 2);
                    lean_inc(v_stdout_2298_);
                    v___f_2300_ = lean_alloc_closure(
                        l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___lam__0___boxed
                            as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    lean_closure_set(v___f_2300_, 0, v_stdout_2298_);
                    v___x_2301_ = lean_unsigned_to_nat(9);
                    v___x_2302_ = lean_io_as_task(v___f_2300_, v___x_2301_);
                    lean_inc(v_stderr_2299_);
                    v___f_2303_ = lean_alloc_closure(
                        l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___lam__1___boxed
                            as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    lean_closure_set(v___f_2303_, 0, v_stderr_2299_);
                    v___x_2304_ = lean_io_as_task(v___f_2303_, v___x_2301_);
                    v___x_2305_ = lean_unsigned_to_nat(1000);
                    v___x_2306_ = lean_nat_mul(v_timeout_2279_, v___x_2305_);
                    v___x_2307_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go(v___x_2284_, v___x_2306_, v_a_2297_, v___x_2302_, v___x_2304_, v_a_2281_, v_a_2282_);
                    return v___x_2307_;
                } else {
                    v_a_2308_ = lean_ctor_get(v___x_2296_, 0);
                    v_isSharedCheck_2320_ = (!lean_is_exclusive(v___x_2296_)) as u8;
                    if v_isSharedCheck_2320_ == 0 {
                        v___x_2310_ = v___x_2296_;
                        v_isShared_2311_ = v_isSharedCheck_2320_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2308_);
                        lean_dec(v___x_2296_);
                        v___x_2310_ = lean_box(0);
                        v_isShared_2311_ = v_isSharedCheck_2320_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v_ref_2312_ = lean_ctor_get(v_a_2281_, 5);
                v___x_2313_ = lean_io_error_to_string(v_a_2308_);
                v___x_2314_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_2314_, 0, v___x_2313_);
                v___x_2315_ = l_Lean_MessageData_ofFormat(v___x_2314_);
                lean_inc(v_ref_2312_);
                v___x_2316_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2316_, 0, v_ref_2312_);
                lean_ctor_set(v___x_2316_, 1, v___x_2315_);
                if v_isShared_2311_ == 0 {
                    lean_ctor_set(v___x_2310_, 0, v___x_2316_);
                    v___x_2318_ = v___x_2310_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2319_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2319_, 0, v___x_2316_);
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
    mut v_timeout_2324_: *mut LeanObject,
    mut v_args_2325_: *mut LeanObject,
    mut v_a_2326_: *mut LeanObject,
    mut v_a_2327_: *mut LeanObject,
    mut v_a_2328_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2329_: *mut LeanObject = core::ptr::null_mut();
    v_res_2329_ = l_Lean_Meta_Tactic_BVDecide_External_runInterruptible(
        v_timeout_2324_,
        v_args_2325_,
        v_a_2326_,
        v_a_2327_,
    );
    lean_dec(v_a_2327_);
    lean_dec_ref(v_a_2326_);
    lean_dec(v_timeout_2324_);
    return v_res_2329_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags(
    mut v_mode_2345_: u8,
) -> *mut LeanObject {
    match v_mode_2345_ {
        0 => {
            let mut v___x_2346_: *mut LeanObject = core::ptr::null_mut();
            v___x_2346_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___closed__1;
            return v___x_2346_;
        }
        1 => {
            let mut v___x_2347_: *mut LeanObject = core::ptr::null_mut();
            v___x_2347_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___closed__3;
            return v___x_2347_;
        }
        _ => {
            let mut v___x_2348_: *mut LeanObject = core::ptr::null_mut();
            v___x_2348_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___closed__5;
            return v___x_2348_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___boxed(
    mut v_mode_2349_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_mode_boxed_2350_: u8 = 0;
    let mut v_res_2351_: *mut LeanObject = core::ptr::null_mut();
    v_mode_boxed_2350_ = (lean_unbox(v_mode_2349_) as u8);
    v_res_2351_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags(v_mode_boxed_2350_);
    return v_res_2351_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__0()
-> *mut LeanObject {
    let mut v___x_2352_: *mut LeanObject = core::ptr::null_mut();
    v___x_2352_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_2352_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__1()
-> *mut LeanObject {
    let mut v___x_2353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut LeanObject = core::ptr::null_mut();
    v___x_2353_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__0);
    v___x_2354_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2354_, 0, v___x_2353_);
    return v___x_2354_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__2()
-> *mut LeanObject {
    let mut v___x_2355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: *mut LeanObject = core::ptr::null_mut();
    v___x_2355_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__1);
    v___x_2356_ = lean_unsigned_to_nat(0);
    v___x_2357_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_2357_, 0, v___x_2356_);
    lean_ctor_set(v___x_2357_, 1, v___x_2356_);
    lean_ctor_set(v___x_2357_, 2, v___x_2356_);
    lean_ctor_set(v___x_2357_, 3, v___x_2356_);
    lean_ctor_set(v___x_2357_, 4, v___x_2355_);
    lean_ctor_set(v___x_2357_, 5, v___x_2355_);
    lean_ctor_set(v___x_2357_, 6, v___x_2355_);
    lean_ctor_set(v___x_2357_, 7, v___x_2355_);
    lean_ctor_set(v___x_2357_, 8, v___x_2355_);
    lean_ctor_set(v___x_2357_, 9, v___x_2355_);
    return v___x_2357_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__3()
-> *mut LeanObject {
    let mut v___x_2358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: *mut LeanObject = core::ptr::null_mut();
    v___x_2358_ = lean_unsigned_to_nat(32);
    v___x_2359_ = lean_mk_empty_array_with_capacity(v___x_2358_);
    v___x_2360_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2360_, 0, v___x_2359_);
    return v___x_2360_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__4()
-> *mut LeanObject {
    let mut v___x_2361_: usize = 0;
    let mut v___x_2362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: *mut LeanObject = core::ptr::null_mut();
    v___x_2361_ = 5usize;
    v___x_2362_ = lean_unsigned_to_nat(0);
    v___x_2363_ = lean_unsigned_to_nat(32);
    v___x_2364_ = lean_mk_empty_array_with_capacity(v___x_2363_);
    v___x_2365_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__3);
    v___x_2366_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_2366_, 0, v___x_2365_);
    lean_ctor_set(v___x_2366_, 1, v___x_2364_);
    lean_ctor_set(v___x_2366_, 2, v___x_2362_);
    lean_ctor_set(v___x_2366_, 3, v___x_2362_);
    lean_ctor_set_usize(v___x_2366_, 4, v___x_2361_);
    return v___x_2366_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__5()
-> *mut LeanObject {
    let mut v___x_2367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut LeanObject = core::ptr::null_mut();
    v___x_2367_ = lean_box(1);
    v___x_2368_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__4);
    v___x_2369_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__1);
    v___x_2370_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2370_, 0, v___x_2369_);
    lean_ctor_set(v___x_2370_, 1, v___x_2368_);
    lean_ctor_set(v___x_2370_, 2, v___x_2367_);
    return v___x_2370_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0(
    mut v_msgData_2371_: *mut LeanObject,
    mut v___y_2372_: *mut LeanObject,
    mut v___y_2373_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut LeanObject = core::ptr::null_mut();
    v___x_2375_ = lean_st_ref_get(v___y_2373_);
    v_env_2376_ = lean_ctor_get(v___x_2375_, 0);
    lean_inc_ref(v_env_2376_);
    lean_dec(v___x_2375_);
    v_options_2377_ = lean_ctor_get(v___y_2372_, 2);
    v___x_2378_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__2);
    v___x_2379_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__5);
    lean_inc_ref(v_options_2377_);
    v___x_2380_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_2380_, 0, v_env_2376_);
    lean_ctor_set(v___x_2380_, 1, v___x_2378_);
    lean_ctor_set(v___x_2380_, 2, v___x_2379_);
    lean_ctor_set(v___x_2380_, 3, v_options_2377_);
    v___x_2381_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_2381_, 0, v___x_2380_);
    lean_ctor_set(v___x_2381_, 1, v_msgData_2371_);
    v___x_2382_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2382_, 0, v___x_2381_);
    return v___x_2382_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___boxed(
    mut v_msgData_2383_: *mut LeanObject,
    mut v___y_2384_: *mut LeanObject,
    mut v___y_2385_: *mut LeanObject,
    mut v___y_2386_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2387_: *mut LeanObject = core::ptr::null_mut();
    v_res_2387_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0(v_msgData_2383_, v___y_2384_, v___y_2385_);
    lean_dec(v___y_2385_);
    lean_dec_ref(v___y_2384_);
    return v_res_2387_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0___redArg(
    mut v_msg_2388_: *mut LeanObject,
    mut v___y_2389_: *mut LeanObject,
    mut v___y_2390_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_2392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2397_: u8 = 0;
    let mut v___x_2398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2402_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2392_ = lean_ctor_get(v___y_2389_, 5);
                v___x_2393_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0(v_msg_2388_, v___y_2389_, v___y_2390_);
                v_a_2394_ = lean_ctor_get(v___x_2393_, 0);
                v_isSharedCheck_2402_ = (!lean_is_exclusive(v___x_2393_)) as u8;
                if v_isSharedCheck_2402_ == 0 {
                    v___x_2396_ = v___x_2393_;
                    v_isShared_2397_ = v_isSharedCheck_2402_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_2394_);
                    lean_dec(v___x_2393_);
                    v___x_2396_ = lean_box(0);
                    v_isShared_2397_ = v_isSharedCheck_2402_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_2392_);
                v___x_2398_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2398_, 0, v_ref_2392_);
                lean_ctor_set(v___x_2398_, 1, v_a_2394_);
                if v_isShared_2397_ == 0 {
                    lean_ctor_set_tag(v___x_2396_, 1);
                    lean_ctor_set(v___x_2396_, 0, v___x_2398_);
                    v___x_2400_ = v___x_2396_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2401_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2401_, 0, v___x_2398_);
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
    mut v_msg_2403_: *mut LeanObject,
    mut v___y_2404_: *mut LeanObject,
    mut v___y_2405_: *mut LeanObject,
    mut v___y_2406_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2407_: *mut LeanObject = core::ptr::null_mut();
    v_res_2407_ =
        l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0___redArg(
            v_msg_2403_,
            v___y_2404_,
            v___y_2405_,
        );
    lean_dec(v___y_2405_);
    lean_dec_ref(v___y_2404_);
    return v_res_2407_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__2() -> *mut LeanObject {
    let mut v___x_2410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2411_: *mut LeanObject = core::ptr::null_mut();
    v___x_2410_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseHeader___closed__0;
    v___x_2411_ = lean_string_utf8_byte_size(v___x_2410_);
    return v___x_2411_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__12() -> *mut LeanObject
{
    let mut v___x_2424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut LeanObject = core::ptr::null_mut();
    v___x_2424_ = l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__11;
    v___x_2425_ = lean_string_utf8_byte_size(v___x_2424_);
    return v___x_2425_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__16() -> *mut LeanObject
{
    let mut v___x_2430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut LeanObject = core::ptr::null_mut();
    v___x_2430_ = l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__15;
    v___x_2431_ = l_Lean_MessageData_ofFormat(v___x_2430_);
    return v___x_2431_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_External_satQuery(
    mut v_solverPath_2434_: *mut LeanObject,
    mut v_problemPath_2435_: *mut LeanObject,
    mut v_proofOutput_2436_: *mut LeanObject,
    mut v_timeout_2437_: *mut LeanObject,
    mut v_binaryProofs_2438_: u8,
    mut v_mode_2439_: u8,
    mut v_a_2440_: *mut LeanObject,
    mut v_a_2441_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2458_: u8 = 0;
    let mut v___x_2459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: u8 = 0;
    let mut v___x_2463_: u8 = 0;
    let mut v___x_2464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2470_: u8 = 0;
    let mut v___x_2471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2481_: u8 = 0;
    let mut v_a_2482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2485_: u8 = 0;
    let mut v___x_2487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2490_: u8 = 0;
    let mut v___x_2491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_2507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_2509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: u8 = 0;
    let mut v___x_2515_: u8 = 0;
    let mut v___x_2516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_2519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2522_: u8 = 0;
    let mut v_exitCode_2523_: u32 = 0;
    let mut v_stdout_2524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stderr_2525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: u32 = 0;
    let mut v___x_2527_: u8 = 0;
    let mut v___x_2528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: u8 = 0;
    let mut v___x_2532_: u8 = 0;
    let mut v___x_2533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2540_: u8 = 0;
    let mut v___x_2541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2546_: u8 = 0;
    let mut v___x_2548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2550_: u8 = 0;
    let mut v___x_2551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut LeanObject = core::ptr::null_mut();
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
                lean_dec_ref(v___y_2444_);
                v___x_2448_ = l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__1;
                v___x_2449_ = lean_string_append(v___x_2447_, v___x_2448_);
                v___x_2450_ = lean_string_append(v___x_2449_, v___y_2445_);
                lean_dec_ref(v___y_2445_);
                v___x_2451_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_2451_, 0, v___x_2450_);
                v___x_2452_ = l_Lean_MessageData_ofFormat(v___x_2451_);
                v___x_2453_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0___redArg(v___x_2452_, v_a_2440_, v_a_2441_);
                return v___x_2453_;
            }
            2 => {
                if v___y_2458_ == 0 {
                    v___x_2459_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseHeader___closed__0;
                    v___x_2460_ = lean_string_utf8_byte_size(v___y_2456_);
                    v___x_2461_ = lean_obj_once(
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
                            lean_dec_ref(v___y_2457_);
                            v___x_2464_ = lean_alloc_closure(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parse as *mut core::ffi::c_void, 1, 0);
                            v___x_2465_ = lean_string_to_utf8(v___y_2456_);
                            v___x_2466_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(
                                v___x_2464_,
                                v___x_2465_,
                            );
                            if lean_obj_tag(v___x_2466_) == 0 {
                                v_a_2467_ = lean_ctor_get(v___x_2466_, 0);
                                v_isSharedCheck_2481_ = (!lean_is_exclusive(v___x_2466_)) as u8;
                                if v_isSharedCheck_2481_ == 0 {
                                    v___x_2469_ = v___x_2466_;
                                    v_isShared_2470_ = v_isSharedCheck_2481_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_inc(v_a_2467_);
                                    lean_dec(v___x_2466_);
                                    v___x_2469_ = lean_box(0);
                                    v_isShared_2470_ = v_isSharedCheck_2481_;
                                    state = 3;
                                    continue;
                                }
                            } else {
                                lean_dec_ref(v___y_2456_);
                                v_a_2482_ = lean_ctor_get(v___x_2466_, 0);
                                v_isSharedCheck_2490_ = (!lean_is_exclusive(v___x_2466_)) as u8;
                                if v_isSharedCheck_2490_ == 0 {
                                    v___x_2484_ = v___x_2466_;
                                    v_isShared_2485_ = v_isSharedCheck_2490_;
                                    state = 5;
                                    continue;
                                } else {
                                    lean_inc(v_a_2482_);
                                    lean_dec(v___x_2466_);
                                    v___x_2484_ = lean_box(0);
                                    v_isShared_2485_ = v_isSharedCheck_2490_;
                                    state = 5;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v___y_2457_);
                    lean_dec_ref(v___y_2456_);
                    v___x_2491_ = lean_box(1);
                    v___x_2492_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2492_, 0, v___x_2491_);
                    return v___x_2492_;
                }
            }
            3 => {
                v___x_2471_ = l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__3;
                v___x_2472_ = lean_string_append(v___x_2471_, v_a_2467_);
                lean_dec(v_a_2467_);
                v___x_2473_ = l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__4;
                v___x_2474_ = lean_string_append(v___x_2472_, v___x_2473_);
                v___x_2475_ = lean_string_append(v___x_2474_, v___y_2456_);
                lean_dec_ref(v___y_2456_);
                if v_isShared_2470_ == 0 {
                    lean_ctor_set_tag(v___x_2469_, 3);
                    lean_ctor_set(v___x_2469_, 0, v___x_2475_);
                    v___x_2477_ = v___x_2469_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2480_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2480_, 0, v___x_2475_);
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
                    lean_ctor_set_tag(v___x_2484_, 0);
                    v___x_2487_ = v___x_2484_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2489_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2489_, 0, v_a_2482_);
                    v___x_2487_ = v_reuseFailAlloc_2489_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_2488_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2488_, 0, v___x_2487_);
                return v___x_2488_;
            }
            7 => {
                v___x_2497_ = lean_string_append(v___x_2494_, v___y_2496_);
                v___x_2498_ = l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__7;
                v___x_2499_ = l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__8;
                v___x_2500_ = lean_unsigned_to_nat(6);
                v___x_2501_ = lean_mk_empty_array_with_capacity(v___x_2500_);
                v___x_2502_ = lean_array_push(v___x_2501_, v_problemPath_2435_);
                v___x_2503_ = lean_array_push(v___x_2502_, v_proofOutput_2436_);
                v___x_2504_ = lean_array_push(v___x_2503_, v___x_2493_);
                v___x_2505_ = lean_array_push(v___x_2504_, v___x_2497_);
                v___x_2506_ = lean_array_push(v___x_2505_, v___x_2498_);
                v_args_2507_ = lean_array_push(v___x_2506_, v___x_2499_);
                v___x_2508_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags(v_mode_2439_);
                v_args_2509_ = l_Array_append___redArg(v_args_2507_, v___x_2508_);
                lean_dec_ref(v___x_2508_);
                v___x_2510_ = l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__9;
                v___x_2511_ = lean_box(0);
                v___x_2512_ = lean_unsigned_to_nat(0);
                v___x_2513_ = l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__10;
                v___x_2514_ = 1;
                v___x_2515_ = 0;
                v___x_2516_ = lean_alloc_ctor(0, 5, (2) as u32);
                lean_ctor_set(v___x_2516_, 0, v___x_2510_);
                lean_ctor_set(v___x_2516_, 1, v_solverPath_2434_);
                lean_ctor_set(v___x_2516_, 2, v_args_2509_);
                lean_ctor_set(v___x_2516_, 3, v___x_2511_);
                lean_ctor_set(v___x_2516_, 4, v___x_2513_);
                lean_ctor_set_uint8(
                    v___x_2516_,
                    (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                    v___x_2514_,
                );
                lean_ctor_set_uint8(
                    v___x_2516_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
                    v___x_2515_,
                );
                v___x_2517_ = l_Lean_Meta_Tactic_BVDecide_External_runInterruptible(
                    v_timeout_2437_,
                    v___x_2516_,
                    v_a_2440_,
                    v_a_2441_,
                );
                if lean_obj_tag(v___x_2517_) == 0 {
                    v_a_2518_ = lean_ctor_get(v___x_2517_, 0);
                    lean_inc(v_a_2518_);
                    lean_dec_ref_known(v___x_2517_, 1);
                    if lean_obj_tag(v_a_2518_) == 0 {
                        v_x_2519_ = lean_ctor_get(v_a_2518_, 0);
                        v_isSharedCheck_2540_ = (!lean_is_exclusive(v_a_2518_)) as u8;
                        if v_isSharedCheck_2540_ == 0 {
                            v___x_2521_ = v_a_2518_;
                            v_isShared_2522_ = v_isSharedCheck_2540_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_x_2519_);
                            lean_dec(v_a_2518_);
                            v___x_2521_ = lean_box(0);
                            v_isShared_2522_ = v_isSharedCheck_2540_;
                            state = 8;
                            continue;
                        }
                    } else {
                        v___x_2541_ = lean_obj_once(
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
                    v_a_2543_ = lean_ctor_get(v___x_2517_, 0);
                    v_isSharedCheck_2550_ = (!lean_is_exclusive(v___x_2517_)) as u8;
                    if v_isSharedCheck_2550_ == 0 {
                        v___x_2545_ = v___x_2517_;
                        v_isShared_2546_ = v_isSharedCheck_2550_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_2543_);
                        lean_dec(v___x_2517_);
                        v___x_2545_ = lean_box(0);
                        v_isShared_2546_ = v_isSharedCheck_2550_;
                        state = 10;
                        continue;
                    }
                }
            }
            8 => {
                v_exitCode_2523_ = lean_ctor_get_uint32(
                    v_x_2519_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                );
                v_stdout_2524_ = lean_ctor_get(v_x_2519_, 0);
                lean_inc_ref(v_stdout_2524_);
                v_stderr_2525_ = lean_ctor_get(v_x_2519_, 1);
                lean_inc_ref(v_stderr_2525_);
                lean_dec(v_x_2519_);
                v___x_2526_ = 255;
                v___x_2527_ = lean_uint32_dec_eq(v_exitCode_2523_, v___x_2526_);
                if v___x_2527_ == 0 {
                    lean_del_object(v___x_2521_);
                    v___x_2528_ = l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__11;
                    v___x_2529_ = lean_string_utf8_byte_size(v_stdout_2524_);
                    v___x_2530_ = lean_obj_once(
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
                    lean_dec_ref(v_stdout_2524_);
                    v___x_2533_ = l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__13;
                    v___x_2534_ = lean_string_append(v___x_2533_, v_stderr_2525_);
                    lean_dec_ref(v_stderr_2525_);
                    if v_isShared_2522_ == 0 {
                        lean_ctor_set_tag(v___x_2521_, 3);
                        lean_ctor_set(v___x_2521_, 0, v___x_2534_);
                        v___x_2536_ = v___x_2521_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_2539_ = lean_alloc_ctor(3, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2539_, 0, v___x_2534_);
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
                    v_reuseFailAlloc_2549_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2549_, 0, v_a_2543_);
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
    mut v_solverPath_2553_: *mut LeanObject,
    mut v_problemPath_2554_: *mut LeanObject,
    mut v_proofOutput_2555_: *mut LeanObject,
    mut v_timeout_2556_: *mut LeanObject,
    mut v_binaryProofs_2557_: *mut LeanObject,
    mut v_mode_2558_: *mut LeanObject,
    mut v_a_2559_: *mut LeanObject,
    mut v_a_2560_: *mut LeanObject,
    mut v_a_2561_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_binaryProofs_boxed_2562_: u8 = 0;
    let mut v_mode_boxed_2563_: u8 = 0;
    let mut v_res_2564_: *mut LeanObject = core::ptr::null_mut();
    v_binaryProofs_boxed_2562_ = (lean_unbox(v_binaryProofs_2557_) as u8);
    v_mode_boxed_2563_ = (lean_unbox(v_mode_2558_) as u8);
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
    lean_dec(v_a_2560_);
    lean_dec_ref(v_a_2559_);
    lean_dec(v_timeout_2556_);
    return v_res_2564_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0(
    mut v_00_u03b1_2565_: *mut LeanObject,
    mut v_msg_2566_: *mut LeanObject,
    mut v___y_2567_: *mut LeanObject,
    mut v___y_2568_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2570_: *mut LeanObject = core::ptr::null_mut();
    v___x_2570_ =
        l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0___redArg(
            v_msg_2566_,
            v___y_2567_,
            v___y_2568_,
        );
    return v___x_2570_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0___boxed(
    mut v_00_u03b1_2571_: *mut LeanObject,
    mut v_msg_2572_: *mut LeanObject,
    mut v___y_2573_: *mut LeanObject,
    mut v___y_2574_: *mut LeanObject,
    mut v___y_2575_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2576_: *mut LeanObject = core::ptr::null_mut();
    v_res_2576_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0(
        v_00_u03b1_2571_,
        v_msg_2572_,
        v___y_2573_,
        v___y_2574_,
    );
    lean_dec(v___y_2574_);
    lean_dec_ref(v___y_2573_);
    return v_res_2576_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_BVDecide_External(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Parser(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_CoreM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Syntax(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_BVDecide_External(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_BVDecide_External(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_BVDecide_LRAT_Parser(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_CoreM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Syntax(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_External(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_BVDecide_External(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_BVDecide_External(builtin);
}
