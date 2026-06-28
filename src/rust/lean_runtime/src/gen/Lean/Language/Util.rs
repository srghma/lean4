// Lean compiler output
// Module: Lean.Language.Util
// Imports: Lean.Elab.InfoTree Init.Data.Format.Macro
use crate::r#gen::Init::Data::Format::Macro::{
    initialize_Init_Data_Format_Macro, runtime_initialize_Init_Data_Format_Macro,
};
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_replaceRef,
};
use crate::r#gen::Init::System::IOError::lean_io_error_to_string;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::PersistentArray::{
    l_Lean_PersistentArray_append___redArg, l_Lean_PersistentArray_push___redArg,
    l_Lean_PersistentArray_toArray___redArg,
};
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
use crate::r#gen::Lean::Elab::InfoTree::Main::l_Lean_Elab_InfoTree_format;
use crate::r#gen::Lean::Elab::InfoTree::{
    initialize_Lean_Elab_InfoTree, runtime_initialize_Lean_Elab_InfoTree,
};
use crate::r#gen::Lean::Language::Basic::l_Lean_Language_SnapshotTask_get___redArg;
use crate::r#gen::Lean::Message::{
    l_Lean_Message_toString, l_Lean_MessageData_ofFormat, l_Lean_MessageLog_toList,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Util::Trace::{
    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go, l_Lean_TraceResult_toEmoji,
    l_Lean_trace_profiler, l_Lean_trace_profiler_threshold, l_Lean_trace_profiler_useHeartbeats,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::Float::{lean_float_decLt, lean_float_div, lean_float_sub};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_dec_lt};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_to_list, lean_mk_empty_array_with_capacity,
};
use crate::lean_imports_rs::Init::System::IO::{
    lean_io_get_num_heartbeats, lean_io_mono_nanos_now,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__1_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__2_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__2_value: crate::leanh::LeanStringObject<54> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [60, 101, 120, 99, 101, 112, 116, 105, 111, 110, 32, 116, 104, 114, 111, 119, 110, 32, 119, 104, 105, 108, 101, 32, 112, 114, 111, 100, 117, 99, 105, 110, 103, 32, 116, 114, 97, 99, 101, 32, 110, 111, 100, 101, 32, 109, 101, 115, 115, 97, 103, 101, 62, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__4: f64 = 0.0;
static mut l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__0: f64 =
    0.0;
pub static l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__1_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [105, 110, 102, 111, 0]};
static mut l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__2_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__2_value) as *mut crate::leanh::LeanObject,14231257465488249300 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__4_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__5_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 3, m_data: [10, 226, 128, 162, 32, 0]};
static mut l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__6_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__6_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__7_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [115, 110, 97, 112, 115, 104, 111, 116, 84, 114, 101, 101, 0]};
static mut l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__7_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__8_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__4_value) as *mut crate::leanh::LeanObject,12843180897352504333 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__8_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__7_value) as *mut crate::leanh::LeanObject,11086031300686546955 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__8_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__10_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__4_value) as *mut crate::leanh::LeanObject,12843180897352504333 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__10_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__10_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__1_value) as *mut crate::leanh::LeanObject,879967617213164781 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__10_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__12_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [60, 114, 97, 110, 103, 101, 32, 105, 110, 104, 101, 114, 105, 116, 101, 100, 62, 32, 0]};
static mut l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__12_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__13_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__12_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__13_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__14_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 159, 168, 0]};
static mut l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__14:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__14_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__15_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__14_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__15_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__16_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [44, 32, 0]};
static mut l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__16:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__16_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__17_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__16_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__17:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__17_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__18_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 159, 169, 0]};
static mut l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__18:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__18_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__19_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__18_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__19:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__19_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__20_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [45, 0]};
static mut l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__20:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__20_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__21_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__20_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__21:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__21_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__22_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__22:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__22_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__23_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [60, 110, 111, 32, 114, 97, 110, 103, 101, 62, 32, 0]};
static mut l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__23:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__23_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__24_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__23_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__24:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__24_value
) as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_969_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_970_ = lean_mk_empty_array_with_capacity(v___x_969_);
    v___x_971_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_971_, 0, v___x_970_);
    return v___x_971_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_972_: usize = 0;
    let mut v___x_973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_972_ = 5usize;
    v___x_973_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_974_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_975_ = lean_mk_empty_array_with_capacity(v___x_974_);
    v___x_976_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___redArg___closed__0_once), _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___redArg___closed__0);
    v___x_977_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_977_, 0, v___x_976_);
    crate::leanh::lean_ctor_set(v___x_977_, 1, v___x_975_);
    crate::leanh::lean_ctor_set(v___x_977_, 2, v___x_973_);
    crate::leanh::lean_ctor_set(v___x_977_, 3, v___x_973_);
    crate::leanh::lean_ctor_set_usize(v___x_977_, 4, v___x_972_);
    return v___x_977_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___redArg(
    mut v___y_978_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traces_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_995_: u8 = 0;
    let mut v_tid_996_: u64 = 0;
    let mut v___x_998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_999_: u8 = 0;
    let mut v___x_1000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1009_: u8 = 0;
    let mut v_unused_1010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1011_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_980_ = lean_st_ref_get(v___y_978_);
                v_traceState_981_ = crate::leanh::lean_ctor_get(v___x_980_, 4);
                crate::leanh::lean_inc_ref(v_traceState_981_);
                crate::leanh::lean_dec(v___x_980_);
                v_traces_982_ = crate::leanh::lean_ctor_get(v_traceState_981_, 0);
                crate::leanh::lean_inc_ref(v_traces_982_);
                crate::leanh::lean_dec_ref(v_traceState_981_);
                v___x_983_ = lean_st_ref_take(v___y_978_);
                v_traceState_984_ = crate::leanh::lean_ctor_get(v___x_983_, 4);
                v_env_985_ = crate::leanh::lean_ctor_get(v___x_983_, 0);
                v_nextMacroScope_986_ = crate::leanh::lean_ctor_get(v___x_983_, 1);
                v_ngen_987_ = crate::leanh::lean_ctor_get(v___x_983_, 2);
                v_auxDeclNGen_988_ = crate::leanh::lean_ctor_get(v___x_983_, 3);
                v_cache_989_ = crate::leanh::lean_ctor_get(v___x_983_, 5);
                v_messages_990_ = crate::leanh::lean_ctor_get(v___x_983_, 6);
                v_infoState_991_ = crate::leanh::lean_ctor_get(v___x_983_, 7);
                v_snapshotTasks_992_ = crate::leanh::lean_ctor_get(v___x_983_, 8);
                v_isSharedCheck_1011_ = (!crate::leanh::lean_is_exclusive(v___x_983_)) as u8;
                if v_isSharedCheck_1011_ == 0 {
                    v___x_994_ = v___x_983_;
                    v_isShared_995_ = v_isSharedCheck_1011_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_992_);
                    crate::leanh::lean_inc(v_infoState_991_);
                    crate::leanh::lean_inc(v_messages_990_);
                    crate::leanh::lean_inc(v_cache_989_);
                    crate::leanh::lean_inc(v_traceState_984_);
                    crate::leanh::lean_inc(v_auxDeclNGen_988_);
                    crate::leanh::lean_inc(v_ngen_987_);
                    crate::leanh::lean_inc(v_nextMacroScope_986_);
                    crate::leanh::lean_inc(v_env_985_);
                    crate::leanh::lean_dec(v___x_983_);
                    v___x_994_ = crate::leanh::lean_box(0);
                    v_isShared_995_ = v_isSharedCheck_1011_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_tid_996_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_984_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_1009_ = (!crate::leanh::lean_is_exclusive(v_traceState_984_)) as u8;
                if v_isSharedCheck_1009_ == 0 {
                    v_unused_1010_ = crate::leanh::lean_ctor_get(v_traceState_984_, 0);
                    crate::leanh::lean_dec(v_unused_1010_);
                    v___x_998_ = v_traceState_984_;
                    v_isShared_999_ = v_isSharedCheck_1009_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_traceState_984_);
                    v___x_998_ = crate::leanh::lean_box(0);
                    v_isShared_999_ = v_isSharedCheck_1009_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1000_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___redArg___closed__1_once), _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___redArg___closed__1);
                if v_isShared_999_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_998_, 0, v___x_1000_);
                    v___x_1002_ = v___x_998_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1008_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1008_, 0, v___x_1000_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_1008_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_996_,
                    );
                    v___x_1002_ = v_reuseFailAlloc_1008_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_995_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_994_, 4, v___x_1002_);
                    v___x_1004_ = v___x_994_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1007_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_env_985_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1007_, 1, v_nextMacroScope_986_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1007_, 2, v_ngen_987_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1007_, 3, v_auxDeclNGen_988_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1007_, 4, v___x_1002_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1007_, 5, v_cache_989_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1007_, 6, v_messages_990_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1007_, 7, v_infoState_991_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1007_, 8, v_snapshotTasks_992_);
                    v___x_1004_ = v_reuseFailAlloc_1007_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1005_ = lean_st_ref_set(v___y_978_, v___x_1004_);
                v___x_1006_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1006_, 0, v_traces_982_);
                return v___x_1006_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___redArg___boxed(
    mut v___y_1012_: *mut crate::leanh::LeanObject,
    mut v___y_1013_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1014_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___redArg(v___y_1012_);
    crate::leanh::lean_dec(v___y_1012_);
    return v_res_1014_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4(
    mut v___y_1015_: *mut crate::leanh::LeanObject,
    mut v___y_1016_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1018_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___redArg(v___y_1016_);
    return v___x_1018_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___boxed(
    mut v___y_1019_: *mut crate::leanh::LeanObject,
    mut v___y_1020_: *mut crate::leanh::LeanObject,
    mut v___y_1021_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1022_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4(v___y_1019_, v___y_1020_);
    crate::leanh::lean_dec(v___y_1020_);
    crate::leanh::lean_dec_ref(v___y_1019_);
    return v_res_1022_;
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5(
    mut v_opts_1023_: *mut crate::leanh::LeanObject,
    mut v_opt_1024_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_1026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_1025_ = crate::leanh::lean_ctor_get(v_opt_1024_, 0);
    v_defValue_1026_ = crate::leanh::lean_ctor_get(v_opt_1024_, 1);
    v_map_1027_ = crate::leanh::lean_ctor_get(v_opts_1023_, 0);
    v___x_1028_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_1027_,
            v_name_1025_,
        );
    if crate::leanh::lean_obj_tag(v___x_1028_) == 0 {
        let mut v___x_1029_: u8 = 0;
        v___x_1029_ = (crate::leanh::lean_unbox(v_defValue_1026_) as u8);
        return v___x_1029_;
    } else {
        let mut v_val_1030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1030_ = crate::leanh::lean_ctor_get(v___x_1028_, 0);
        crate::leanh::lean_inc(v_val_1030_);
        crate::leanh::lean_dec_ref_known(v___x_1028_, 1);
        if crate::leanh::lean_obj_tag(v_val_1030_) == 1 {
            let mut v_v_1031_: u8 = 0;
            v_v_1031_ = crate::leanh::lean_ctor_get_uint8(v_val_1030_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_1030_, 0);
            return v_v_1031_;
        } else {
            let mut v___x_1032_: u8 = 0;
            crate::leanh::lean_dec(v_val_1030_);
            v___x_1032_ = (crate::leanh::lean_unbox(v_defValue_1026_) as u8);
            return v___x_1032_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5___boxed(
    mut v_opts_1033_: *mut crate::leanh::LeanObject,
    mut v_opt_1034_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1035_: u8 = 0;
    let mut v_r_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1035_ = l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5(v_opts_1033_, v_opt_1034_);
    crate::leanh::lean_dec_ref(v_opt_1034_);
    crate::leanh::lean_dec_ref(v_opts_1033_);
    v_r_1036_ = crate::leanh::lean_box((v_res_1035_) as usize);
    return v_r_1036_;
}
pub unsafe fn l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___lam__0(
    mut v___x_1037_: *mut crate::leanh::LeanObject,
    mut v_x_1038_: *mut crate::leanh::LeanObject,
    mut v___y_1039_: *mut crate::leanh::LeanObject,
    mut v___y_1040_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1042_ = l_Lean_MessageData_ofFormat(v___x_1037_);
    v___x_1043_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1043_, 0, v___x_1042_);
    return v___x_1043_;
}
pub unsafe fn l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___lam__0___boxed(
    mut v___x_1044_: *mut crate::leanh::LeanObject,
    mut v_x_1045_: *mut crate::leanh::LeanObject,
    mut v___y_1046_: *mut crate::leanh::LeanObject,
    mut v___y_1047_: *mut crate::leanh::LeanObject,
    mut v___y_1048_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1049_ = l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___lam__0(
        v___x_1044_,
        v_x_1045_,
        v___y_1046_,
        v___y_1047_,
    );
    crate::leanh::lean_dec(v___y_1047_);
    crate::leanh::lean_dec_ref(v___y_1046_);
    crate::leanh::lean_dec_ref(v_x_1045_);
    return v_res_1049_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1050_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1050_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1051_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__0);
    v___x_1052_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1052_, 0, v___x_1051_);
    return v___x_1052_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1053_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__1);
    v___x_1054_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1055_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1055_, 0, v___x_1054_);
    crate::leanh::lean_ctor_set(v___x_1055_, 1, v___x_1054_);
    crate::leanh::lean_ctor_set(v___x_1055_, 2, v___x_1054_);
    crate::leanh::lean_ctor_set(v___x_1055_, 3, v___x_1054_);
    crate::leanh::lean_ctor_set(v___x_1055_, 4, v___x_1053_);
    crate::leanh::lean_ctor_set(v___x_1055_, 5, v___x_1053_);
    crate::leanh::lean_ctor_set(v___x_1055_, 6, v___x_1053_);
    crate::leanh::lean_ctor_set(v___x_1055_, 7, v___x_1053_);
    crate::leanh::lean_ctor_set(v___x_1055_, 8, v___x_1053_);
    crate::leanh::lean_ctor_set(v___x_1055_, 9, v___x_1053_);
    return v___x_1055_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1056_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1057_ = lean_mk_empty_array_with_capacity(v___x_1056_);
    v___x_1058_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1058_, 0, v___x_1057_);
    return v___x_1058_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1059_: usize = 0;
    let mut v___x_1060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1059_ = 5usize;
    v___x_1060_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1061_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1062_ = lean_mk_empty_array_with_capacity(v___x_1061_);
    v___x_1063_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__3);
    v___x_1064_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_1064_, 0, v___x_1063_);
    crate::leanh::lean_ctor_set(v___x_1064_, 1, v___x_1062_);
    crate::leanh::lean_ctor_set(v___x_1064_, 2, v___x_1060_);
    crate::leanh::lean_ctor_set(v___x_1064_, 3, v___x_1060_);
    crate::leanh::lean_ctor_set_usize(v___x_1064_, 4, v___x_1059_);
    return v___x_1064_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1065_ = crate::leanh::lean_box(1);
    v___x_1066_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__4);
    v___x_1067_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__1);
    v___x_1068_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1068_, 0, v___x_1067_);
    crate::leanh::lean_ctor_set(v___x_1068_, 1, v___x_1066_);
    crate::leanh::lean_ctor_set(v___x_1068_, 2, v___x_1065_);
    return v___x_1068_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2(
    mut v_msgData_1069_: *mut crate::leanh::LeanObject,
    mut v___y_1070_: *mut crate::leanh::LeanObject,
    mut v___y_1071_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1073_ = lean_st_ref_get(v___y_1071_);
    v_env_1074_ = crate::leanh::lean_ctor_get(v___x_1073_, 0);
    crate::leanh::lean_inc_ref(v_env_1074_);
    crate::leanh::lean_dec(v___x_1073_);
    v_options_1075_ = crate::leanh::lean_ctor_get(v___y_1070_, 2);
    v___x_1076_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__2);
    v___x_1077_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__5);
    crate::leanh::lean_inc_ref(v_options_1075_);
    v___x_1078_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1078_, 0, v_env_1074_);
    crate::leanh::lean_ctor_set(v___x_1078_, 1, v___x_1076_);
    crate::leanh::lean_ctor_set(v___x_1078_, 2, v___x_1077_);
    crate::leanh::lean_ctor_set(v___x_1078_, 3, v_options_1075_);
    v___x_1079_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1079_, 0, v___x_1078_);
    crate::leanh::lean_ctor_set(v___x_1079_, 1, v_msgData_1069_);
    v___x_1080_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1080_, 0, v___x_1079_);
    return v___x_1080_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___boxed(
    mut v_msgData_1081_: *mut crate::leanh::LeanObject,
    mut v___y_1082_: *mut crate::leanh::LeanObject,
    mut v___y_1083_: *mut crate::leanh::LeanObject,
    mut v___y_1084_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1085_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2(v_msgData_1081_, v___y_1082_, v___y_1083_);
    crate::leanh::lean_dec(v___y_1083_);
    crate::leanh::lean_dec_ref(v___y_1082_);
    return v_res_1085_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__0()
-> f64 {
    let mut v___x_1086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1087_: f64 = 0.0;
    v___x_1086_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1087_ = lean_float_of_nat(v___x_1086_);
    return v___x_1087_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2(
    mut v_cls_1091_: *mut crate::leanh::LeanObject,
    mut v_msg_1092_: *mut crate::leanh::LeanObject,
    mut v___y_1093_: *mut crate::leanh::LeanObject,
    mut v___y_1094_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1101_: u8 = 0;
    let mut v___x_1102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1114_: u8 = 0;
    let mut v_tid_1115_: u64 = 0;
    let mut v_traces_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1119_: u8 = 0;
    let mut v___x_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1121_: f64 = 0.0;
    let mut v___x_1122_: u8 = 0;
    let mut v___x_1123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1140_: u8 = 0;
    let mut v_isSharedCheck_1141_: u8 = 0;
    let mut v_isSharedCheck_1142_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1096_ = crate::leanh::lean_ctor_get(v___y_1093_, 5);
                v___x_1097_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2(v_msg_1092_, v___y_1093_, v___y_1094_);
                v_a_1098_ = crate::leanh::lean_ctor_get(v___x_1097_, 0);
                v_isSharedCheck_1142_ = (!crate::leanh::lean_is_exclusive(v___x_1097_)) as u8;
                if v_isSharedCheck_1142_ == 0 {
                    v___x_1100_ = v___x_1097_;
                    v_isShared_1101_ = v_isSharedCheck_1142_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1098_);
                    crate::leanh::lean_dec(v___x_1097_);
                    v___x_1100_ = crate::leanh::lean_box(0);
                    v_isShared_1101_ = v_isSharedCheck_1142_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1102_ = lean_st_ref_take(v___y_1094_);
                v_traceState_1103_ = crate::leanh::lean_ctor_get(v___x_1102_, 4);
                v_env_1104_ = crate::leanh::lean_ctor_get(v___x_1102_, 0);
                v_nextMacroScope_1105_ = crate::leanh::lean_ctor_get(v___x_1102_, 1);
                v_ngen_1106_ = crate::leanh::lean_ctor_get(v___x_1102_, 2);
                v_auxDeclNGen_1107_ = crate::leanh::lean_ctor_get(v___x_1102_, 3);
                v_cache_1108_ = crate::leanh::lean_ctor_get(v___x_1102_, 5);
                v_messages_1109_ = crate::leanh::lean_ctor_get(v___x_1102_, 6);
                v_infoState_1110_ = crate::leanh::lean_ctor_get(v___x_1102_, 7);
                v_snapshotTasks_1111_ = crate::leanh::lean_ctor_get(v___x_1102_, 8);
                v_isSharedCheck_1141_ = (!crate::leanh::lean_is_exclusive(v___x_1102_)) as u8;
                if v_isSharedCheck_1141_ == 0 {
                    v___x_1113_ = v___x_1102_;
                    v_isShared_1114_ = v_isSharedCheck_1141_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_1111_);
                    crate::leanh::lean_inc(v_infoState_1110_);
                    crate::leanh::lean_inc(v_messages_1109_);
                    crate::leanh::lean_inc(v_cache_1108_);
                    crate::leanh::lean_inc(v_traceState_1103_);
                    crate::leanh::lean_inc(v_auxDeclNGen_1107_);
                    crate::leanh::lean_inc(v_ngen_1106_);
                    crate::leanh::lean_inc(v_nextMacroScope_1105_);
                    crate::leanh::lean_inc(v_env_1104_);
                    crate::leanh::lean_dec(v___x_1102_);
                    v___x_1113_ = crate::leanh::lean_box(0);
                    v_isShared_1114_ = v_isSharedCheck_1141_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_1115_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_1103_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_1116_ = crate::leanh::lean_ctor_get(v_traceState_1103_, 0);
                v_isSharedCheck_1140_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_1103_)) as u8;
                if v_isSharedCheck_1140_ == 0 {
                    v___x_1118_ = v_traceState_1103_;
                    v_isShared_1119_ = v_isSharedCheck_1140_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_1116_);
                    crate::leanh::lean_dec(v_traceState_1103_);
                    v___x_1118_ = crate::leanh::lean_box(0);
                    v_isShared_1119_ = v_isSharedCheck_1140_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1120_ = crate::leanh::lean_box(0);
                v___x_1121_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__0_once), _init_l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__0);
                v___x_1122_ = 0;
                v___x_1123_ = l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__1;
                v___x_1124_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v___x_1124_, 0, v_cls_1091_);
                crate::leanh::lean_ctor_set(v___x_1124_, 1, v___x_1120_);
                crate::leanh::lean_ctor_set(v___x_1124_, 2, v___x_1123_);
                crate::leanh::lean_ctor_set_float(
                    v___x_1124_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_1121_,
                );
                crate::leanh::lean_ctor_set_float(
                    v___x_1124_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_1121_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1124_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_1122_,
                );
                v___x_1125_ = l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__2;
                v___x_1126_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1126_, 0, v___x_1124_);
                crate::leanh::lean_ctor_set(v___x_1126_, 1, v_a_1098_);
                crate::leanh::lean_ctor_set(v___x_1126_, 2, v___x_1125_);
                crate::leanh::lean_inc(v_ref_1096_);
                v___x_1127_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1127_, 0, v_ref_1096_);
                crate::leanh::lean_ctor_set(v___x_1127_, 1, v___x_1126_);
                v___x_1128_ = l_Lean_PersistentArray_push___redArg(v_traces_1116_, v___x_1127_);
                if v_isShared_1119_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1118_, 0, v___x_1128_);
                    v___x_1130_ = v___x_1118_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1139_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1139_, 0, v___x_1128_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_1139_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_1115_,
                    );
                    v___x_1130_ = v_reuseFailAlloc_1139_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1114_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1113_, 4, v___x_1130_);
                    v___x_1132_ = v___x_1113_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1138_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_env_1104_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1138_, 1, v_nextMacroScope_1105_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1138_, 2, v_ngen_1106_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1138_, 3, v_auxDeclNGen_1107_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1138_, 4, v___x_1130_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1138_, 5, v_cache_1108_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1138_, 6, v_messages_1109_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1138_, 7, v_infoState_1110_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1138_, 8, v_snapshotTasks_1111_);
                    v___x_1132_ = v_reuseFailAlloc_1138_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1133_ = lean_st_ref_set(v___y_1094_, v___x_1132_);
                v___x_1134_ = crate::leanh::lean_box(0);
                if v_isShared_1101_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1100_, 0, v___x_1134_);
                    v___x_1136_ = v___x_1100_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1137_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1137_, 0, v___x_1134_);
                    v___x_1136_ = v_reuseFailAlloc_1137_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1136_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___boxed(
    mut v_cls_1143_: *mut crate::leanh::LeanObject,
    mut v_msg_1144_: *mut crate::leanh::LeanObject,
    mut v___y_1145_: *mut crate::leanh::LeanObject,
    mut v___y_1146_: *mut crate::leanh::LeanObject,
    mut v___y_1147_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1148_ = l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2(v_cls_1143_, v_msg_1144_, v___y_1145_, v___y_1146_);
    crate::leanh::lean_dec(v___y_1146_);
    crate::leanh::lean_dec_ref(v___y_1145_);
    return v_res_1148_;
}
pub unsafe fn l_List_foldl___at___00Std_Format_prefixJoin___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3_spec__4(
    mut v_pre_1149_: *mut crate::leanh::LeanObject,
    mut v_x_1150_: *mut crate::leanh::LeanObject,
    mut v_x_1151_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1156_: u8 = 0;
    let mut v___x_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1163_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1151_) == 0 {
                    crate::leanh::lean_dec(v_pre_1149_);
                    return v_x_1150_;
                } else {
                    v_head_1152_ = crate::leanh::lean_ctor_get(v_x_1151_, 0);
                    v_tail_1153_ = crate::leanh::lean_ctor_get(v_x_1151_, 1);
                    v_isSharedCheck_1163_ = (!crate::leanh::lean_is_exclusive(v_x_1151_)) as u8;
                    if v_isSharedCheck_1163_ == 0 {
                        v___x_1155_ = v_x_1151_;
                        v_isShared_1156_ = v_isSharedCheck_1163_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1153_);
                        crate::leanh::lean_inc(v_head_1152_);
                        crate::leanh::lean_dec(v_x_1151_);
                        v___x_1155_ = crate::leanh::lean_box(0);
                        v_isShared_1156_ = v_isSharedCheck_1163_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_pre_1149_);
                if v_isShared_1156_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1155_, 5);
                    crate::leanh::lean_ctor_set(v___x_1155_, 1, v_pre_1149_);
                    crate::leanh::lean_ctor_set(v___x_1155_, 0, v_x_1150_);
                    v___x_1158_ = v___x_1155_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1162_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_x_1150_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1162_, 1, v_pre_1149_);
                    v___x_1158_ = v_reuseFailAlloc_1162_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1159_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1159_, 0, v_head_1152_);
                v___x_1160_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1160_, 0, v___x_1158_);
                crate::leanh::lean_ctor_set(v___x_1160_, 1, v___x_1159_);
                v_x_1150_ = v___x_1160_;
                v_x_1151_ = v_tail_1153_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_prefixJoin___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3(
    mut v_pre_1164_: *mut crate::leanh::LeanObject,
    mut v_x_1165_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1171_: u8 = 0;
    let mut v___x_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1177_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1165_) == 0 {
                    crate::leanh::lean_dec(v_pre_1164_);
                    v___x_1166_ = crate::leanh::lean_box(0);
                    return v___x_1166_;
                } else {
                    v_head_1167_ = crate::leanh::lean_ctor_get(v_x_1165_, 0);
                    v_tail_1168_ = crate::leanh::lean_ctor_get(v_x_1165_, 1);
                    v_isSharedCheck_1177_ = (!crate::leanh::lean_is_exclusive(v_x_1165_)) as u8;
                    if v_isSharedCheck_1177_ == 0 {
                        v___x_1170_ = v_x_1165_;
                        v_isShared_1171_ = v_isSharedCheck_1177_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1168_);
                        crate::leanh::lean_inc(v_head_1167_);
                        crate::leanh::lean_dec(v_x_1165_);
                        v___x_1170_ = crate::leanh::lean_box(0);
                        v_isShared_1171_ = v_isSharedCheck_1177_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1172_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1172_, 0, v_head_1167_);
                crate::leanh::lean_inc(v_pre_1164_);
                if v_isShared_1171_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1170_, 5);
                    crate::leanh::lean_ctor_set(v___x_1170_, 1, v___x_1172_);
                    crate::leanh::lean_ctor_set(v___x_1170_, 0, v_pre_1164_);
                    v___x_1174_ = v___x_1170_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1176_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1176_, 0, v_pre_1164_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1176_, 1, v___x_1172_);
                    v___x_1174_ = v_reuseFailAlloc_1176_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1175_ = l_List_foldl___at___00Std_Format_prefixJoin___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3_spec__4(v_pre_1164_, v___x_1174_, v_tail_1168_);
                return v___x_1175_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___redArg(
    mut v_x_1178_: *mut crate::leanh::LeanObject,
    mut v_x_1179_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1187_: u8 = 0;
    let mut v___x_1188_: u8 = 0;
    let mut v___x_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1194_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1178_) == 0 {
                    v___x_1181_ = l_List_reverse___redArg(v_x_1179_);
                    v___x_1182_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1182_, 0, v___x_1181_);
                    return v___x_1182_;
                } else {
                    v_head_1183_ = crate::leanh::lean_ctor_get(v_x_1178_, 0);
                    v_tail_1184_ = crate::leanh::lean_ctor_get(v_x_1178_, 1);
                    v_isSharedCheck_1194_ = (!crate::leanh::lean_is_exclusive(v_x_1178_)) as u8;
                    if v_isSharedCheck_1194_ == 0 {
                        v___x_1186_ = v_x_1178_;
                        v_isShared_1187_ = v_isSharedCheck_1194_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1184_);
                        crate::leanh::lean_inc(v_head_1183_);
                        crate::leanh::lean_dec(v_x_1178_);
                        v___x_1186_ = crate::leanh::lean_box(0);
                        v_isShared_1187_ = v_isSharedCheck_1194_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1188_ = 0;
                v___x_1189_ = l_Lean_Message_toString(v_head_1183_, v___x_1188_);
                if v_isShared_1187_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1186_, 1, v_x_1179_);
                    crate::leanh::lean_ctor_set(v___x_1186_, 0, v___x_1189_);
                    v___x_1191_ = v___x_1186_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1193_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1193_, 0, v___x_1189_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1193_, 1, v_x_1179_);
                    v___x_1191_ = v_reuseFailAlloc_1193_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_x_1178_ = v_tail_1184_;
                v_x_1179_ = v___x_1191_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___redArg___boxed(
    mut v_x_1195_: *mut crate::leanh::LeanObject,
    mut v_x_1196_: *mut crate::leanh::LeanObject,
    mut v___y_1197_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1198_ = l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___redArg(v_x_1195_, v_x_1196_);
    return v_res_1198_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9_spec__10(
    mut v_sz_1199_: usize,
    mut v_i_1200_: usize,
    mut v_bs_1201_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1202_: u8 = 0;
    let mut v_v_1203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_1204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: usize = 0;
    let mut v___x_1208_: usize = 0;
    let mut v___x_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1202_ = lean_usize_dec_lt(v_i_1200_, v_sz_1199_);
                if v___x_1202_ == 0 {
                    return v_bs_1201_;
                } else {
                    v_v_1203_ = lean_array_uget_borrowed(v_bs_1201_, v_i_1200_);
                    v_msg_1204_ = crate::leanh::lean_ctor_get(v_v_1203_, 1);
                    crate::leanh::lean_inc_ref(v_msg_1204_);
                    v___x_1205_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1206_ = lean_array_uset(v_bs_1201_, v_i_1200_, v___x_1205_);
                    v___x_1207_ = 1usize;
                    v___x_1208_ = lean_usize_add(v_i_1200_, v___x_1207_);
                    v___x_1209_ = lean_array_uset(v_bs_x27_1206_, v_i_1200_, v_msg_1204_);
                    v_i_1200_ = v___x_1208_;
                    v_bs_1201_ = v___x_1209_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9_spec__10___boxed(
    mut v_sz_1211_: *mut crate::leanh::LeanObject,
    mut v_i_1212_: *mut crate::leanh::LeanObject,
    mut v_bs_1213_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1214_: usize = 0;
    let mut v_i_boxed_1215_: usize = 0;
    let mut v_res_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1214_ = crate::leanh::lean_unbox_usize(v_sz_1211_);
    crate::leanh::lean_dec(v_sz_1211_);
    v_i_boxed_1215_ = crate::leanh::lean_unbox_usize(v_i_1212_);
    crate::leanh::lean_dec(v_i_1212_);
    v_res_1216_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9_spec__10(v_sz_boxed_1214_, v_i_boxed_1215_, v_bs_1213_);
    return v_res_1216_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9(
    mut v_oldTraces_1217_: *mut crate::leanh::LeanObject,
    mut v_data_1218_: *mut crate::leanh::LeanObject,
    mut v_ref_1219_: *mut crate::leanh::LeanObject,
    mut v_msg_1220_: *mut crate::leanh::LeanObject,
    mut v___y_1221_: *mut crate::leanh::LeanObject,
    mut v___y_1222_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1236_: u8 = 0;
    let mut v_cancelTk_x3f_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1238_: u8 = 0;
    let mut v_inheritedTraceOptions_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traces_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1246_: usize = 0;
    let mut v___x_1247_: usize = 0;
    let mut v___x_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1254_: u8 = 0;
    let mut v___x_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1267_: u8 = 0;
    let mut v_tid_1268_: u64 = 0;
    let mut v___x_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1271_: u8 = 0;
    let mut v___x_1272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1285_: u8 = 0;
    let mut v_unused_1286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1287_: u8 = 0;
    let mut v_isSharedCheck_1288_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_1224_ = crate::leanh::lean_ctor_get(v___y_1221_, 0);
                v_fileMap_1225_ = crate::leanh::lean_ctor_get(v___y_1221_, 1);
                v_options_1226_ = crate::leanh::lean_ctor_get(v___y_1221_, 2);
                v_currRecDepth_1227_ = crate::leanh::lean_ctor_get(v___y_1221_, 3);
                v_maxRecDepth_1228_ = crate::leanh::lean_ctor_get(v___y_1221_, 4);
                v_ref_1229_ = crate::leanh::lean_ctor_get(v___y_1221_, 5);
                v_currNamespace_1230_ = crate::leanh::lean_ctor_get(v___y_1221_, 6);
                v_openDecls_1231_ = crate::leanh::lean_ctor_get(v___y_1221_, 7);
                v_initHeartbeats_1232_ = crate::leanh::lean_ctor_get(v___y_1221_, 8);
                v_maxHeartbeats_1233_ = crate::leanh::lean_ctor_get(v___y_1221_, 9);
                v_quotContext_1234_ = crate::leanh::lean_ctor_get(v___y_1221_, 10);
                v_currMacroScope_1235_ = crate::leanh::lean_ctor_get(v___y_1221_, 11);
                v_diag_1236_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_1221_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_1237_ = crate::leanh::lean_ctor_get(v___y_1221_, 12);
                v_suppressElabErrors_1238_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_1221_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_1239_ = crate::leanh::lean_ctor_get(v___y_1221_, 13);
                v___x_1240_ = lean_st_ref_get(v___y_1222_);
                v_traceState_1241_ = crate::leanh::lean_ctor_get(v___x_1240_, 4);
                crate::leanh::lean_inc_ref(v_traceState_1241_);
                crate::leanh::lean_dec(v___x_1240_);
                v_traces_1242_ = crate::leanh::lean_ctor_get(v_traceState_1241_, 0);
                crate::leanh::lean_inc_ref(v_traces_1242_);
                crate::leanh::lean_dec_ref(v_traceState_1241_);
                v_ref_1243_ = l_Lean_replaceRef(v_ref_1219_, v_ref_1229_);
                crate::leanh::lean_inc_ref(v_inheritedTraceOptions_1239_);
                crate::leanh::lean_inc(v_cancelTk_x3f_1237_);
                crate::leanh::lean_inc(v_currMacroScope_1235_);
                crate::leanh::lean_inc(v_quotContext_1234_);
                crate::leanh::lean_inc(v_maxHeartbeats_1233_);
                crate::leanh::lean_inc(v_initHeartbeats_1232_);
                crate::leanh::lean_inc(v_openDecls_1231_);
                crate::leanh::lean_inc(v_currNamespace_1230_);
                crate::leanh::lean_inc(v_maxRecDepth_1228_);
                crate::leanh::lean_inc(v_currRecDepth_1227_);
                crate::leanh::lean_inc_ref(v_options_1226_);
                crate::leanh::lean_inc_ref(v_fileMap_1225_);
                crate::leanh::lean_inc_ref(v_fileName_1224_);
                v___x_1244_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_1244_, 0, v_fileName_1224_);
                crate::leanh::lean_ctor_set(v___x_1244_, 1, v_fileMap_1225_);
                crate::leanh::lean_ctor_set(v___x_1244_, 2, v_options_1226_);
                crate::leanh::lean_ctor_set(v___x_1244_, 3, v_currRecDepth_1227_);
                crate::leanh::lean_ctor_set(v___x_1244_, 4, v_maxRecDepth_1228_);
                crate::leanh::lean_ctor_set(v___x_1244_, 5, v_ref_1243_);
                crate::leanh::lean_ctor_set(v___x_1244_, 6, v_currNamespace_1230_);
                crate::leanh::lean_ctor_set(v___x_1244_, 7, v_openDecls_1231_);
                crate::leanh::lean_ctor_set(v___x_1244_, 8, v_initHeartbeats_1232_);
                crate::leanh::lean_ctor_set(v___x_1244_, 9, v_maxHeartbeats_1233_);
                crate::leanh::lean_ctor_set(v___x_1244_, 10, v_quotContext_1234_);
                crate::leanh::lean_ctor_set(v___x_1244_, 11, v_currMacroScope_1235_);
                crate::leanh::lean_ctor_set(v___x_1244_, 12, v_cancelTk_x3f_1237_);
                crate::leanh::lean_ctor_set(v___x_1244_, 13, v_inheritedTraceOptions_1239_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1244_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                    v_diag_1236_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1244_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_1238_,
                );
                v___x_1245_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1242_);
                crate::leanh::lean_dec_ref(v_traces_1242_);
                v_sz_1246_ = lean_array_size(v___x_1245_);
                v___x_1247_ = 0usize;
                v___x_1248_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9_spec__10(v_sz_1246_, v___x_1247_, v___x_1245_);
                v_msg_1249_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v_msg_1249_, 0, v_data_1218_);
                crate::leanh::lean_ctor_set(v_msg_1249_, 1, v_msg_1220_);
                crate::leanh::lean_ctor_set(v_msg_1249_, 2, v___x_1248_);
                v___x_1250_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2(v_msg_1249_, v___x_1244_, v___y_1222_);
                crate::leanh::lean_dec_ref_known(v___x_1244_, 14);
                v_a_1251_ = crate::leanh::lean_ctor_get(v___x_1250_, 0);
                v_isSharedCheck_1288_ = (!crate::leanh::lean_is_exclusive(v___x_1250_)) as u8;
                if v_isSharedCheck_1288_ == 0 {
                    v___x_1253_ = v___x_1250_;
                    v_isShared_1254_ = v_isSharedCheck_1288_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1251_);
                    crate::leanh::lean_dec(v___x_1250_);
                    v___x_1253_ = crate::leanh::lean_box(0);
                    v_isShared_1254_ = v_isSharedCheck_1288_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1255_ = lean_st_ref_take(v___y_1222_);
                v_traceState_1256_ = crate::leanh::lean_ctor_get(v___x_1255_, 4);
                v_env_1257_ = crate::leanh::lean_ctor_get(v___x_1255_, 0);
                v_nextMacroScope_1258_ = crate::leanh::lean_ctor_get(v___x_1255_, 1);
                v_ngen_1259_ = crate::leanh::lean_ctor_get(v___x_1255_, 2);
                v_auxDeclNGen_1260_ = crate::leanh::lean_ctor_get(v___x_1255_, 3);
                v_cache_1261_ = crate::leanh::lean_ctor_get(v___x_1255_, 5);
                v_messages_1262_ = crate::leanh::lean_ctor_get(v___x_1255_, 6);
                v_infoState_1263_ = crate::leanh::lean_ctor_get(v___x_1255_, 7);
                v_snapshotTasks_1264_ = crate::leanh::lean_ctor_get(v___x_1255_, 8);
                v_isSharedCheck_1287_ = (!crate::leanh::lean_is_exclusive(v___x_1255_)) as u8;
                if v_isSharedCheck_1287_ == 0 {
                    v___x_1266_ = v___x_1255_;
                    v_isShared_1267_ = v_isSharedCheck_1287_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_1264_);
                    crate::leanh::lean_inc(v_infoState_1263_);
                    crate::leanh::lean_inc(v_messages_1262_);
                    crate::leanh::lean_inc(v_cache_1261_);
                    crate::leanh::lean_inc(v_traceState_1256_);
                    crate::leanh::lean_inc(v_auxDeclNGen_1260_);
                    crate::leanh::lean_inc(v_ngen_1259_);
                    crate::leanh::lean_inc(v_nextMacroScope_1258_);
                    crate::leanh::lean_inc(v_env_1257_);
                    crate::leanh::lean_dec(v___x_1255_);
                    v___x_1266_ = crate::leanh::lean_box(0);
                    v_isShared_1267_ = v_isSharedCheck_1287_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_1268_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_1256_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_1285_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_1256_)) as u8;
                if v_isSharedCheck_1285_ == 0 {
                    v_unused_1286_ = crate::leanh::lean_ctor_get(v_traceState_1256_, 0);
                    crate::leanh::lean_dec(v_unused_1286_);
                    v___x_1270_ = v_traceState_1256_;
                    v_isShared_1271_ = v_isSharedCheck_1285_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_traceState_1256_);
                    v___x_1270_ = crate::leanh::lean_box(0);
                    v_isShared_1271_ = v_isSharedCheck_1285_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1272_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1272_, 0, v_ref_1219_);
                crate::leanh::lean_ctor_set(v___x_1272_, 1, v_a_1251_);
                v___x_1273_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1217_, v___x_1272_);
                if v_isShared_1271_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1270_, 0, v___x_1273_);
                    v___x_1275_ = v___x_1270_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1284_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1284_, 0, v___x_1273_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_1284_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_1268_,
                    );
                    v___x_1275_ = v_reuseFailAlloc_1284_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1267_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1266_, 4, v___x_1275_);
                    v___x_1277_ = v___x_1266_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1283_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1283_, 0, v_env_1257_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1283_, 1, v_nextMacroScope_1258_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1283_, 2, v_ngen_1259_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1283_, 3, v_auxDeclNGen_1260_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1283_, 4, v___x_1275_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1283_, 5, v_cache_1261_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1283_, 6, v_messages_1262_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1283_, 7, v_infoState_1263_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1283_, 8, v_snapshotTasks_1264_);
                    v___x_1277_ = v_reuseFailAlloc_1283_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1278_ = lean_st_ref_set(v___y_1222_, v___x_1277_);
                v___x_1279_ = crate::leanh::lean_box(0);
                if v_isShared_1254_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1253_, 0, v___x_1279_);
                    v___x_1281_ = v___x_1253_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1282_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1282_, 0, v___x_1279_);
                    v___x_1281_ = v_reuseFailAlloc_1282_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1281_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9___boxed(
    mut v_oldTraces_1289_: *mut crate::leanh::LeanObject,
    mut v_data_1290_: *mut crate::leanh::LeanObject,
    mut v_ref_1291_: *mut crate::leanh::LeanObject,
    mut v_msg_1292_: *mut crate::leanh::LeanObject,
    mut v___y_1293_: *mut crate::leanh::LeanObject,
    mut v___y_1294_: *mut crate::leanh::LeanObject,
    mut v___y_1295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1296_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9(v_oldTraces_1289_, v_data_1290_, v_ref_1291_, v_msg_1292_, v___y_1293_, v___y_1294_);
    crate::leanh::lean_dec(v___y_1294_);
    crate::leanh::lean_dec_ref(v___y_1293_);
    return v_res_1296_;
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11(
    mut v_opts_1297_: *mut crate::leanh::LeanObject,
    mut v_opt_1298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_1299_ = crate::leanh::lean_ctor_get(v_opt_1298_, 0);
    v_defValue_1300_ = crate::leanh::lean_ctor_get(v_opt_1298_, 1);
    v_map_1301_ = crate::leanh::lean_ctor_get(v_opts_1297_, 0);
    v___x_1302_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_1301_,
            v_name_1299_,
        );
    if crate::leanh::lean_obj_tag(v___x_1302_) == 0 {
        crate::leanh::lean_inc(v_defValue_1300_);
        return v_defValue_1300_;
    } else {
        let mut v_val_1303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1303_ = crate::leanh::lean_ctor_get(v___x_1302_, 0);
        crate::leanh::lean_inc(v_val_1303_);
        crate::leanh::lean_dec_ref_known(v___x_1302_, 1);
        if crate::leanh::lean_obj_tag(v_val_1303_) == 3 {
            let mut v_v_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_v_1304_ = crate::leanh::lean_ctor_get(v_val_1303_, 0);
            crate::leanh::lean_inc(v_v_1304_);
            crate::leanh::lean_dec_ref_known(v_val_1303_, 1);
            return v_v_1304_;
        } else {
            crate::leanh::lean_dec(v_val_1303_);
            crate::leanh::lean_inc(v_defValue_1300_);
            return v_defValue_1300_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11___boxed(
    mut v_opts_1305_: *mut crate::leanh::LeanObject,
    mut v_opt_1306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1307_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11(v_opts_1305_, v_opt_1306_);
    crate::leanh::lean_dec_ref(v_opt_1306_);
    crate::leanh::lean_dec_ref(v_opts_1305_);
    return v_res_1307_;
}
pub unsafe fn l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8(
    mut v_e_1308_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_e_1308_) == 0 {
        let mut v___x_1309_: u8 = 0;
        v___x_1309_ = 2;
        return v___x_1309_;
    } else {
        let mut v___x_1310_: u8 = 0;
        v___x_1310_ = 0;
        return v___x_1310_;
    }
}
pub unsafe fn l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8___boxed(
    mut v_e_1311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1312_: u8 = 0;
    let mut v_r_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1312_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8(v_e_1311_);
    crate::leanh::lean_dec_ref(v_e_1311_);
    v_r_1313_ = crate::leanh::lean_box((v_res_1312_) as usize);
    return v_r_1313_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__10___redArg(
    mut v_x_1314_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1319_: u8 = 0;
    let mut v___x_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1323_: u8 = 0;
    let mut v_a_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1327_: u8 = 0;
    let mut v___x_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1331_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1314_) == 0 {
                    v_a_1316_ = crate::leanh::lean_ctor_get(v_x_1314_, 0);
                    v_isSharedCheck_1323_ = (!crate::leanh::lean_is_exclusive(v_x_1314_)) as u8;
                    if v_isSharedCheck_1323_ == 0 {
                        v___x_1318_ = v_x_1314_;
                        v_isShared_1319_ = v_isSharedCheck_1323_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1316_);
                        crate::leanh::lean_dec(v_x_1314_);
                        v___x_1318_ = crate::leanh::lean_box(0);
                        v_isShared_1319_ = v_isSharedCheck_1323_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1324_ = crate::leanh::lean_ctor_get(v_x_1314_, 0);
                    v_isSharedCheck_1331_ = (!crate::leanh::lean_is_exclusive(v_x_1314_)) as u8;
                    if v_isSharedCheck_1331_ == 0 {
                        v___x_1326_ = v_x_1314_;
                        v_isShared_1327_ = v_isSharedCheck_1331_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1324_);
                        crate::leanh::lean_dec(v_x_1314_);
                        v___x_1326_ = crate::leanh::lean_box(0);
                        v_isShared_1327_ = v_isSharedCheck_1331_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1319_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1318_, 1);
                    v___x_1321_ = v___x_1318_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1322_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_a_1316_);
                    v___x_1321_ = v_reuseFailAlloc_1322_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1321_;
            }
            3 => {
                if v_isShared_1327_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1326_, 0);
                    v___x_1329_ = v___x_1326_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1330_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1330_, 0, v_a_1324_);
                    v___x_1329_ = v_reuseFailAlloc_1330_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1329_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__10___redArg___boxed(
    mut v_x_1332_: *mut crate::leanh::LeanObject,
    mut v___y_1333_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1334_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__10___redArg(v_x_1332_);
    return v_res_1334_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1336_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__0;
    v___x_1337_ = l_Lean_stringToMessageData(v___x_1336_);
    return v___x_1337_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1339_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__2;
    v___x_1340_ = l_Lean_stringToMessageData(v___x_1339_);
    return v___x_1340_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__4()
-> f64 {
    let mut v___x_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: f64 = 0.0;
    v___x_1341_ = crate::leanh::lean_unsigned_to_nat(1000);
    v___x_1342_ = lean_float_of_nat(v___x_1341_);
    return v___x_1342_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6(
    mut v_cls_1343_: *mut crate::leanh::LeanObject,
    mut v_collapsed_1344_: u8,
    mut v_tag_1345_: *mut crate::leanh::LeanObject,
    mut v_opts_1346_: *mut crate::leanh::LeanObject,
    mut v_clsEnabled_1347_: u8,
    mut v_oldTraces_1348_: *mut crate::leanh::LeanObject,
    mut v_msg_1349_: *mut crate::leanh::LeanObject,
    mut v_resStartStop_1350_: *mut crate::leanh::LeanObject,
    mut v___y_1351_: *mut crate::leanh::LeanObject,
    mut v___y_1352_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1358_: u8 = 0;
    let mut v___y_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1369_: u8 = 0;
    let mut v___x_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: u8 = 0;
    let mut v___y_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_1375_: u8 = 0;
    let mut v___x_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: f64 = 0.0;
    let mut v_data_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1388_: f64 = 0.0;
    let mut v___x_1389_: f64 = 0.0;
    let mut v_reuseFailAlloc_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1398_: u8 = 0;
    let mut v___x_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1411_: u8 = 0;
    let mut v_tid_1412_: u64 = 0;
    let mut v_traces_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1416_: u8 = 0;
    let mut v___x_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1426_: u8 = 0;
    let mut v_isSharedCheck_1427_: u8 = 0;
    let mut v___y_1429_: f64 = 0.0;
    let mut v___x_1430_: f64 = 0.0;
    let mut v___x_1431_: f64 = 0.0;
    let mut v___x_1432_: f64 = 0.0;
    let mut v___x_1433_: u8 = 0;
    let mut v___x_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: u8 = 0;
    let mut v___x_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: f64 = 0.0;
    let mut v___x_1439_: f64 = 0.0;
    let mut v___x_1440_: f64 = 0.0;
    let mut v___x_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: f64 = 0.0;
    let mut v_isSharedCheck_1444_: u8 = 0;
    let mut v_isSharedCheck_1445_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_1354_ = crate::leanh::lean_ctor_get(v_resStartStop_1350_, 0);
                v_snd_1355_ = crate::leanh::lean_ctor_get(v_resStartStop_1350_, 1);
                v_isSharedCheck_1445_ =
                    (!crate::leanh::lean_is_exclusive(v_resStartStop_1350_)) as u8;
                if v_isSharedCheck_1445_ == 0 {
                    v___x_1357_ = v_resStartStop_1350_;
                    v_isShared_1358_ = v_isSharedCheck_1445_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1355_);
                    crate::leanh::lean_inc(v_fst_1354_);
                    crate::leanh::lean_dec(v_resStartStop_1350_);
                    v___x_1357_ = crate::leanh::lean_box(0);
                    v_isShared_1358_ = v_isSharedCheck_1445_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_1365_ = crate::leanh::lean_ctor_get(v_snd_1355_, 0);
                v_snd_1366_ = crate::leanh::lean_ctor_get(v_snd_1355_, 1);
                v_isSharedCheck_1444_ = (!crate::leanh::lean_is_exclusive(v_snd_1355_)) as u8;
                if v_isSharedCheck_1444_ == 0 {
                    v___x_1368_ = v_snd_1355_;
                    v_isShared_1369_ = v_isSharedCheck_1444_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1366_);
                    crate::leanh::lean_inc(v_fst_1365_);
                    crate::leanh::lean_dec(v_snd_1355_);
                    v___x_1368_ = crate::leanh::lean_box(0);
                    v_isShared_1369_ = v_isSharedCheck_1444_;
                    state = 3;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v___y_1360_);
                v___x_1363_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9(v_oldTraces_1348_, v_data_1362_, v___y_1360_, v___y_1361_, v___y_1351_, v___y_1352_);
                if crate::leanh::lean_obj_tag(v___x_1363_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_1363_, 1);
                    v___x_1364_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__10___redArg(v_fst_1354_);
                    return v___x_1364_;
                } else {
                    crate::leanh::lean_dec(v_fst_1354_);
                    return v___x_1363_;
                }
            }
            3 => {
                v___x_1370_ = l_Lean_trace_profiler;
                v___x_1371_ = l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5(v_opts_1346_, v___x_1370_);
                if v___x_1371_ == 0 {
                    v___y_1398_ = v___x_1371_;
                    state = 8;
                    continue;
                } else {
                    v___x_1434_ = l_Lean_trace_profiler_useHeartbeats;
                    v___x_1435_ = l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5(v_opts_1346_, v___x_1434_);
                    if v___x_1435_ == 0 {
                        v___x_1436_ = l_Lean_trace_profiler_threshold;
                        v___x_1437_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11(v_opts_1346_, v___x_1436_);
                        v___x_1438_ = lean_float_of_nat(v___x_1437_);
                        v___x_1439_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__4_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__4);
                        v___x_1440_ = lean_float_div(v___x_1438_, v___x_1439_);
                        v___y_1429_ = v___x_1440_;
                        state = 13;
                        continue;
                    } else {
                        v___x_1441_ = l_Lean_trace_profiler_threshold;
                        v___x_1442_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11(v_opts_1346_, v___x_1441_);
                        v___x_1443_ = lean_float_of_nat(v___x_1442_);
                        v___y_1429_ = v___x_1443_;
                        state = 13;
                        continue;
                    }
                }
            }
            4 => {
                v_result_1375_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8(v_fst_1354_);
                v___x_1376_ = l_Lean_TraceResult_toEmoji(v_result_1375_);
                v___x_1377_ = l_Lean_stringToMessageData(v___x_1376_);
                v___x_1378_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__1_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__1);
                if v_isShared_1369_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1368_, 7);
                    crate::leanh::lean_ctor_set(v___x_1368_, 1, v___x_1378_);
                    crate::leanh::lean_ctor_set(v___x_1368_, 0, v___x_1377_);
                    v___x_1380_ = v___x_1368_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1391_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1391_, 0, v___x_1377_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1391_, 1, v___x_1378_);
                    v___x_1380_ = v_reuseFailAlloc_1391_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_1358_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1357_, 7);
                    crate::leanh::lean_ctor_set(v___x_1357_, 1, v_a_1374_);
                    crate::leanh::lean_ctor_set(v___x_1357_, 0, v___x_1380_);
                    v_m_1382_ = v___x_1357_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1390_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1390_, 0, v___x_1380_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1390_, 1, v_a_1374_);
                    v_m_1382_ = v_reuseFailAlloc_1390_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_1383_ = crate::leanh::lean_box((v_result_1375_) as usize);
                v___x_1384_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1384_, 0, v___x_1383_);
                v___x_1385_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__0_once), _init_l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__0);
                crate::leanh::lean_inc_ref(v_tag_1345_);
                crate::leanh::lean_inc_ref(v___x_1384_);
                crate::leanh::lean_inc(v_cls_1343_);
                v_data_1386_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v_data_1386_, 0, v_cls_1343_);
                crate::leanh::lean_ctor_set(v_data_1386_, 1, v___x_1384_);
                crate::leanh::lean_ctor_set(v_data_1386_, 2, v_tag_1345_);
                crate::leanh::lean_ctor_set_float(
                    v_data_1386_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_1385_,
                );
                crate::leanh::lean_ctor_set_float(
                    v_data_1386_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_1385_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v_data_1386_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v_collapsed_1344_,
                );
                if v___x_1371_ == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_1384_, 1);
                    crate::leanh::lean_dec(v_snd_1366_);
                    crate::leanh::lean_dec(v_fst_1365_);
                    crate::leanh::lean_dec_ref(v_tag_1345_);
                    crate::leanh::lean_dec(v_cls_1343_);
                    v___y_1360_ = v___y_1373_;
                    v___y_1361_ = v_m_1382_;
                    v_data_1362_ = v_data_1386_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref_known(v_data_1386_, 3);
                    v_data_1387_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                    crate::leanh::lean_ctor_set(v_data_1387_, 0, v_cls_1343_);
                    crate::leanh::lean_ctor_set(v_data_1387_, 1, v___x_1384_);
                    crate::leanh::lean_ctor_set(v_data_1387_, 2, v_tag_1345_);
                    v___x_1388_ = crate::leanh::lean_unbox_float(v_fst_1365_);
                    crate::leanh::lean_dec(v_fst_1365_);
                    crate::leanh::lean_ctor_set_float(
                        v_data_1387_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v___x_1388_,
                    );
                    v___x_1389_ = crate::leanh::lean_unbox_float(v_snd_1366_);
                    crate::leanh::lean_dec(v_snd_1366_);
                    crate::leanh::lean_ctor_set_float(
                        v_data_1387_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                        v___x_1389_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_data_1387_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                        v_collapsed_1344_,
                    );
                    v___y_1360_ = v___y_1373_;
                    v___y_1361_ = v_m_1382_;
                    v_data_1362_ = v_data_1387_;
                    state = 2;
                    continue;
                }
            }
            7 => {
                v_ref_1393_ = crate::leanh::lean_ctor_get(v___y_1351_, 5);
                crate::leanh::lean_inc(v___y_1352_);
                crate::leanh::lean_inc_ref(v___y_1351_);
                crate::leanh::lean_inc(v_fst_1354_);
                v___x_1394_ = crate::leanh::lean_apply_4(
                    v_msg_1349_,
                    v_fst_1354_,
                    v___y_1351_,
                    v___y_1352_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_1394_) == 0 {
                    v_a_1395_ = crate::leanh::lean_ctor_get(v___x_1394_, 0);
                    crate::leanh::lean_inc(v_a_1395_);
                    crate::leanh::lean_dec_ref_known(v___x_1394_, 1);
                    v___y_1373_ = v_ref_1393_;
                    v_a_1374_ = v_a_1395_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_1394_, 1);
                    v___x_1396_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__3_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__3);
                    v___y_1373_ = v_ref_1393_;
                    v_a_1374_ = v___x_1396_;
                    state = 4;
                    continue;
                }
            }
            8 => {
                if v_clsEnabled_1347_ == 0 {
                    if v___y_1398_ == 0 {
                        crate::leanh::lean_del_object(v___x_1368_);
                        crate::leanh::lean_dec(v_snd_1366_);
                        crate::leanh::lean_dec(v_fst_1365_);
                        crate::leanh::lean_del_object(v___x_1357_);
                        crate::leanh::lean_dec_ref(v_msg_1349_);
                        crate::leanh::lean_dec_ref(v_tag_1345_);
                        crate::leanh::lean_dec(v_cls_1343_);
                        v___x_1399_ = lean_st_ref_take(v___y_1352_);
                        v_traceState_1400_ = crate::leanh::lean_ctor_get(v___x_1399_, 4);
                        v_env_1401_ = crate::leanh::lean_ctor_get(v___x_1399_, 0);
                        v_nextMacroScope_1402_ = crate::leanh::lean_ctor_get(v___x_1399_, 1);
                        v_ngen_1403_ = crate::leanh::lean_ctor_get(v___x_1399_, 2);
                        v_auxDeclNGen_1404_ = crate::leanh::lean_ctor_get(v___x_1399_, 3);
                        v_cache_1405_ = crate::leanh::lean_ctor_get(v___x_1399_, 5);
                        v_messages_1406_ = crate::leanh::lean_ctor_get(v___x_1399_, 6);
                        v_infoState_1407_ = crate::leanh::lean_ctor_get(v___x_1399_, 7);
                        v_snapshotTasks_1408_ = crate::leanh::lean_ctor_get(v___x_1399_, 8);
                        v_isSharedCheck_1427_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1399_)) as u8;
                        if v_isSharedCheck_1427_ == 0 {
                            v___x_1410_ = v___x_1399_;
                            v_isShared_1411_ = v_isSharedCheck_1427_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snapshotTasks_1408_);
                            crate::leanh::lean_inc(v_infoState_1407_);
                            crate::leanh::lean_inc(v_messages_1406_);
                            crate::leanh::lean_inc(v_cache_1405_);
                            crate::leanh::lean_inc(v_traceState_1400_);
                            crate::leanh::lean_inc(v_auxDeclNGen_1404_);
                            crate::leanh::lean_inc(v_ngen_1403_);
                            crate::leanh::lean_inc(v_nextMacroScope_1402_);
                            crate::leanh::lean_inc(v_env_1401_);
                            crate::leanh::lean_dec(v___x_1399_);
                            v___x_1410_ = crate::leanh::lean_box(0);
                            v_isShared_1411_ = v_isSharedCheck_1427_;
                            state = 9;
                            continue;
                        }
                    } else {
                        state = 7;
                        continue;
                    }
                } else {
                    state = 7;
                    continue;
                }
            }
            9 => {
                v_tid_1412_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_1400_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_1413_ = crate::leanh::lean_ctor_get(v_traceState_1400_, 0);
                v_isSharedCheck_1426_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_1400_)) as u8;
                if v_isSharedCheck_1426_ == 0 {
                    v___x_1415_ = v_traceState_1400_;
                    v_isShared_1416_ = v_isSharedCheck_1426_;
                    state = 10;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_1413_);
                    crate::leanh::lean_dec(v_traceState_1400_);
                    v___x_1415_ = crate::leanh::lean_box(0);
                    v_isShared_1416_ = v_isSharedCheck_1426_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_1417_ =
                    l_Lean_PersistentArray_append___redArg(v_oldTraces_1348_, v_traces_1413_);
                crate::leanh::lean_dec_ref(v_traces_1413_);
                if v_isShared_1416_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1415_, 0, v___x_1417_);
                    v___x_1419_ = v___x_1415_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1425_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1425_, 0, v___x_1417_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_1425_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_1412_,
                    );
                    v___x_1419_ = v_reuseFailAlloc_1425_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_1411_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1410_, 4, v___x_1419_);
                    v___x_1421_ = v___x_1410_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1424_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1424_, 0, v_env_1401_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1424_, 1, v_nextMacroScope_1402_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1424_, 2, v_ngen_1403_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1424_, 3, v_auxDeclNGen_1404_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1424_, 4, v___x_1419_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1424_, 5, v_cache_1405_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1424_, 6, v_messages_1406_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1424_, 7, v_infoState_1407_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1424_, 8, v_snapshotTasks_1408_);
                    v___x_1421_ = v_reuseFailAlloc_1424_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_1422_ = lean_st_ref_set(v___y_1352_, v___x_1421_);
                v___x_1423_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__10___redArg(v_fst_1354_);
                return v___x_1423_;
            }
            13 => {
                v___x_1430_ = crate::leanh::lean_unbox_float(v_snd_1366_);
                v___x_1431_ = crate::leanh::lean_unbox_float(v_fst_1365_);
                v___x_1432_ = lean_float_sub(v___x_1430_, v___x_1431_);
                v___x_1433_ = lean_float_decLt(v___y_1429_, v___x_1432_);
                v___y_1398_ = v___x_1433_;
                state = 8;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___boxed(
    mut v_cls_1446_: *mut crate::leanh::LeanObject,
    mut v_collapsed_1447_: *mut crate::leanh::LeanObject,
    mut v_tag_1448_: *mut crate::leanh::LeanObject,
    mut v_opts_1449_: *mut crate::leanh::LeanObject,
    mut v_clsEnabled_1450_: *mut crate::leanh::LeanObject,
    mut v_oldTraces_1451_: *mut crate::leanh::LeanObject,
    mut v_msg_1452_: *mut crate::leanh::LeanObject,
    mut v_resStartStop_1453_: *mut crate::leanh::LeanObject,
    mut v___y_1454_: *mut crate::leanh::LeanObject,
    mut v___y_1455_: *mut crate::leanh::LeanObject,
    mut v___y_1456_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_collapsed_boxed_1457_: u8 = 0;
    let mut v_clsEnabled_boxed_1458_: u8 = 0;
    let mut v_res_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_1457_ = (crate::leanh::lean_unbox(v_collapsed_1447_) as u8);
    v_clsEnabled_boxed_1458_ = (crate::leanh::lean_unbox(v_clsEnabled_1450_) as u8);
    v_res_1459_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6(v_cls_1446_, v_collapsed_boxed_1457_, v_tag_1448_, v_opts_1449_, v_clsEnabled_boxed_1458_, v_oldTraces_1451_, v_msg_1452_, v_resStartStop_1453_, v___y_1454_, v___y_1455_);
    crate::leanh::lean_dec(v___y_1455_);
    crate::leanh::lean_dec_ref(v___y_1454_);
    crate::leanh::lean_dec_ref(v_opts_1449_);
    return v_res_1459_;
}
pub unsafe fn _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__0()
-> f64 {
    let mut v___x_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: f64 = 0.0;
    v___x_1460_ = crate::leanh::lean_unsigned_to_nat(1000000000);
    v___x_1461_ = lean_float_of_nat(v___x_1460_);
    return v___x_1461_;
}
pub unsafe fn _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1474_ = l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__8;
    v___x_1475_ = l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__3;
    v___x_1476_ = l_Lean_Name_append(v___x_1475_, v___x_1474_);
    return v___x_1476_;
}
pub unsafe fn _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1480_ =
        l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__10;
    v___x_1481_ = l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__3;
    v___x_1482_ = l_Lean_Name_append(v___x_1481_, v___x_1480_);
    return v___x_1482_;
}
pub unsafe fn l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go(
    mut v_range_x3f_1503_: *mut crate::leanh::LeanObject,
    mut v_s_1504_: *mut crate::leanh::LeanObject,
    mut v_a_1505_: *mut crate::leanh::LeanObject,
    mut v_a_1506_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1510_: u8 = 0;
    let mut v___y_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1512_: u8 = 0;
    let mut v___y_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: f64 = 0.0;
    let mut v___x_1522_: f64 = 0.0;
    let mut v___x_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1530_: u8 = 0;
    let mut v___y_1531_: u8 = 0;
    let mut v___y_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1543_: u8 = 0;
    let mut v___y_1544_: u8 = 0;
    let mut v___y_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1556_: u8 = 0;
    let mut v___y_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1558_: u8 = 0;
    let mut v___y_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1571_: u8 = 0;
    let mut v___y_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1573_: u8 = 0;
    let mut v___y_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: f64 = 0.0;
    let mut v___x_1582_: f64 = 0.0;
    let mut v___x_1583_: f64 = 0.0;
    let mut v___x_1584_: f64 = 0.0;
    let mut v___x_1585_: f64 = 0.0;
    let mut v___x_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1594_: u8 = 0;
    let mut v___y_1595_: u8 = 0;
    let mut v___y_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1607_: u8 = 0;
    let mut v___y_1608_: u8 = 0;
    let mut v___y_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1620_: u8 = 0;
    let mut v___y_1621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1622_: u8 = 0;
    let mut v___y_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1637_: u8 = 0;
    let mut v___y_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1639_: u8 = 0;
    let mut v___y_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: u8 = 0;
    let mut v___x_1649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: u8 = 0;
    let mut v___x_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1666_: u8 = 0;
    let mut v___x_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1673_: u8 = 0;
    let mut v___x_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: u8 = 0;
    let mut v___x_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1692_: u8 = 0;
    let mut v___x_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1699_: u8 = 0;
    let mut v___x_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1704_: u8 = 0;
    let mut v___x_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1708_: u8 = 0;
    let mut v_element_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_children_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1713_: u8 = 0;
    let mut v_desc_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diagnostics_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoTree_x3f_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_desc_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgLog_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1724_: u8 = 0;
    let mut v___x_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_1732_: u8 = 0;
    let mut v___x_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1737_: u8 = 0;
    let mut v___x_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1746_: u8 = 0;
    let mut v_unused_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: u8 = 0;
    let mut v___x_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: u8 = 0;
    let mut v___x_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1763_: u8 = 0;
    let mut v_val_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1767_: u8 = 0;
    let mut v___x_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: u8 = 0;
    let mut v___x_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1783_: u8 = 0;
    let mut v___x_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1795_: u8 = 0;
    let mut v_isSharedCheck_1796_: u8 = 0;
    let mut v___x_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1801_: u8 = 0;
    let mut v_unused_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1807_: u8 = 0;
    let mut v___x_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1811_: u8 = 0;
    let mut v_isSharedCheck_1812_: u8 = 0;
    let mut v_unused_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1820_: u8 = 0;
    let mut v_fileMap_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1826_: u8 = 0;
    let mut v___x_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_line_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_column_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1832_: u8 = 0;
    let mut v___x_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_line_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_column_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1838_: u8 = 0;
    let mut v___x_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1872_: u8 = 0;
    let mut v_isSharedCheck_1873_: u8 = 0;
    let mut v_isSharedCheck_1874_: u8 = 0;
    let mut v_isSharedCheck_1875_: u8 = 0;
    let mut v___x_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1878_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_element_1709_ = crate::leanh::lean_ctor_get(v_s_1504_, 0);
                v_children_1710_ = crate::leanh::lean_ctor_get(v_s_1504_, 1);
                v_isSharedCheck_1878_ = (!crate::leanh::lean_is_exclusive(v_s_1504_)) as u8;
                if v_isSharedCheck_1878_ == 0 {
                    v___x_1712_ = v_s_1504_;
                    v_isShared_1713_ = v_isSharedCheck_1878_;
                    state = 16;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_children_1710_);
                    crate::leanh::lean_inc(v_element_1709_);
                    crate::leanh::lean_dec(v_s_1504_);
                    v___x_1712_ = crate::leanh::lean_box(0);
                    v_isShared_1713_ = v_isSharedCheck_1878_;
                    state = 16;
                    continue;
                }
            }
            1 => {
                v___x_1520_ = lean_io_get_num_heartbeats();
                v___x_1521_ = lean_float_of_nat(v___y_1516_);
                v___x_1522_ = lean_float_of_nat(v___x_1520_);
                v___x_1523_ = crate::leanh::lean_box_float(v___x_1521_);
                v___x_1524_ = crate::leanh::lean_box_float(v___x_1522_);
                v___x_1525_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1525_, 0, v___x_1523_);
                crate::leanh::lean_ctor_set(v___x_1525_, 1, v___x_1524_);
                v___x_1526_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1526_, 0, v_a_1519_);
                crate::leanh::lean_ctor_set(v___x_1526_, 1, v___x_1525_);
                crate::leanh::lean_inc_ref(v___y_1514_);
                crate::leanh::lean_inc(v___y_1515_);
                v___x_1527_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6(v___y_1515_, v___y_1512_, v___y_1514_, v___y_1517_, v___y_1510_, v___y_1513_, v___y_1509_, v___x_1526_, v___y_1518_, v___y_1511_);
                return v___x_1527_;
            }
            2 => {
                v___x_1540_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1540_, 0, v_a_1539_);
                v___y_1509_ = v___y_1529_;
                v___y_1510_ = v___y_1530_;
                v___y_1511_ = v___y_1532_;
                v___y_1512_ = v___y_1531_;
                v___y_1513_ = v___y_1535_;
                v___y_1514_ = v___y_1534_;
                v___y_1515_ = v___y_1533_;
                v___y_1516_ = v___y_1536_;
                v___y_1517_ = v___y_1537_;
                v___y_1518_ = v___y_1538_;
                v_a_1519_ = v___x_1540_;
                state = 1;
                continue;
            }
            3 => {
                v___x_1553_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1553_, 0, v_a_1552_);
                v___y_1509_ = v___y_1542_;
                v___y_1510_ = v___y_1543_;
                v___y_1511_ = v___y_1545_;
                v___y_1512_ = v___y_1544_;
                v___y_1513_ = v___y_1548_;
                v___y_1514_ = v___y_1547_;
                v___y_1515_ = v___y_1546_;
                v___y_1516_ = v___y_1549_;
                v___y_1517_ = v___y_1550_;
                v___y_1518_ = v___y_1551_;
                v_a_1519_ = v___x_1553_;
                state = 1;
                continue;
            }
            4 => {
                if crate::leanh::lean_obj_tag(v___y_1565_) == 0 {
                    v_a_1566_ = crate::leanh::lean_ctor_get(v___y_1565_, 0);
                    crate::leanh::lean_inc(v_a_1566_);
                    crate::leanh::lean_dec_ref_known(v___y_1565_, 1);
                    v___y_1529_ = v___y_1555_;
                    v___y_1530_ = v___y_1556_;
                    v___y_1531_ = v___y_1558_;
                    v___y_1532_ = v___y_1557_;
                    v___y_1533_ = v___y_1561_;
                    v___y_1534_ = v___y_1560_;
                    v___y_1535_ = v___y_1559_;
                    v___y_1536_ = v___y_1562_;
                    v___y_1537_ = v___y_1563_;
                    v___y_1538_ = v___y_1564_;
                    v_a_1539_ = v_a_1566_;
                    state = 2;
                    continue;
                } else {
                    v_a_1567_ = crate::leanh::lean_ctor_get(v___y_1565_, 0);
                    crate::leanh::lean_inc(v_a_1567_);
                    crate::leanh::lean_dec_ref_known(v___y_1565_, 1);
                    v___y_1542_ = v___y_1555_;
                    v___y_1543_ = v___y_1556_;
                    v___y_1544_ = v___y_1558_;
                    v___y_1545_ = v___y_1557_;
                    v___y_1546_ = v___y_1561_;
                    v___y_1547_ = v___y_1560_;
                    v___y_1548_ = v___y_1559_;
                    v___y_1549_ = v___y_1562_;
                    v___y_1550_ = v___y_1563_;
                    v___y_1551_ = v___y_1564_;
                    v_a_1552_ = v_a_1567_;
                    state = 3;
                    continue;
                }
            }
            5 => {
                v___x_1580_ = lean_io_mono_nanos_now();
                v___x_1581_ = lean_float_of_nat(v___y_1570_);
                v___x_1582_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__0_once), _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__0);
                v___x_1583_ = lean_float_div(v___x_1581_, v___x_1582_);
                v___x_1584_ = lean_float_of_nat(v___x_1580_);
                v___x_1585_ = lean_float_div(v___x_1584_, v___x_1582_);
                v___x_1586_ = crate::leanh::lean_box_float(v___x_1583_);
                v___x_1587_ = crate::leanh::lean_box_float(v___x_1585_);
                v___x_1588_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1588_, 0, v___x_1586_);
                crate::leanh::lean_ctor_set(v___x_1588_, 1, v___x_1587_);
                v___x_1589_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1589_, 0, v_a_1579_);
                crate::leanh::lean_ctor_set(v___x_1589_, 1, v___x_1588_);
                crate::leanh::lean_inc_ref(v___y_1575_);
                crate::leanh::lean_inc(v___y_1576_);
                v___x_1590_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6(v___y_1576_, v___y_1573_, v___y_1575_, v___y_1577_, v___y_1571_, v___y_1574_, v___y_1569_, v___x_1589_, v___y_1578_, v___y_1572_);
                return v___x_1590_;
            }
            6 => {
                v___x_1603_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1603_, 0, v_a_1602_);
                v___y_1569_ = v___y_1592_;
                v___y_1570_ = v___y_1593_;
                v___y_1571_ = v___y_1594_;
                v___y_1572_ = v___y_1596_;
                v___y_1573_ = v___y_1595_;
                v___y_1574_ = v___y_1599_;
                v___y_1575_ = v___y_1598_;
                v___y_1576_ = v___y_1597_;
                v___y_1577_ = v___y_1600_;
                v___y_1578_ = v___y_1601_;
                v_a_1579_ = v___x_1603_;
                state = 5;
                continue;
            }
            7 => {
                v___x_1616_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1616_, 0, v_a_1615_);
                v___y_1569_ = v___y_1605_;
                v___y_1570_ = v___y_1606_;
                v___y_1571_ = v___y_1607_;
                v___y_1572_ = v___y_1609_;
                v___y_1573_ = v___y_1608_;
                v___y_1574_ = v___y_1612_;
                v___y_1575_ = v___y_1611_;
                v___y_1576_ = v___y_1610_;
                v___y_1577_ = v___y_1613_;
                v___y_1578_ = v___y_1614_;
                v_a_1579_ = v___x_1616_;
                state = 5;
                continue;
            }
            8 => {
                if crate::leanh::lean_obj_tag(v___y_1628_) == 0 {
                    v_a_1629_ = crate::leanh::lean_ctor_get(v___y_1628_, 0);
                    crate::leanh::lean_inc(v_a_1629_);
                    crate::leanh::lean_dec_ref_known(v___y_1628_, 1);
                    v___y_1592_ = v___y_1618_;
                    v___y_1593_ = v___y_1619_;
                    v___y_1594_ = v___y_1620_;
                    v___y_1595_ = v___y_1622_;
                    v___y_1596_ = v___y_1621_;
                    v___y_1597_ = v___y_1625_;
                    v___y_1598_ = v___y_1624_;
                    v___y_1599_ = v___y_1623_;
                    v___y_1600_ = v___y_1626_;
                    v___y_1601_ = v___y_1627_;
                    v_a_1602_ = v_a_1629_;
                    state = 6;
                    continue;
                } else {
                    v_a_1630_ = crate::leanh::lean_ctor_get(v___y_1628_, 0);
                    crate::leanh::lean_inc(v_a_1630_);
                    crate::leanh::lean_dec_ref_known(v___y_1628_, 1);
                    v___y_1605_ = v___y_1618_;
                    v___y_1606_ = v___y_1619_;
                    v___y_1607_ = v___y_1620_;
                    v___y_1608_ = v___y_1622_;
                    v___y_1609_ = v___y_1621_;
                    v___y_1610_ = v___y_1625_;
                    v___y_1611_ = v___y_1624_;
                    v___y_1612_ = v___y_1623_;
                    v___y_1613_ = v___y_1626_;
                    v___y_1614_ = v___y_1627_;
                    v_a_1615_ = v_a_1630_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                v___x_1645_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___redArg(v___y_1638_);
                if crate::leanh::lean_obj_tag(v___x_1645_) == 0 {
                    v_a_1646_ = crate::leanh::lean_ctor_get(v___x_1645_, 0);
                    crate::leanh::lean_inc(v_a_1646_);
                    crate::leanh::lean_dec_ref_known(v___x_1645_, 1);
                    v___x_1647_ = l_Lean_trace_profiler_useHeartbeats;
                    v___x_1648_ = l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5(v___y_1635_, v___x_1647_);
                    if v___x_1648_ == 0 {
                        v___x_1649_ = lean_io_mono_nanos_now();
                        v___x_1650_ = l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(v___y_1643_, v___y_1636_, v___y_1638_);
                        if crate::leanh::lean_obj_tag(v___x_1650_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_1650_, 1);
                            if crate::leanh::lean_obj_tag(v___y_1644_) == 1 {
                                v_val_1651_ = crate::leanh::lean_ctor_get(v___y_1644_, 0);
                                crate::leanh::lean_inc(v_val_1651_);
                                crate::leanh::lean_dec_ref_known(v___y_1644_, 1);
                                v___x_1652_ = l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__1;
                                crate::leanh::lean_inc_ref(v___y_1634_);
                                v___x_1653_ = l_Lean_Name_mkStr2(v___y_1634_, v___x_1652_);
                                v___x_1654_ = l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__3;
                                crate::leanh::lean_inc(v___x_1653_);
                                v___x_1655_ = l_Lean_Name_append(v___x_1654_, v___x_1653_);
                                v___x_1656_ =
                                    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                        v___y_1642_,
                                        v___y_1635_,
                                        v___x_1655_,
                                    );
                                crate::leanh::lean_dec(v___x_1655_);
                                if v___x_1656_ == 0 {
                                    crate::leanh::lean_dec(v___x_1653_);
                                    crate::leanh::lean_dec(v_val_1651_);
                                    v___x_1657_ = crate::leanh::lean_box(0);
                                    v___y_1592_ = v___y_1632_;
                                    v___y_1593_ = v___x_1649_;
                                    v___y_1594_ = v___y_1637_;
                                    v___y_1595_ = v___y_1639_;
                                    v___y_1596_ = v___y_1638_;
                                    v___y_1597_ = v___y_1641_;
                                    v___y_1598_ = v___y_1640_;
                                    v___y_1599_ = v_a_1646_;
                                    v___y_1600_ = v___y_1635_;
                                    v___y_1601_ = v___y_1636_;
                                    v_a_1602_ = v___x_1657_;
                                    state = 6;
                                    continue;
                                } else {
                                    v___x_1658_ = crate::leanh::lean_box(0);
                                    v___x_1659_ =
                                        l_Lean_Elab_InfoTree_format(v_val_1651_, v___x_1658_);
                                    if crate::leanh::lean_obj_tag(v___x_1659_) == 0 {
                                        v_a_1660_ = crate::leanh::lean_ctor_get(v___x_1659_, 0);
                                        crate::leanh::lean_inc(v_a_1660_);
                                        crate::leanh::lean_dec_ref_known(v___x_1659_, 1);
                                        v___x_1661_ = l_Lean_MessageData_ofFormat(v_a_1660_);
                                        v___x_1662_ = l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2(v___x_1653_, v___x_1661_, v___y_1636_, v___y_1638_);
                                        v___y_1618_ = v___y_1632_;
                                        v___y_1619_ = v___x_1649_;
                                        v___y_1620_ = v___y_1637_;
                                        v___y_1621_ = v___y_1638_;
                                        v___y_1622_ = v___y_1639_;
                                        v___y_1623_ = v_a_1646_;
                                        v___y_1624_ = v___y_1640_;
                                        v___y_1625_ = v___y_1641_;
                                        v___y_1626_ = v___y_1635_;
                                        v___y_1627_ = v___y_1636_;
                                        v___y_1628_ = v___x_1662_;
                                        state = 8;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v___x_1653_);
                                        v_a_1663_ = crate::leanh::lean_ctor_get(v___x_1659_, 0);
                                        v_isSharedCheck_1673_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_1659_)) as u8;
                                        if v_isSharedCheck_1673_ == 0 {
                                            v___x_1665_ = v___x_1659_;
                                            v_isShared_1666_ = v_isSharedCheck_1673_;
                                            state = 10;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_1663_);
                                            crate::leanh::lean_dec(v___x_1659_);
                                            v___x_1665_ = crate::leanh::lean_box(0);
                                            v_isShared_1666_ = v_isSharedCheck_1673_;
                                            state = 10;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v___y_1644_);
                                v___x_1674_ = crate::leanh::lean_box(0);
                                v___y_1592_ = v___y_1632_;
                                v___y_1593_ = v___x_1649_;
                                v___y_1594_ = v___y_1637_;
                                v___y_1595_ = v___y_1639_;
                                v___y_1596_ = v___y_1638_;
                                v___y_1597_ = v___y_1641_;
                                v___y_1598_ = v___y_1640_;
                                v___y_1599_ = v_a_1646_;
                                v___y_1600_ = v___y_1635_;
                                v___y_1601_ = v___y_1636_;
                                v_a_1602_ = v___x_1674_;
                                state = 6;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v___y_1644_);
                            v___y_1618_ = v___y_1632_;
                            v___y_1619_ = v___x_1649_;
                            v___y_1620_ = v___y_1637_;
                            v___y_1621_ = v___y_1638_;
                            v___y_1622_ = v___y_1639_;
                            v___y_1623_ = v_a_1646_;
                            v___y_1624_ = v___y_1640_;
                            v___y_1625_ = v___y_1641_;
                            v___y_1626_ = v___y_1635_;
                            v___y_1627_ = v___y_1636_;
                            v___y_1628_ = v___x_1650_;
                            state = 8;
                            continue;
                        }
                    } else {
                        v___x_1675_ = lean_io_get_num_heartbeats();
                        v___x_1676_ = l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(v___y_1643_, v___y_1636_, v___y_1638_);
                        if crate::leanh::lean_obj_tag(v___x_1676_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_1676_, 1);
                            if crate::leanh::lean_obj_tag(v___y_1644_) == 1 {
                                v_val_1677_ = crate::leanh::lean_ctor_get(v___y_1644_, 0);
                                crate::leanh::lean_inc(v_val_1677_);
                                crate::leanh::lean_dec_ref_known(v___y_1644_, 1);
                                v___x_1678_ = l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__1;
                                crate::leanh::lean_inc_ref(v___y_1634_);
                                v___x_1679_ = l_Lean_Name_mkStr2(v___y_1634_, v___x_1678_);
                                v___x_1680_ = l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__3;
                                crate::leanh::lean_inc(v___x_1679_);
                                v___x_1681_ = l_Lean_Name_append(v___x_1680_, v___x_1679_);
                                v___x_1682_ =
                                    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                        v___y_1642_,
                                        v___y_1635_,
                                        v___x_1681_,
                                    );
                                crate::leanh::lean_dec(v___x_1681_);
                                if v___x_1682_ == 0 {
                                    crate::leanh::lean_dec(v___x_1679_);
                                    crate::leanh::lean_dec(v_val_1677_);
                                    v___x_1683_ = crate::leanh::lean_box(0);
                                    v___y_1529_ = v___y_1632_;
                                    v___y_1530_ = v___y_1637_;
                                    v___y_1531_ = v___y_1639_;
                                    v___y_1532_ = v___y_1638_;
                                    v___y_1533_ = v___y_1641_;
                                    v___y_1534_ = v___y_1640_;
                                    v___y_1535_ = v_a_1646_;
                                    v___y_1536_ = v___x_1675_;
                                    v___y_1537_ = v___y_1635_;
                                    v___y_1538_ = v___y_1636_;
                                    v_a_1539_ = v___x_1683_;
                                    state = 2;
                                    continue;
                                } else {
                                    v___x_1684_ = crate::leanh::lean_box(0);
                                    v___x_1685_ =
                                        l_Lean_Elab_InfoTree_format(v_val_1677_, v___x_1684_);
                                    if crate::leanh::lean_obj_tag(v___x_1685_) == 0 {
                                        v_a_1686_ = crate::leanh::lean_ctor_get(v___x_1685_, 0);
                                        crate::leanh::lean_inc(v_a_1686_);
                                        crate::leanh::lean_dec_ref_known(v___x_1685_, 1);
                                        v___x_1687_ = l_Lean_MessageData_ofFormat(v_a_1686_);
                                        v___x_1688_ = l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2(v___x_1679_, v___x_1687_, v___y_1636_, v___y_1638_);
                                        v___y_1555_ = v___y_1632_;
                                        v___y_1556_ = v___y_1637_;
                                        v___y_1557_ = v___y_1638_;
                                        v___y_1558_ = v___y_1639_;
                                        v___y_1559_ = v_a_1646_;
                                        v___y_1560_ = v___y_1640_;
                                        v___y_1561_ = v___y_1641_;
                                        v___y_1562_ = v___x_1675_;
                                        v___y_1563_ = v___y_1635_;
                                        v___y_1564_ = v___y_1636_;
                                        v___y_1565_ = v___x_1688_;
                                        state = 4;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v___x_1679_);
                                        v_a_1689_ = crate::leanh::lean_ctor_get(v___x_1685_, 0);
                                        v_isSharedCheck_1699_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_1685_)) as u8;
                                        if v_isSharedCheck_1699_ == 0 {
                                            v___x_1691_ = v___x_1685_;
                                            v_isShared_1692_ = v_isSharedCheck_1699_;
                                            state = 12;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_1689_);
                                            crate::leanh::lean_dec(v___x_1685_);
                                            v___x_1691_ = crate::leanh::lean_box(0);
                                            v_isShared_1692_ = v_isSharedCheck_1699_;
                                            state = 12;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v___y_1644_);
                                v___x_1700_ = crate::leanh::lean_box(0);
                                v___y_1529_ = v___y_1632_;
                                v___y_1530_ = v___y_1637_;
                                v___y_1531_ = v___y_1639_;
                                v___y_1532_ = v___y_1638_;
                                v___y_1533_ = v___y_1641_;
                                v___y_1534_ = v___y_1640_;
                                v___y_1535_ = v_a_1646_;
                                v___y_1536_ = v___x_1675_;
                                v___y_1537_ = v___y_1635_;
                                v___y_1538_ = v___y_1636_;
                                v_a_1539_ = v___x_1700_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v___y_1644_);
                            v___y_1555_ = v___y_1632_;
                            v___y_1556_ = v___y_1637_;
                            v___y_1557_ = v___y_1638_;
                            v___y_1558_ = v___y_1639_;
                            v___y_1559_ = v_a_1646_;
                            v___y_1560_ = v___y_1640_;
                            v___y_1561_ = v___y_1641_;
                            v___y_1562_ = v___x_1675_;
                            v___y_1563_ = v___y_1635_;
                            v___y_1564_ = v___y_1636_;
                            v___y_1565_ = v___x_1676_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___y_1644_);
                    crate::leanh::lean_dec(v___y_1643_);
                    crate::leanh::lean_dec_ref(v___y_1632_);
                    v_a_1701_ = crate::leanh::lean_ctor_get(v___x_1645_, 0);
                    v_isSharedCheck_1708_ = (!crate::leanh::lean_is_exclusive(v___x_1645_)) as u8;
                    if v_isSharedCheck_1708_ == 0 {
                        v___x_1703_ = v___x_1645_;
                        v_isShared_1704_ = v_isSharedCheck_1708_;
                        state = 14;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1701_);
                        crate::leanh::lean_dec(v___x_1645_);
                        v___x_1703_ = crate::leanh::lean_box(0);
                        v_isShared_1704_ = v_isSharedCheck_1708_;
                        state = 14;
                        continue;
                    }
                }
            }
            10 => {
                v___x_1667_ = lean_io_error_to_string(v_a_1663_);
                if v_isShared_1666_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1665_, 3);
                    crate::leanh::lean_ctor_set(v___x_1665_, 0, v___x_1667_);
                    v___x_1669_ = v___x_1665_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1672_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1672_, 0, v___x_1667_);
                    v___x_1669_ = v_reuseFailAlloc_1672_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_1670_ = l_Lean_MessageData_ofFormat(v___x_1669_);
                crate::leanh::lean_inc(v___y_1633_);
                v___x_1671_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1671_, 0, v___y_1633_);
                crate::leanh::lean_ctor_set(v___x_1671_, 1, v___x_1670_);
                v___y_1605_ = v___y_1632_;
                v___y_1606_ = v___x_1649_;
                v___y_1607_ = v___y_1637_;
                v___y_1608_ = v___y_1639_;
                v___y_1609_ = v___y_1638_;
                v___y_1610_ = v___y_1641_;
                v___y_1611_ = v___y_1640_;
                v___y_1612_ = v_a_1646_;
                v___y_1613_ = v___y_1635_;
                v___y_1614_ = v___y_1636_;
                v_a_1615_ = v___x_1671_;
                state = 7;
                continue;
            }
            12 => {
                v___x_1693_ = lean_io_error_to_string(v_a_1689_);
                if v_isShared_1692_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1691_, 3);
                    crate::leanh::lean_ctor_set(v___x_1691_, 0, v___x_1693_);
                    v___x_1695_ = v___x_1691_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1698_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1698_, 0, v___x_1693_);
                    v___x_1695_ = v_reuseFailAlloc_1698_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_1696_ = l_Lean_MessageData_ofFormat(v___x_1695_);
                crate::leanh::lean_inc(v___y_1633_);
                v___x_1697_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1697_, 0, v___y_1633_);
                crate::leanh::lean_ctor_set(v___x_1697_, 1, v___x_1696_);
                v___y_1542_ = v___y_1632_;
                v___y_1543_ = v___y_1637_;
                v___y_1544_ = v___y_1639_;
                v___y_1545_ = v___y_1638_;
                v___y_1546_ = v___y_1641_;
                v___y_1547_ = v___y_1640_;
                v___y_1548_ = v_a_1646_;
                v___y_1549_ = v___x_1675_;
                v___y_1550_ = v___y_1635_;
                v___y_1551_ = v___y_1636_;
                v_a_1552_ = v___x_1697_;
                state = 3;
                continue;
            }
            14 => {
                if v_isShared_1704_ == 0 {
                    v___x_1706_ = v___x_1703_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1707_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1707_, 0, v_a_1701_);
                    v___x_1706_ = v_reuseFailAlloc_1707_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_1706_;
            }
            16 => {
                v_desc_1714_ = crate::leanh::lean_ctor_get(v_element_1709_, 0);
                crate::leanh::lean_inc_ref(v_desc_1714_);
                v_diagnostics_1715_ = crate::leanh::lean_ctor_get(v_element_1709_, 1);
                crate::leanh::lean_inc_ref(v_diagnostics_1715_);
                v_infoTree_x3f_1716_ = crate::leanh::lean_ctor_get(v_element_1709_, 2);
                crate::leanh::lean_inc(v_infoTree_x3f_1716_);
                crate::leanh::lean_dec_ref(v_element_1709_);
                v___x_1814_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1814_, 0, v_desc_1714_);
                match crate::leanh::lean_obj_tag(v_range_x3f_1503_) {
                    0 => {
                        v___x_1815_ = l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__13;
                        v___x_1816_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1816_, 0, v___x_1814_);
                        crate::leanh::lean_ctor_set(v___x_1816_, 1, v___x_1815_);
                        v_desc_1718_ = v___x_1816_;
                        v___y_1719_ = v_a_1505_;
                        v___y_1720_ = v_a_1506_;
                        state = 17;
                        continue;
                    }
                    1 => {
                        v_range_1817_ = crate::leanh::lean_ctor_get(v_range_x3f_1503_, 0);
                        v_isSharedCheck_1875_ =
                            (!crate::leanh::lean_is_exclusive(v_range_x3f_1503_)) as u8;
                        if v_isSharedCheck_1875_ == 0 {
                            v___x_1819_ = v_range_x3f_1503_;
                            v_isShared_1820_ = v_isSharedCheck_1875_;
                            state = 33;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_range_1817_);
                            crate::leanh::lean_dec(v_range_x3f_1503_);
                            v___x_1819_ = crate::leanh::lean_box(0);
                            v_isShared_1820_ = v_isSharedCheck_1875_;
                            state = 33;
                            continue;
                        }
                    }
                    _ => {
                        v___x_1876_ = l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__24;
                        v___x_1877_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1877_, 0, v___x_1814_);
                        crate::leanh::lean_ctor_set(v___x_1877_, 1, v___x_1876_);
                        v_desc_1718_ = v___x_1877_;
                        v___y_1719_ = v_a_1505_;
                        v___y_1720_ = v_a_1506_;
                        state = 17;
                        continue;
                    }
                }
            }
            17 => {
                v_msgLog_1721_ = crate::leanh::lean_ctor_get(v_diagnostics_1715_, 0);
                v_isSharedCheck_1812_ =
                    (!crate::leanh::lean_is_exclusive(v_diagnostics_1715_)) as u8;
                if v_isSharedCheck_1812_ == 0 {
                    v_unused_1813_ = crate::leanh::lean_ctor_get(v_diagnostics_1715_, 1);
                    crate::leanh::lean_dec(v_unused_1813_);
                    v___x_1723_ = v_diagnostics_1715_;
                    v_isShared_1724_ = v_isSharedCheck_1812_;
                    state = 18;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_msgLog_1721_);
                    crate::leanh::lean_dec(v_diagnostics_1715_);
                    v___x_1723_ = crate::leanh::lean_box(0);
                    v_isShared_1724_ = v_isSharedCheck_1812_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                v___x_1725_ = l_Lean_MessageLog_toList(v_msgLog_1721_);
                crate::leanh::lean_dec_ref(v_msgLog_1721_);
                v___x_1726_ = crate::leanh::lean_box(0);
                v___x_1727_ = l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___redArg(v___x_1725_, v___x_1726_);
                if crate::leanh::lean_obj_tag(v___x_1727_) == 0 {
                    v_options_1728_ = crate::leanh::lean_ctor_get(v___y_1719_, 2);
                    v_a_1729_ = crate::leanh::lean_ctor_get(v___x_1727_, 0);
                    crate::leanh::lean_inc(v_a_1729_);
                    crate::leanh::lean_dec_ref_known(v___x_1727_, 1);
                    v_ref_1730_ = crate::leanh::lean_ctor_get(v___y_1719_, 5);
                    v_inheritedTraceOptions_1731_ = crate::leanh::lean_ctor_get(v___y_1719_, 13);
                    v_hasTrace_1732_ = crate::leanh::lean_ctor_get_uint8(
                        v_options_1728_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    v___x_1733_ = lean_array_to_list(v_children_1710_);
                    if v_hasTrace_1732_ == 0 {
                        crate::leanh::lean_dec(v_a_1729_);
                        crate::leanh::lean_del_object(v___x_1723_);
                        crate::leanh::lean_dec(v_desc_1718_);
                        crate::leanh::lean_del_object(v___x_1712_);
                        v___x_1734_ = l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(v___x_1733_, v___y_1719_, v___y_1720_);
                        if crate::leanh::lean_obj_tag(v___x_1734_) == 0 {
                            v_isSharedCheck_1746_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1734_)) as u8;
                            if v_isSharedCheck_1746_ == 0 {
                                v_unused_1747_ = crate::leanh::lean_ctor_get(v___x_1734_, 0);
                                crate::leanh::lean_dec(v_unused_1747_);
                                v___x_1736_ = v___x_1734_;
                                v_isShared_1737_ = v_isSharedCheck_1746_;
                                state = 19;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_1734_);
                                v___x_1736_ = crate::leanh::lean_box(0);
                                v_isShared_1737_ = v_isSharedCheck_1746_;
                                state = 19;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_infoTree_x3f_1716_);
                            return v___x_1734_;
                        }
                    } else {
                        v___x_1748_ = l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__4;
                        v___x_1749_ = l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__6;
                        v___x_1750_ = l_Std_Format_prefixJoin___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3(v___x_1749_, v_a_1729_);
                        if v_isShared_1724_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_1723_, 5);
                            crate::leanh::lean_ctor_set(v___x_1723_, 1, v___x_1750_);
                            crate::leanh::lean_ctor_set(v___x_1723_, 0, v_desc_1718_);
                            v___x_1752_ = v___x_1723_;
                            state = 22;
                            continue;
                        } else {
                            v_reuseFailAlloc_1803_ =
                                crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1803_, 0, v_desc_1718_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1803_, 1, v___x_1750_);
                            v___x_1752_ = v_reuseFailAlloc_1803_;
                            state = 22;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1723_);
                    crate::leanh::lean_dec(v_desc_1718_);
                    crate::leanh::lean_dec(v_infoTree_x3f_1716_);
                    crate::leanh::lean_del_object(v___x_1712_);
                    crate::leanh::lean_dec_ref(v_children_1710_);
                    v_a_1804_ = crate::leanh::lean_ctor_get(v___x_1727_, 0);
                    v_isSharedCheck_1811_ = (!crate::leanh::lean_is_exclusive(v___x_1727_)) as u8;
                    if v_isSharedCheck_1811_ == 0 {
                        v___x_1806_ = v___x_1727_;
                        v_isShared_1807_ = v_isSharedCheck_1811_;
                        state = 31;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1804_);
                        crate::leanh::lean_dec(v___x_1727_);
                        v___x_1806_ = crate::leanh::lean_box(0);
                        v_isShared_1807_ = v_isSharedCheck_1811_;
                        state = 31;
                        continue;
                    }
                }
            }
            19 => {
                if crate::leanh::lean_obj_tag(v_infoTree_x3f_1716_) == 1 {
                    crate::leanh::lean_dec_ref_known(v_infoTree_x3f_1716_, 1);
                    v___x_1738_ = crate::leanh::lean_box(0);
                    if v_isShared_1737_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1736_, 0, v___x_1738_);
                        v___x_1740_ = v___x_1736_;
                        state = 20;
                        continue;
                    } else {
                        v_reuseFailAlloc_1741_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1741_, 0, v___x_1738_);
                        v___x_1740_ = v_reuseFailAlloc_1741_;
                        state = 20;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_infoTree_x3f_1716_);
                    v___x_1742_ = crate::leanh::lean_box(0);
                    if v_isShared_1737_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1736_, 0, v___x_1742_);
                        v___x_1744_ = v___x_1736_;
                        state = 21;
                        continue;
                    } else {
                        v_reuseFailAlloc_1745_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1745_, 0, v___x_1742_);
                        v___x_1744_ = v_reuseFailAlloc_1745_;
                        state = 21;
                        continue;
                    }
                }
            }
            20 => {
                return v___x_1740_;
            }
            21 => {
                return v___x_1744_;
            }
            22 => {
                v___f_1753_ = crate::leanh::lean_alloc_closure(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___lam__0___boxed as *mut core::ffi::c_void, 5, 1);
                crate::leanh::lean_closure_set(v___f_1753_, 0, v___x_1752_);
                v___x_1754_ = l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__8;
                v___x_1755_ = l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__1;
                v___x_1756_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__9_once), _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__9);
                v___x_1757_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                    v_inheritedTraceOptions_1731_,
                    v_options_1728_,
                    v___x_1756_,
                );
                if v___x_1757_ == 0 {
                    v___x_1758_ = l_Lean_trace_profiler;
                    v___x_1759_ = l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5(v_options_1728_, v___x_1758_);
                    if v___x_1759_ == 0 {
                        crate::leanh::lean_dec_ref(v___f_1753_);
                        v___x_1760_ = l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(v___x_1733_, v___y_1719_, v___y_1720_);
                        if crate::leanh::lean_obj_tag(v___x_1760_) == 0 {
                            v_isSharedCheck_1801_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1760_)) as u8;
                            if v_isSharedCheck_1801_ == 0 {
                                v_unused_1802_ = crate::leanh::lean_ctor_get(v___x_1760_, 0);
                                crate::leanh::lean_dec(v_unused_1802_);
                                v___x_1762_ = v___x_1760_;
                                v_isShared_1763_ = v_isSharedCheck_1801_;
                                state = 23;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_1760_);
                                v___x_1762_ = crate::leanh::lean_box(0);
                                v_isShared_1763_ = v_isSharedCheck_1801_;
                                state = 23;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_infoTree_x3f_1716_);
                            crate::leanh::lean_del_object(v___x_1712_);
                            return v___x_1760_;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_1712_);
                        v___y_1632_ = v___f_1753_;
                        v___y_1633_ = v_ref_1730_;
                        v___y_1634_ = v___x_1748_;
                        v___y_1635_ = v_options_1728_;
                        v___y_1636_ = v___y_1719_;
                        v___y_1637_ = v___x_1757_;
                        v___y_1638_ = v___y_1720_;
                        v___y_1639_ = v_hasTrace_1732_;
                        v___y_1640_ = v___x_1755_;
                        v___y_1641_ = v___x_1754_;
                        v___y_1642_ = v_inheritedTraceOptions_1731_;
                        v___y_1643_ = v___x_1733_;
                        v___y_1644_ = v_infoTree_x3f_1716_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1712_);
                    v___y_1632_ = v___f_1753_;
                    v___y_1633_ = v_ref_1730_;
                    v___y_1634_ = v___x_1748_;
                    v___y_1635_ = v_options_1728_;
                    v___y_1636_ = v___y_1719_;
                    v___y_1637_ = v___x_1757_;
                    v___y_1638_ = v___y_1720_;
                    v___y_1639_ = v_hasTrace_1732_;
                    v___y_1640_ = v___x_1755_;
                    v___y_1641_ = v___x_1754_;
                    v___y_1642_ = v_inheritedTraceOptions_1731_;
                    v___y_1643_ = v___x_1733_;
                    v___y_1644_ = v_infoTree_x3f_1716_;
                    state = 9;
                    continue;
                }
            }
            23 => {
                if crate::leanh::lean_obj_tag(v_infoTree_x3f_1716_) == 1 {
                    v_val_1764_ = crate::leanh::lean_ctor_get(v_infoTree_x3f_1716_, 0);
                    v_isSharedCheck_1796_ =
                        (!crate::leanh::lean_is_exclusive(v_infoTree_x3f_1716_)) as u8;
                    if v_isSharedCheck_1796_ == 0 {
                        v___x_1766_ = v_infoTree_x3f_1716_;
                        v_isShared_1767_ = v_isSharedCheck_1796_;
                        state = 24;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1764_);
                        crate::leanh::lean_dec(v_infoTree_x3f_1716_);
                        v___x_1766_ = crate::leanh::lean_box(0);
                        v_isShared_1767_ = v_isSharedCheck_1796_;
                        state = 24;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_infoTree_x3f_1716_);
                    crate::leanh::lean_del_object(v___x_1712_);
                    v___x_1797_ = crate::leanh::lean_box(0);
                    if v_isShared_1763_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1762_, 0, v___x_1797_);
                        v___x_1799_ = v___x_1762_;
                        state = 30;
                        continue;
                    } else {
                        v_reuseFailAlloc_1800_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1800_, 0, v___x_1797_);
                        v___x_1799_ = v_reuseFailAlloc_1800_;
                        state = 30;
                        continue;
                    }
                }
            }
            24 => {
                v___x_1768_ = l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__10;
                v___x_1769_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__11_once), _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__11);
                v___x_1770_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                    v_inheritedTraceOptions_1731_,
                    v_options_1728_,
                    v___x_1769_,
                );
                if v___x_1770_ == 0 {
                    crate::leanh::lean_del_object(v___x_1766_);
                    crate::leanh::lean_dec(v_val_1764_);
                    crate::leanh::lean_del_object(v___x_1712_);
                    v___x_1771_ = crate::leanh::lean_box(0);
                    if v_isShared_1763_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1762_, 0, v___x_1771_);
                        v___x_1773_ = v___x_1762_;
                        state = 25;
                        continue;
                    } else {
                        v_reuseFailAlloc_1774_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1774_, 0, v___x_1771_);
                        v___x_1773_ = v_reuseFailAlloc_1774_;
                        state = 25;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1762_);
                    v___x_1775_ = crate::leanh::lean_box(0);
                    v___x_1776_ = l_Lean_Elab_InfoTree_format(v_val_1764_, v___x_1775_);
                    if crate::leanh::lean_obj_tag(v___x_1776_) == 0 {
                        crate::leanh::lean_del_object(v___x_1766_);
                        crate::leanh::lean_del_object(v___x_1712_);
                        v_a_1777_ = crate::leanh::lean_ctor_get(v___x_1776_, 0);
                        crate::leanh::lean_inc(v_a_1777_);
                        crate::leanh::lean_dec_ref_known(v___x_1776_, 1);
                        v___x_1778_ = l_Lean_MessageData_ofFormat(v_a_1777_);
                        v___x_1779_ = l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2(v___x_1768_, v___x_1778_, v___y_1719_, v___y_1720_);
                        return v___x_1779_;
                    } else {
                        v_a_1780_ = crate::leanh::lean_ctor_get(v___x_1776_, 0);
                        v_isSharedCheck_1795_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1776_)) as u8;
                        if v_isSharedCheck_1795_ == 0 {
                            v___x_1782_ = v___x_1776_;
                            v_isShared_1783_ = v_isSharedCheck_1795_;
                            state = 26;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1780_);
                            crate::leanh::lean_dec(v___x_1776_);
                            v___x_1782_ = crate::leanh::lean_box(0);
                            v_isShared_1783_ = v_isSharedCheck_1795_;
                            state = 26;
                            continue;
                        }
                    }
                }
            }
            25 => {
                return v___x_1773_;
            }
            26 => {
                v___x_1784_ = lean_io_error_to_string(v_a_1780_);
                if v_isShared_1767_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1766_, 3);
                    crate::leanh::lean_ctor_set(v___x_1766_, 0, v___x_1784_);
                    v___x_1786_ = v___x_1766_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_1794_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1794_, 0, v___x_1784_);
                    v___x_1786_ = v_reuseFailAlloc_1794_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                v___x_1787_ = l_Lean_MessageData_ofFormat(v___x_1786_);
                crate::leanh::lean_inc(v_ref_1730_);
                if v_isShared_1713_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1712_, 1, v___x_1787_);
                    crate::leanh::lean_ctor_set(v___x_1712_, 0, v_ref_1730_);
                    v___x_1789_ = v___x_1712_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_1793_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1793_, 0, v_ref_1730_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1793_, 1, v___x_1787_);
                    v___x_1789_ = v_reuseFailAlloc_1793_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                if v_isShared_1783_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1782_, 0, v___x_1789_);
                    v___x_1791_ = v___x_1782_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_1792_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1792_, 0, v___x_1789_);
                    v___x_1791_ = v_reuseFailAlloc_1792_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_1791_;
            }
            30 => {
                return v___x_1799_;
            }
            31 => {
                if v_isShared_1807_ == 0 {
                    v___x_1809_ = v___x_1806_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_1810_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1810_, 0, v_a_1804_);
                    v___x_1809_ = v_reuseFailAlloc_1810_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_1809_;
            }
            33 => {
                v_fileMap_1821_ = crate::leanh::lean_ctor_get(v_a_1505_, 1);
                v_start_1822_ = crate::leanh::lean_ctor_get(v_range_1817_, 0);
                v_stop_1823_ = crate::leanh::lean_ctor_get(v_range_1817_, 1);
                v_isSharedCheck_1874_ = (!crate::leanh::lean_is_exclusive(v_range_1817_)) as u8;
                if v_isSharedCheck_1874_ == 0 {
                    v___x_1825_ = v_range_1817_;
                    v_isShared_1826_ = v_isSharedCheck_1874_;
                    state = 34;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_stop_1823_);
                    crate::leanh::lean_inc(v_start_1822_);
                    crate::leanh::lean_dec(v_range_1817_);
                    v___x_1825_ = crate::leanh::lean_box(0);
                    v_isShared_1826_ = v_isSharedCheck_1874_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                crate::leanh::lean_inc_ref(v_fileMap_1821_);
                v___x_1827_ = l_Lean_FileMap_toPosition(v_fileMap_1821_, v_start_1822_);
                crate::leanh::lean_dec(v_start_1822_);
                v_line_1828_ = crate::leanh::lean_ctor_get(v___x_1827_, 0);
                v_column_1829_ = crate::leanh::lean_ctor_get(v___x_1827_, 1);
                v_isSharedCheck_1873_ = (!crate::leanh::lean_is_exclusive(v___x_1827_)) as u8;
                if v_isSharedCheck_1873_ == 0 {
                    v___x_1831_ = v___x_1827_;
                    v_isShared_1832_ = v_isSharedCheck_1873_;
                    state = 35;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_column_1829_);
                    crate::leanh::lean_inc(v_line_1828_);
                    crate::leanh::lean_dec(v___x_1827_);
                    v___x_1831_ = crate::leanh::lean_box(0);
                    v_isShared_1832_ = v_isSharedCheck_1873_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                crate::leanh::lean_inc_ref(v_fileMap_1821_);
                v___x_1833_ = l_Lean_FileMap_toPosition(v_fileMap_1821_, v_stop_1823_);
                crate::leanh::lean_dec(v_stop_1823_);
                v_line_1834_ = crate::leanh::lean_ctor_get(v___x_1833_, 0);
                v_column_1835_ = crate::leanh::lean_ctor_get(v___x_1833_, 1);
                v_isSharedCheck_1872_ = (!crate::leanh::lean_is_exclusive(v___x_1833_)) as u8;
                if v_isSharedCheck_1872_ == 0 {
                    v___x_1837_ = v___x_1833_;
                    v_isShared_1838_ = v_isSharedCheck_1872_;
                    state = 36;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_column_1835_);
                    crate::leanh::lean_inc(v_line_1834_);
                    crate::leanh::lean_dec(v___x_1833_);
                    v___x_1837_ = crate::leanh::lean_box(0);
                    v_isShared_1838_ = v_isSharedCheck_1872_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                v___x_1839_ = l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__15;
                v___x_1840_ = l_Nat_reprFast(v_line_1828_);
                if v_isShared_1820_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1819_, 3);
                    crate::leanh::lean_ctor_set(v___x_1819_, 0, v___x_1840_);
                    v___x_1842_ = v___x_1819_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_1871_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1871_, 0, v___x_1840_);
                    v___x_1842_ = v_reuseFailAlloc_1871_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                if v_isShared_1838_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1837_, 5);
                    crate::leanh::lean_ctor_set(v___x_1837_, 1, v___x_1842_);
                    crate::leanh::lean_ctor_set(v___x_1837_, 0, v___x_1839_);
                    v___x_1844_ = v___x_1837_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_1870_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1870_, 0, v___x_1839_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1870_, 1, v___x_1842_);
                    v___x_1844_ = v_reuseFailAlloc_1870_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                v___x_1845_ = l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__17;
                if v_isShared_1832_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1831_, 5);
                    crate::leanh::lean_ctor_set(v___x_1831_, 1, v___x_1845_);
                    crate::leanh::lean_ctor_set(v___x_1831_, 0, v___x_1844_);
                    v___x_1847_ = v___x_1831_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_1869_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1869_, 0, v___x_1844_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1869_, 1, v___x_1845_);
                    v___x_1847_ = v_reuseFailAlloc_1869_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                v___x_1848_ = l_Nat_reprFast(v_column_1829_);
                v___x_1849_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1849_, 0, v___x_1848_);
                if v_isShared_1826_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1825_, 5);
                    crate::leanh::lean_ctor_set(v___x_1825_, 1, v___x_1849_);
                    crate::leanh::lean_ctor_set(v___x_1825_, 0, v___x_1847_);
                    v___x_1851_ = v___x_1825_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_1868_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1868_, 0, v___x_1847_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1868_, 1, v___x_1849_);
                    v___x_1851_ = v_reuseFailAlloc_1868_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                v___x_1852_ = l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__19;
                v___x_1853_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1853_, 0, v___x_1851_);
                crate::leanh::lean_ctor_set(v___x_1853_, 1, v___x_1852_);
                v___x_1854_ = l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__21;
                v___x_1855_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1855_, 0, v___x_1853_);
                crate::leanh::lean_ctor_set(v___x_1855_, 1, v___x_1854_);
                v___x_1856_ = l_Nat_reprFast(v_line_1834_);
                v___x_1857_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1857_, 0, v___x_1856_);
                v___x_1858_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1858_, 0, v___x_1839_);
                crate::leanh::lean_ctor_set(v___x_1858_, 1, v___x_1857_);
                v___x_1859_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1859_, 0, v___x_1858_);
                crate::leanh::lean_ctor_set(v___x_1859_, 1, v___x_1845_);
                v___x_1860_ = l_Nat_reprFast(v_column_1835_);
                v___x_1861_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1861_, 0, v___x_1860_);
                v___x_1862_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1862_, 0, v___x_1859_);
                crate::leanh::lean_ctor_set(v___x_1862_, 1, v___x_1861_);
                v___x_1863_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1863_, 0, v___x_1862_);
                crate::leanh::lean_ctor_set(v___x_1863_, 1, v___x_1852_);
                v___x_1864_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1864_, 0, v___x_1855_);
                crate::leanh::lean_ctor_set(v___x_1864_, 1, v___x_1863_);
                v___x_1865_ = l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__22;
                v___x_1866_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1866_, 0, v___x_1864_);
                crate::leanh::lean_ctor_set(v___x_1866_, 1, v___x_1865_);
                v___x_1867_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1867_, 0, v___x_1814_);
                crate::leanh::lean_ctor_set(v___x_1867_, 1, v___x_1866_);
                v_desc_1718_ = v___x_1867_;
                v___y_1719_ = v_a_1505_;
                v___y_1720_ = v_a_1506_;
                state = 17;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(
    mut v_as_1879_: *mut crate::leanh::LeanObject,
    mut v___y_1880_: *mut crate::leanh::LeanObject,
    mut v___y_1881_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reportingRange_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_1879_) == 0 {
                    v___x_1883_ = crate::leanh::lean_box(0);
                    v___x_1884_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1884_, 0, v___x_1883_);
                    return v___x_1884_;
                } else {
                    v_head_1885_ = crate::leanh::lean_ctor_get(v_as_1879_, 0);
                    crate::leanh::lean_inc(v_head_1885_);
                    v_tail_1886_ = crate::leanh::lean_ctor_get(v_as_1879_, 1);
                    crate::leanh::lean_inc(v_tail_1886_);
                    crate::leanh::lean_dec_ref_known(v_as_1879_, 2);
                    v_reportingRange_1887_ = crate::leanh::lean_ctor_get(v_head_1885_, 1);
                    crate::leanh::lean_inc(v_reportingRange_1887_);
                    v___x_1888_ = l_Lean_Language_SnapshotTask_get___redArg(v_head_1885_);
                    v___x_1889_ =
                        l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go(
                            v_reportingRange_1887_,
                            v___x_1888_,
                            v___y_1880_,
                            v___y_1881_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_1889_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_1889_, 1);
                        v_as_1879_ = v_tail_1886_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_tail_1886_);
                        return v___x_1889_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1___boxed(
    mut v_as_1891_: *mut crate::leanh::LeanObject,
    mut v___y_1892_: *mut crate::leanh::LeanObject,
    mut v___y_1893_: *mut crate::leanh::LeanObject,
    mut v___y_1894_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1895_ = l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(v_as_1891_, v___y_1892_, v___y_1893_);
    crate::leanh::lean_dec(v___y_1893_);
    crate::leanh::lean_dec_ref(v___y_1892_);
    return v_res_1895_;
}
pub unsafe fn l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___boxed(
    mut v_range_x3f_1896_: *mut crate::leanh::LeanObject,
    mut v_s_1897_: *mut crate::leanh::LeanObject,
    mut v_a_1898_: *mut crate::leanh::LeanObject,
    mut v_a_1899_: *mut crate::leanh::LeanObject,
    mut v_a_1900_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1901_ = l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go(
        v_range_x3f_1896_,
        v_s_1897_,
        v_a_1898_,
        v_a_1899_,
    );
    crate::leanh::lean_dec(v_a_1899_);
    crate::leanh::lean_dec_ref(v_a_1898_);
    return v_res_1901_;
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0(
    mut v_x_1902_: *mut crate::leanh::LeanObject,
    mut v_x_1903_: *mut crate::leanh::LeanObject,
    mut v___y_1904_: *mut crate::leanh::LeanObject,
    mut v___y_1905_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1907_ = l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___redArg(v_x_1902_, v_x_1903_);
    return v___x_1907_;
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___boxed(
    mut v_x_1908_: *mut crate::leanh::LeanObject,
    mut v_x_1909_: *mut crate::leanh::LeanObject,
    mut v___y_1910_: *mut crate::leanh::LeanObject,
    mut v___y_1911_: *mut crate::leanh::LeanObject,
    mut v___y_1912_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1913_ = l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0(v_x_1908_, v_x_1909_, v___y_1910_, v___y_1911_);
    crate::leanh::lean_dec(v___y_1911_);
    crate::leanh::lean_dec_ref(v___y_1910_);
    return v_res_1913_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__10(
    mut v_00_u03b1_1914_: *mut crate::leanh::LeanObject,
    mut v_x_1915_: *mut crate::leanh::LeanObject,
    mut v___y_1916_: *mut crate::leanh::LeanObject,
    mut v___y_1917_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1919_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__10___redArg(v_x_1915_);
    return v___x_1919_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__10___boxed(
    mut v_00_u03b1_1920_: *mut crate::leanh::LeanObject,
    mut v_x_1921_: *mut crate::leanh::LeanObject,
    mut v___y_1922_: *mut crate::leanh::LeanObject,
    mut v___y_1923_: *mut crate::leanh::LeanObject,
    mut v___y_1924_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1925_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__10(v_00_u03b1_1920_, v_x_1921_, v___y_1922_, v___y_1923_);
    crate::leanh::lean_dec(v___y_1923_);
    crate::leanh::lean_dec_ref(v___y_1922_);
    return v_res_1925_;
}
pub unsafe fn l_Lean_Language_SnapshotTree_trace(
    mut v_s_1926_: *mut crate::leanh::LeanObject,
    mut v_a_1927_: *mut crate::leanh::LeanObject,
    mut v_a_1928_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1930_ = crate::leanh::lean_box(2);
    v___x_1931_ = l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go(
        v___x_1930_,
        v_s_1926_,
        v_a_1927_,
        v_a_1928_,
    );
    return v___x_1931_;
}
pub unsafe fn l_Lean_Language_SnapshotTree_trace___boxed(
    mut v_s_1932_: *mut crate::leanh::LeanObject,
    mut v_a_1933_: *mut crate::leanh::LeanObject,
    mut v_a_1934_: *mut crate::leanh::LeanObject,
    mut v_a_1935_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1936_ = l_Lean_Language_SnapshotTree_trace(v_s_1932_, v_a_1933_, v_a_1934_);
    crate::leanh::lean_dec(v_a_1934_);
    crate::leanh::lean_dec_ref(v_a_1933_);
    return v_res_1936_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Language_Util(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_InfoTree(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Format_Macro(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Language_Util(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Language_Util(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_InfoTree(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Format_Macro(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Language_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Language_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Language_Util(builtin);
}
