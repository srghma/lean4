// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Normalize
// Imports: Lean.Elab.Tactic.FalseOrByContra Lean.Meta.Tactic.BVDecide.Normalize.Basic Lean.Meta.Tactic.BVDecide.Normalize.ApplyControlFlow Lean.Meta.Tactic.BVDecide.Normalize.Simproc Lean.Meta.Tactic.BVDecide.Normalize.Rewrite Lean.Meta.Tactic.BVDecide.Normalize.AndFlatten Lean.Meta.Tactic.BVDecide.Normalize.EmbeddedConstraint Lean.Meta.Tactic.BVDecide.Normalize.AC Lean.Meta.Tactic.BVDecide.Normalize.Structures Lean.Meta.Tactic.BVDecide.Normalize.IntToBitVec Lean.Meta.Tactic.BVDecide.Normalize.Enums Lean.Meta.Tactic.BVDecide.Normalize.TypeAnalysis Lean.Meta.Tactic.BVDecide.Normalize.ShortCircuit
use crate::ffi::{
    lean_array_get_size, lean_array_size, lean_array_uget_borrowed, lean_array_uset,
    lean_float_decLt, lean_float_div, lean_float_sub, lean_io_get_num_heartbeats,
    lean_io_mono_nanos_now, lean_mk_array, lean_mk_empty_array_with_capacity, lean_nat_div,
    lean_nat_mul, lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
    lean_usize_add, lean_usize_dec_lt,
};
use crate::r#gen::Init::Data::List::Basic::l_List_appendTR___redArg;
use crate::r#gen::Init::Data::Nat::Power2::Basic::l_Nat_nextPowerOfTwo;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Prelude::{l_Lean_Name_append, l_Lean_replaceRef};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::PersistentArray::{
    l_Lean_PersistentArray_append___redArg, l_Lean_PersistentArray_push___redArg,
    l_Lean_PersistentArray_toArray___redArg,
};
use crate::r#gen::Lean::Elab::Tactic::FalseOrByContra::{
    initialize_Lean_Elab_Tactic_FalseOrByContra, l_Lean_MVarId_falseOrByContra,
    runtime_initialize_Lean_Elab_Tactic_FalseOrByContra,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofName, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp;
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Normalize::AC::{
    initialize_Lean_Meta_Tactic_BVDecide_Normalize_AC,
    l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass,
    runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_AC,
};
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Normalize::AndFlatten::{
    initialize_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten,
    l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass,
    runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten,
};
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Normalize::ApplyControlFlow::{
    initialize_Lean_Meta_Tactic_BVDecide_Normalize_ApplyControlFlow,
    runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_ApplyControlFlow,
};
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Normalize::Basic::{
    initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic,
    l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline,
    runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic,
};
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Normalize::EmbeddedConstraint::{
    initialize_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint,
    l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass,
    runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint,
};
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Normalize::Enums::{
    initialize_Lean_Meta_Tactic_BVDecide_Normalize_Enums,
    l_Lean_Meta_Tactic_BVDecide_Normalize_enumsPass,
    runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Enums,
};
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Normalize::IntToBitVec::{
    initialize_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec,
    l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass,
    runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec,
};
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Normalize::Rewrite::{
    initialize_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite,
    l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass,
    runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite,
};
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Normalize::ShortCircuit::{
    initialize_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit,
    l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass,
    runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit,
};
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Normalize::Simproc::{
    initialize_Lean_Meta_Tactic_BVDecide_Normalize_Simproc,
    runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Simproc,
};
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Normalize::Structures::{
    initialize_Lean_Meta_Tactic_BVDecide_Normalize_Structures,
    l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass,
    runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Structures,
};
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Normalize::TypeAnalysis::{
    initialize_Lean_Meta_Tactic_BVDecide_Normalize_TypeAnalysis,
    l_Lean_Meta_Tactic_BVDecide_Normalize_typeAnalysisPass,
    runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_TypeAnalysis,
};
use crate::r#gen::Lean::Meta::Tactic::Util::l_Lean_Meta_getPropHyps___boxed;
use crate::r#gen::Lean::Util::Trace::{
    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go, l_Lean_TraceResult_toEmoji,
    l_Lean_trace_profiler, l_Lean_trace_profiler_threshold, l_Lean_trace_profiler_useHeartbeats,
};
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__0_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [82, 117, 110, 110, 105, 110, 103, 32, 112, 97, 115, 115, 58, 32, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__2_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [32, 111, 110, 10, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__1_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__2_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__2_value: crate::leanh::LeanStringObject<54> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [60, 101, 120, 99, 101, 112, 116, 105, 111, 110, 32, 116, 104, 114, 111, 119, 110, 32, 119, 104, 105, 108, 101, 32, 112, 114, 111, 100, 117, 99, 105, 110, 103, 32, 116, 114, 97, 99, 101, 32, 110, 111, 100, 101, 32, 109, 101, 115, 115, 97, 103, 101, 62, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__4: f64 = 0.0;
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__2_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [98, 118, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__2_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__0_value) as *mut crate::leanh::LeanObject,142734480563613395 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__1_value) as *mut crate::leanh::LeanObject,15847151208953044930 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__2_value) as *mut crate::leanh::LeanObject,10551690841954068875 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__4: f64 = 0.0;
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__5_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__5_value) as *mut crate::leanh::LeanObject,14231257465488249300 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__8_value: crate::leanh::LeanStringObject<31> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 31, m_capacity: 31, m_length: 30, m_data: [82, 117, 110, 110, 105, 110, 103, 32, 102, 105, 120, 112, 111, 105, 110, 116, 32, 112, 105, 112, 101, 108, 105, 110, 101, 32, 111, 110, 58, 10, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__10_value: crate::leanh::LeanStringObject<36> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 36, m_capacity: 36, m_length: 35, m_data: [82, 117, 110, 110, 105, 110, 103, 32, 112, 114, 101, 112, 114, 111, 99, 101, 115, 115, 105, 110, 103, 32, 112, 105, 112, 101, 108, 105, 110, 101, 32, 111, 110, 58, 10, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__10_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__11: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 19,
    m_capacity: 19,
    m_length: 18,
    m_data: [
        80, 114, 101, 112, 114, 111, 99, 101, 115, 115, 105, 110, 103, 32, 103, 111, 97, 108, 0,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___closed__0_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___closed__1_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_getPropHyps___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__4_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2047_ = crate::leanh::lean_box(0);
    v___x_2048_ = l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass;
    v___x_2049_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2049_, 0, v___x_2048_);
    crate::leanh::lean_ctor_set(v___x_2049_, 1, v___x_2047_);
    return v___x_2049_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2050_ = crate::leanh::lean_box(0);
    v___x_2051_ = l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass;
    v___x_2052_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2052_, 0, v___x_2051_);
    crate::leanh::lean_ctor_set(v___x_2052_, 1, v___x_2050_);
    return v___x_2052_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_passPipeline_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2053_ = crate::leanh::lean_box(0);
    v___x_2054_ = l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass;
    v_passPipeline_2055_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v_passPipeline_2055_, 0, v___x_2054_);
    crate::leanh::lean_ctor_set(v_passPipeline_2055_, 1, v___x_2053_);
    return v_passPipeline_2055_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2056_ = crate::leanh::lean_box(0);
    v___x_2057_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass;
    v___x_2058_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2058_, 0, v___x_2057_);
    crate::leanh::lean_ctor_set(v___x_2058_, 1, v___x_2056_);
    return v___x_2058_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_passPipeline_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2059_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__3_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__3);
    v_passPipeline_2060_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__2_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__2);
    v___x_2061_ = l_List_appendTR___redArg(v_passPipeline_2060_, v___x_2059_);
    return v___x_2061_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg(
    mut v_a_2062_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_acNf_2064_: u8 = 0;
    let mut v_andFlattening_2065_: u8 = 0;
    let mut v_embeddedConstraintSubst_2066_: u8 = 0;
    let mut v_passPipeline_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_passPipeline_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_passPipeline_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_acNf_2064_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_2062_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 2) as u32,
                );
                v_andFlattening_2065_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_2062_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 3) as u32,
                );
                v_embeddedConstraintSubst_2066_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_2062_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 4) as u32,
                );
                v_passPipeline_2077_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__2_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__2);
                if v_acNf_2064_ == 0 {
                    v_passPipeline_2074_ = v_passPipeline_2077_;
                    state = 2;
                    continue;
                } else {
                    v___x_2078_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__4_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__4);
                    v_passPipeline_2074_ = v___x_2078_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                if v_embeddedConstraintSubst_2066_ == 0 {
                    v___x_2069_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2069_, 0, v_passPipeline_2068_);
                    return v___x_2069_;
                } else {
                    v___x_2070_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__0_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__0);
                    v___x_2071_ = l_List_appendTR___redArg(v_passPipeline_2068_, v___x_2070_);
                    v___x_2072_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2072_, 0, v___x_2071_);
                    return v___x_2072_;
                }
            }
            2 => {
                if v_embeddedConstraintSubst_2066_ == 0 {
                    crate::leanh::lean_inc(v_passPipeline_2074_);
                    v_passPipeline_2068_ = v_passPipeline_2074_;
                    state = 1;
                    continue;
                } else {
                    if v_andFlattening_2065_ == 0 {
                        crate::leanh::lean_inc(v_passPipeline_2074_);
                        v_passPipeline_2068_ = v_passPipeline_2074_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2075_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__1_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__1);
                        crate::leanh::lean_inc(v_passPipeline_2074_);
                        v___x_2076_ = l_List_appendTR___redArg(v_passPipeline_2074_, v___x_2075_);
                        v_passPipeline_2068_ = v___x_2076_;
                        state = 1;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___boxed(
    mut v_a_2079_: *mut crate::leanh::LeanObject,
    mut v_a_2080_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2081_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg(v_a_2079_);
    crate::leanh::lean_dec_ref(v_a_2079_);
    return v_res_2081_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline(
    mut v_a_2082_: *mut crate::leanh::LeanObject,
    mut v_a_2083_: *mut crate::leanh::LeanObject,
    mut v_a_2084_: *mut crate::leanh::LeanObject,
    mut v_a_2085_: *mut crate::leanh::LeanObject,
    mut v_a_2086_: *mut crate::leanh::LeanObject,
    mut v_a_2087_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2089_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg(v_a_2082_);
    return v___x_2089_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___boxed(
    mut v_a_2090_: *mut crate::leanh::LeanObject,
    mut v_a_2091_: *mut crate::leanh::LeanObject,
    mut v_a_2092_: *mut crate::leanh::LeanObject,
    mut v_a_2093_: *mut crate::leanh::LeanObject,
    mut v_a_2094_: *mut crate::leanh::LeanObject,
    mut v_a_2095_: *mut crate::leanh::LeanObject,
    mut v_a_2096_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2097_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline(v_a_2090_, v_a_2091_, v_a_2092_, v_a_2093_, v_a_2094_, v_a_2095_);
    crate::leanh::lean_dec(v_a_2095_);
    crate::leanh::lean_dec_ref(v_a_2094_);
    crate::leanh::lean_dec(v_a_2093_);
    crate::leanh::lean_dec_ref(v_a_2092_);
    crate::leanh::lean_dec(v_a_2091_);
    crate::leanh::lean_dec_ref(v_a_2090_);
    return v_res_2097_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2098_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_2099_ = lean_mk_empty_array_with_capacity(v___x_2098_);
    v___x_2100_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2100_, 0, v___x_2099_);
    return v___x_2100_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2101_: usize = 0;
    let mut v___x_2102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2101_ = 5usize;
    v___x_2102_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2103_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_2104_ = lean_mk_empty_array_with_capacity(v___x_2103_);
    v___x_2105_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___redArg___closed__0_once), _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___redArg___closed__0);
    v___x_2106_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_2106_, 0, v___x_2105_);
    crate::leanh::lean_ctor_set(v___x_2106_, 1, v___x_2104_);
    crate::leanh::lean_ctor_set(v___x_2106_, 2, v___x_2102_);
    crate::leanh::lean_ctor_set(v___x_2106_, 3, v___x_2102_);
    crate::leanh::lean_ctor_set_usize(v___x_2106_, 4, v___x_2101_);
    return v___x_2106_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___redArg(
    mut v___y_2107_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traces_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2124_: u8 = 0;
    let mut v_tid_2125_: u64 = 0;
    let mut v___x_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2128_: u8 = 0;
    let mut v___x_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2138_: u8 = 0;
    let mut v_unused_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2140_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2109_ = lean_st_ref_get(v___y_2107_);
                v_traceState_2110_ = crate::leanh::lean_ctor_get(v___x_2109_, 4);
                crate::leanh::lean_inc_ref(v_traceState_2110_);
                crate::leanh::lean_dec(v___x_2109_);
                v_traces_2111_ = crate::leanh::lean_ctor_get(v_traceState_2110_, 0);
                crate::leanh::lean_inc_ref(v_traces_2111_);
                crate::leanh::lean_dec_ref(v_traceState_2110_);
                v___x_2112_ = lean_st_ref_take(v___y_2107_);
                v_traceState_2113_ = crate::leanh::lean_ctor_get(v___x_2112_, 4);
                v_env_2114_ = crate::leanh::lean_ctor_get(v___x_2112_, 0);
                v_nextMacroScope_2115_ = crate::leanh::lean_ctor_get(v___x_2112_, 1);
                v_ngen_2116_ = crate::leanh::lean_ctor_get(v___x_2112_, 2);
                v_auxDeclNGen_2117_ = crate::leanh::lean_ctor_get(v___x_2112_, 3);
                v_cache_2118_ = crate::leanh::lean_ctor_get(v___x_2112_, 5);
                v_messages_2119_ = crate::leanh::lean_ctor_get(v___x_2112_, 6);
                v_infoState_2120_ = crate::leanh::lean_ctor_get(v___x_2112_, 7);
                v_snapshotTasks_2121_ = crate::leanh::lean_ctor_get(v___x_2112_, 8);
                v_isSharedCheck_2140_ = (!crate::leanh::lean_is_exclusive(v___x_2112_)) as u8;
                if v_isSharedCheck_2140_ == 0 {
                    v___x_2123_ = v___x_2112_;
                    v_isShared_2124_ = v_isSharedCheck_2140_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_2121_);
                    crate::leanh::lean_inc(v_infoState_2120_);
                    crate::leanh::lean_inc(v_messages_2119_);
                    crate::leanh::lean_inc(v_cache_2118_);
                    crate::leanh::lean_inc(v_traceState_2113_);
                    crate::leanh::lean_inc(v_auxDeclNGen_2117_);
                    crate::leanh::lean_inc(v_ngen_2116_);
                    crate::leanh::lean_inc(v_nextMacroScope_2115_);
                    crate::leanh::lean_inc(v_env_2114_);
                    crate::leanh::lean_dec(v___x_2112_);
                    v___x_2123_ = crate::leanh::lean_box(0);
                    v_isShared_2124_ = v_isSharedCheck_2140_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_tid_2125_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_2113_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_2138_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_2113_)) as u8;
                if v_isSharedCheck_2138_ == 0 {
                    v_unused_2139_ = crate::leanh::lean_ctor_get(v_traceState_2113_, 0);
                    crate::leanh::lean_dec(v_unused_2139_);
                    v___x_2127_ = v_traceState_2113_;
                    v_isShared_2128_ = v_isSharedCheck_2138_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_traceState_2113_);
                    v___x_2127_ = crate::leanh::lean_box(0);
                    v_isShared_2128_ = v_isSharedCheck_2138_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2129_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___redArg___closed__1_once), _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___redArg___closed__1);
                if v_isShared_2128_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2127_, 0, v___x_2129_);
                    v___x_2131_ = v___x_2127_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2137_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2137_, 0, v___x_2129_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_2137_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_2125_,
                    );
                    v___x_2131_ = v_reuseFailAlloc_2137_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2124_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2123_, 4, v___x_2131_);
                    v___x_2133_ = v___x_2123_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2136_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_env_2114_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2136_, 1, v_nextMacroScope_2115_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2136_, 2, v_ngen_2116_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2136_, 3, v_auxDeclNGen_2117_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2136_, 4, v___x_2131_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2136_, 5, v_cache_2118_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2136_, 6, v_messages_2119_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2136_, 7, v_infoState_2120_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2136_, 8, v_snapshotTasks_2121_);
                    v___x_2133_ = v_reuseFailAlloc_2136_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2134_ = lean_st_ref_set(v___y_2107_, v___x_2133_);
                v___x_2135_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2135_, 0, v_traces_2111_);
                return v___x_2135_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___redArg___boxed(
    mut v___y_2141_: *mut crate::leanh::LeanObject,
    mut v___y_2142_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2143_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___redArg(v___y_2141_);
    crate::leanh::lean_dec(v___y_2141_);
    return v_res_2143_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0(
    mut v___y_2144_: *mut crate::leanh::LeanObject,
    mut v___y_2145_: *mut crate::leanh::LeanObject,
    mut v___y_2146_: *mut crate::leanh::LeanObject,
    mut v___y_2147_: *mut crate::leanh::LeanObject,
    mut v___y_2148_: *mut crate::leanh::LeanObject,
    mut v___y_2149_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2151_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___redArg(v___y_2149_);
    return v___x_2151_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___boxed(
    mut v___y_2152_: *mut crate::leanh::LeanObject,
    mut v___y_2153_: *mut crate::leanh::LeanObject,
    mut v___y_2154_: *mut crate::leanh::LeanObject,
    mut v___y_2155_: *mut crate::leanh::LeanObject,
    mut v___y_2156_: *mut crate::leanh::LeanObject,
    mut v___y_2157_: *mut crate::leanh::LeanObject,
    mut v___y_2158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2159_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0(v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_);
    crate::leanh::lean_dec(v___y_2157_);
    crate::leanh::lean_dec_ref(v___y_2156_);
    crate::leanh::lean_dec(v___y_2155_);
    crate::leanh::lean_dec_ref(v___y_2154_);
    crate::leanh::lean_dec(v___y_2153_);
    crate::leanh::lean_dec_ref(v___y_2152_);
    return v_res_2159_;
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__1(
    mut v_opts_2160_: *mut crate::leanh::LeanObject,
    mut v_opt_2161_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_2162_ = crate::leanh::lean_ctor_get(v_opt_2161_, 0);
    v_defValue_2163_ = crate::leanh::lean_ctor_get(v_opt_2161_, 1);
    v_map_2164_ = crate::leanh::lean_ctor_get(v_opts_2160_, 0);
    v___x_2165_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2164_,
            v_name_2162_,
        );
    if crate::leanh::lean_obj_tag(v___x_2165_) == 0 {
        let mut v___x_2166_: u8 = 0;
        v___x_2166_ = (crate::leanh::lean_unbox(v_defValue_2163_) as u8);
        return v___x_2166_;
    } else {
        let mut v_val_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2167_ = crate::leanh::lean_ctor_get(v___x_2165_, 0);
        crate::leanh::lean_inc(v_val_2167_);
        crate::leanh::lean_dec_ref_known(v___x_2165_, 1);
        if crate::leanh::lean_obj_tag(v_val_2167_) == 1 {
            let mut v_v_2168_: u8 = 0;
            v_v_2168_ = crate::leanh::lean_ctor_get_uint8(v_val_2167_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_2167_, 0);
            return v_v_2168_;
        } else {
            let mut v___x_2169_: u8 = 0;
            crate::leanh::lean_dec(v_val_2167_);
            v___x_2169_ = (crate::leanh::lean_unbox(v_defValue_2163_) as u8);
            return v___x_2169_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__1___boxed(
    mut v_opts_2170_: *mut crate::leanh::LeanObject,
    mut v_opt_2171_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2172_: u8 = 0;
    let mut v_r_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2172_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__1(v_opts_2170_, v_opt_2171_);
    crate::leanh::lean_dec_ref(v_opt_2171_);
    crate::leanh::lean_dec_ref(v_opts_2170_);
    v_r_2173_ = crate::leanh::lean_box((v_res_2172_) as usize);
    return v_r_2173_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2175_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__0;
    v___x_2176_ = l_Lean_stringToMessageData(v___x_2175_);
    return v___x_2176_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2178_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__2;
    v___x_2179_ = l_Lean_stringToMessageData(v___x_2178_);
    return v___x_2179_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0(
    mut v___x_2180_: *mut crate::leanh::LeanObject,
    mut v_val_2181_: *mut crate::leanh::LeanObject,
    mut v_x_2182_: *mut crate::leanh::LeanObject,
    mut v___y_2183_: *mut crate::leanh::LeanObject,
    mut v___y_2184_: *mut crate::leanh::LeanObject,
    mut v___y_2185_: *mut crate::leanh::LeanObject,
    mut v___y_2186_: *mut crate::leanh::LeanObject,
    mut v___y_2187_: *mut crate::leanh::LeanObject,
    mut v___y_2188_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2193_: u8 = 0;
    let mut v___x_2194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2204_: u8 = 0;
    let mut v_unused_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_2190_ = crate::leanh::lean_ctor_get(v___x_2180_, 0);
                v_isSharedCheck_2204_ = (!crate::leanh::lean_is_exclusive(v___x_2180_)) as u8;
                if v_isSharedCheck_2204_ == 0 {
                    v_unused_2205_ = crate::leanh::lean_ctor_get(v___x_2180_, 1);
                    crate::leanh::lean_dec(v_unused_2205_);
                    v___x_2192_ = v___x_2180_;
                    v_isShared_2193_ = v_isSharedCheck_2204_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_name_2190_);
                    crate::leanh::lean_dec(v___x_2180_);
                    v___x_2192_ = crate::leanh::lean_box(0);
                    v_isShared_2193_ = v_isSharedCheck_2204_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2194_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__1_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__1);
                v___x_2195_ = l_Lean_MessageData_ofName(v_name_2190_);
                if v_isShared_2193_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2192_, 7);
                    crate::leanh::lean_ctor_set(v___x_2192_, 1, v___x_2195_);
                    crate::leanh::lean_ctor_set(v___x_2192_, 0, v___x_2194_);
                    v___x_2197_ = v___x_2192_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2203_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2203_, 0, v___x_2194_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2203_, 1, v___x_2195_);
                    v___x_2197_ = v_reuseFailAlloc_2203_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2198_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__3_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__3);
                v___x_2199_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2199_, 0, v___x_2197_);
                crate::leanh::lean_ctor_set(v___x_2199_, 1, v___x_2198_);
                v___x_2200_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2200_, 0, v_val_2181_);
                v___x_2201_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2201_, 0, v___x_2199_);
                crate::leanh::lean_ctor_set(v___x_2201_, 1, v___x_2200_);
                v___x_2202_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2202_, 0, v___x_2201_);
                return v___x_2202_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___boxed(
    mut v___x_2206_: *mut crate::leanh::LeanObject,
    mut v_val_2207_: *mut crate::leanh::LeanObject,
    mut v_x_2208_: *mut crate::leanh::LeanObject,
    mut v___y_2209_: *mut crate::leanh::LeanObject,
    mut v___y_2210_: *mut crate::leanh::LeanObject,
    mut v___y_2211_: *mut crate::leanh::LeanObject,
    mut v___y_2212_: *mut crate::leanh::LeanObject,
    mut v___y_2213_: *mut crate::leanh::LeanObject,
    mut v___y_2214_: *mut crate::leanh::LeanObject,
    mut v___y_2215_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2216_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0(v___x_2206_, v_val_2207_, v_x_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_);
    crate::leanh::lean_dec(v___y_2214_);
    crate::leanh::lean_dec_ref(v___y_2213_);
    crate::leanh::lean_dec(v___y_2212_);
    crate::leanh::lean_dec_ref(v___y_2211_);
    crate::leanh::lean_dec(v___y_2210_);
    crate::leanh::lean_dec_ref(v___y_2209_);
    crate::leanh::lean_dec_ref(v_x_2208_);
    return v_res_2216_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__1(
    mut v___x_2217_: *mut crate::leanh::LeanObject,
    mut v_g_2218_: *mut crate::leanh::LeanObject,
    mut v_x_2219_: *mut crate::leanh::LeanObject,
    mut v___y_2220_: *mut crate::leanh::LeanObject,
    mut v___y_2221_: *mut crate::leanh::LeanObject,
    mut v___y_2222_: *mut crate::leanh::LeanObject,
    mut v___y_2223_: *mut crate::leanh::LeanObject,
    mut v___y_2224_: *mut crate::leanh::LeanObject,
    mut v___y_2225_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2230_: u8 = 0;
    let mut v___x_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2241_: u8 = 0;
    let mut v_unused_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_2227_ = crate::leanh::lean_ctor_get(v___x_2217_, 0);
                v_isSharedCheck_2241_ = (!crate::leanh::lean_is_exclusive(v___x_2217_)) as u8;
                if v_isSharedCheck_2241_ == 0 {
                    v_unused_2242_ = crate::leanh::lean_ctor_get(v___x_2217_, 1);
                    crate::leanh::lean_dec(v_unused_2242_);
                    v___x_2229_ = v___x_2217_;
                    v_isShared_2230_ = v_isSharedCheck_2241_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_name_2227_);
                    crate::leanh::lean_dec(v___x_2217_);
                    v___x_2229_ = crate::leanh::lean_box(0);
                    v_isShared_2230_ = v_isSharedCheck_2241_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2231_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__1_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__1);
                v___x_2232_ = l_Lean_MessageData_ofName(v_name_2227_);
                if v_isShared_2230_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2229_, 7);
                    crate::leanh::lean_ctor_set(v___x_2229_, 1, v___x_2232_);
                    crate::leanh::lean_ctor_set(v___x_2229_, 0, v___x_2231_);
                    v___x_2234_ = v___x_2229_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2240_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2240_, 0, v___x_2231_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2240_, 1, v___x_2232_);
                    v___x_2234_ = v_reuseFailAlloc_2240_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2235_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__3_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__3);
                v___x_2236_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2236_, 0, v___x_2234_);
                crate::leanh::lean_ctor_set(v___x_2236_, 1, v___x_2235_);
                v___x_2237_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2237_, 0, v_g_2218_);
                v___x_2238_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2238_, 0, v___x_2236_);
                crate::leanh::lean_ctor_set(v___x_2238_, 1, v___x_2237_);
                v___x_2239_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2239_, 0, v___x_2238_);
                return v___x_2239_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__1___boxed(
    mut v___x_2243_: *mut crate::leanh::LeanObject,
    mut v_g_2244_: *mut crate::leanh::LeanObject,
    mut v_x_2245_: *mut crate::leanh::LeanObject,
    mut v___y_2246_: *mut crate::leanh::LeanObject,
    mut v___y_2247_: *mut crate::leanh::LeanObject,
    mut v___y_2248_: *mut crate::leanh::LeanObject,
    mut v___y_2249_: *mut crate::leanh::LeanObject,
    mut v___y_2250_: *mut crate::leanh::LeanObject,
    mut v___y_2251_: *mut crate::leanh::LeanObject,
    mut v___y_2252_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2253_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__1(v___x_2243_, v_g_2244_, v_x_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_);
    crate::leanh::lean_dec(v___y_2251_);
    crate::leanh::lean_dec_ref(v___y_2250_);
    crate::leanh::lean_dec(v___y_2249_);
    crate::leanh::lean_dec_ref(v___y_2248_);
    crate::leanh::lean_dec(v___y_2247_);
    crate::leanh::lean_dec_ref(v___y_2246_);
    crate::leanh::lean_dec_ref(v_x_2245_);
    return v_res_2253_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3_spec__7(
    mut v_msgData_2254_: *mut crate::leanh::LeanObject,
    mut v___y_2255_: *mut crate::leanh::LeanObject,
    mut v___y_2256_: *mut crate::leanh::LeanObject,
    mut v___y_2257_: *mut crate::leanh::LeanObject,
    mut v___y_2258_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2260_ = lean_st_ref_get(v___y_2258_);
    v_env_2261_ = crate::leanh::lean_ctor_get(v___x_2260_, 0);
    crate::leanh::lean_inc_ref(v_env_2261_);
    crate::leanh::lean_dec(v___x_2260_);
    v___x_2262_ = lean_st_ref_get(v___y_2256_);
    v_mctx_2263_ = crate::leanh::lean_ctor_get(v___x_2262_, 0);
    crate::leanh::lean_inc_ref(v_mctx_2263_);
    crate::leanh::lean_dec(v___x_2262_);
    v_lctx_2264_ = crate::leanh::lean_ctor_get(v___y_2255_, 2);
    v_options_2265_ = crate::leanh::lean_ctor_get(v___y_2257_, 2);
    crate::leanh::lean_inc_ref(v_options_2265_);
    crate::leanh::lean_inc_ref(v_lctx_2264_);
    v___x_2266_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2266_, 0, v_env_2261_);
    crate::leanh::lean_ctor_set(v___x_2266_, 1, v_mctx_2263_);
    crate::leanh::lean_ctor_set(v___x_2266_, 2, v_lctx_2264_);
    crate::leanh::lean_ctor_set(v___x_2266_, 3, v_options_2265_);
    v___x_2267_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2267_, 0, v___x_2266_);
    crate::leanh::lean_ctor_set(v___x_2267_, 1, v_msgData_2254_);
    v___x_2268_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2268_, 0, v___x_2267_);
    return v___x_2268_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3_spec__7___boxed(
    mut v_msgData_2269_: *mut crate::leanh::LeanObject,
    mut v___y_2270_: *mut crate::leanh::LeanObject,
    mut v___y_2271_: *mut crate::leanh::LeanObject,
    mut v___y_2272_: *mut crate::leanh::LeanObject,
    mut v___y_2273_: *mut crate::leanh::LeanObject,
    mut v___y_2274_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2275_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3_spec__7(v_msgData_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_);
    crate::leanh::lean_dec(v___y_2273_);
    crate::leanh::lean_dec_ref(v___y_2272_);
    crate::leanh::lean_dec(v___y_2271_);
    crate::leanh::lean_dec_ref(v___y_2270_);
    return v_res_2275_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__0()
-> f64 {
    let mut v___x_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: f64 = 0.0;
    v___x_2276_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2277_ = lean_float_of_nat(v___x_2276_);
    return v___x_2277_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg(
    mut v_cls_2281_: *mut crate::leanh::LeanObject,
    mut v_msg_2282_: *mut crate::leanh::LeanObject,
    mut v___y_2283_: *mut crate::leanh::LeanObject,
    mut v___y_2284_: *mut crate::leanh::LeanObject,
    mut v___y_2285_: *mut crate::leanh::LeanObject,
    mut v___y_2286_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2293_: u8 = 0;
    let mut v___x_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2306_: u8 = 0;
    let mut v_tid_2307_: u64 = 0;
    let mut v_traces_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2311_: u8 = 0;
    let mut v___x_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: f64 = 0.0;
    let mut v___x_2314_: u8 = 0;
    let mut v___x_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2332_: u8 = 0;
    let mut v_isSharedCheck_2333_: u8 = 0;
    let mut v_isSharedCheck_2334_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2288_ = crate::leanh::lean_ctor_get(v___y_2285_, 5);
                v___x_2289_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3_spec__7(v_msg_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_);
                v_a_2290_ = crate::leanh::lean_ctor_get(v___x_2289_, 0);
                v_isSharedCheck_2334_ = (!crate::leanh::lean_is_exclusive(v___x_2289_)) as u8;
                if v_isSharedCheck_2334_ == 0 {
                    v___x_2292_ = v___x_2289_;
                    v_isShared_2293_ = v_isSharedCheck_2334_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_2290_);
                    crate::leanh::lean_dec(v___x_2289_);
                    v___x_2292_ = crate::leanh::lean_box(0);
                    v_isShared_2293_ = v_isSharedCheck_2334_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2294_ = lean_st_ref_take(v___y_2286_);
                v_traceState_2295_ = crate::leanh::lean_ctor_get(v___x_2294_, 4);
                v_env_2296_ = crate::leanh::lean_ctor_get(v___x_2294_, 0);
                v_nextMacroScope_2297_ = crate::leanh::lean_ctor_get(v___x_2294_, 1);
                v_ngen_2298_ = crate::leanh::lean_ctor_get(v___x_2294_, 2);
                v_auxDeclNGen_2299_ = crate::leanh::lean_ctor_get(v___x_2294_, 3);
                v_cache_2300_ = crate::leanh::lean_ctor_get(v___x_2294_, 5);
                v_messages_2301_ = crate::leanh::lean_ctor_get(v___x_2294_, 6);
                v_infoState_2302_ = crate::leanh::lean_ctor_get(v___x_2294_, 7);
                v_snapshotTasks_2303_ = crate::leanh::lean_ctor_get(v___x_2294_, 8);
                v_isSharedCheck_2333_ = (!crate::leanh::lean_is_exclusive(v___x_2294_)) as u8;
                if v_isSharedCheck_2333_ == 0 {
                    v___x_2305_ = v___x_2294_;
                    v_isShared_2306_ = v_isSharedCheck_2333_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_2303_);
                    crate::leanh::lean_inc(v_infoState_2302_);
                    crate::leanh::lean_inc(v_messages_2301_);
                    crate::leanh::lean_inc(v_cache_2300_);
                    crate::leanh::lean_inc(v_traceState_2295_);
                    crate::leanh::lean_inc(v_auxDeclNGen_2299_);
                    crate::leanh::lean_inc(v_ngen_2298_);
                    crate::leanh::lean_inc(v_nextMacroScope_2297_);
                    crate::leanh::lean_inc(v_env_2296_);
                    crate::leanh::lean_dec(v___x_2294_);
                    v___x_2305_ = crate::leanh::lean_box(0);
                    v_isShared_2306_ = v_isSharedCheck_2333_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_2307_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_2295_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_2308_ = crate::leanh::lean_ctor_get(v_traceState_2295_, 0);
                v_isSharedCheck_2332_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_2295_)) as u8;
                if v_isSharedCheck_2332_ == 0 {
                    v___x_2310_ = v_traceState_2295_;
                    v_isShared_2311_ = v_isSharedCheck_2332_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_2308_);
                    crate::leanh::lean_dec(v_traceState_2295_);
                    v___x_2310_ = crate::leanh::lean_box(0);
                    v_isShared_2311_ = v_isSharedCheck_2332_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2312_ = crate::leanh::lean_box(0);
                v___x_2313_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__0_once), _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__0);
                v___x_2314_ = 0;
                v___x_2315_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__1;
                v___x_2316_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v___x_2316_, 0, v_cls_2281_);
                crate::leanh::lean_ctor_set(v___x_2316_, 1, v___x_2312_);
                crate::leanh::lean_ctor_set(v___x_2316_, 2, v___x_2315_);
                crate::leanh::lean_ctor_set_float(
                    v___x_2316_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_2313_,
                );
                crate::leanh::lean_ctor_set_float(
                    v___x_2316_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_2313_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2316_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_2314_,
                );
                v___x_2317_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__2;
                v___x_2318_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2318_, 0, v___x_2316_);
                crate::leanh::lean_ctor_set(v___x_2318_, 1, v_a_2290_);
                crate::leanh::lean_ctor_set(v___x_2318_, 2, v___x_2317_);
                crate::leanh::lean_inc(v_ref_2288_);
                v___x_2319_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2319_, 0, v_ref_2288_);
                crate::leanh::lean_ctor_set(v___x_2319_, 1, v___x_2318_);
                v___x_2320_ = l_Lean_PersistentArray_push___redArg(v_traces_2308_, v___x_2319_);
                if v_isShared_2311_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2310_, 0, v___x_2320_);
                    v___x_2322_ = v___x_2310_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2331_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2331_, 0, v___x_2320_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_2331_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_2307_,
                    );
                    v___x_2322_ = v_reuseFailAlloc_2331_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2306_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2305_, 4, v___x_2322_);
                    v___x_2324_ = v___x_2305_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2330_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2330_, 0, v_env_2296_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2330_, 1, v_nextMacroScope_2297_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2330_, 2, v_ngen_2298_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2330_, 3, v_auxDeclNGen_2299_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2330_, 4, v___x_2322_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2330_, 5, v_cache_2300_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2330_, 6, v_messages_2301_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2330_, 7, v_infoState_2302_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2330_, 8, v_snapshotTasks_2303_);
                    v___x_2324_ = v_reuseFailAlloc_2330_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2325_ = lean_st_ref_set(v___y_2286_, v___x_2324_);
                v___x_2326_ = crate::leanh::lean_box(0);
                if v_isShared_2293_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2292_, 0, v___x_2326_);
                    v___x_2328_ = v___x_2292_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2329_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2329_, 0, v___x_2326_);
                    v___x_2328_ = v_reuseFailAlloc_2329_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2328_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___boxed(
    mut v_cls_2335_: *mut crate::leanh::LeanObject,
    mut v_msg_2336_: *mut crate::leanh::LeanObject,
    mut v___y_2337_: *mut crate::leanh::LeanObject,
    mut v___y_2338_: *mut crate::leanh::LeanObject,
    mut v___y_2339_: *mut crate::leanh::LeanObject,
    mut v___y_2340_: *mut crate::leanh::LeanObject,
    mut v___y_2341_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2342_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg(v_cls_2335_, v_msg_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_);
    crate::leanh::lean_dec(v___y_2340_);
    crate::leanh::lean_dec_ref(v___y_2339_);
    crate::leanh::lean_dec(v___y_2338_);
    crate::leanh::lean_dec_ref(v___y_2337_);
    return v_res_2342_;
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__5(
    mut v_opts_2343_: *mut crate::leanh::LeanObject,
    mut v_opt_2344_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_2346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_2345_ = crate::leanh::lean_ctor_get(v_opt_2344_, 0);
    v_defValue_2346_ = crate::leanh::lean_ctor_get(v_opt_2344_, 1);
    v_map_2347_ = crate::leanh::lean_ctor_get(v_opts_2343_, 0);
    v___x_2348_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2347_,
            v_name_2345_,
        );
    if crate::leanh::lean_obj_tag(v___x_2348_) == 0 {
        crate::leanh::lean_inc(v_defValue_2346_);
        return v_defValue_2346_;
    } else {
        let mut v_val_2349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2349_ = crate::leanh::lean_ctor_get(v___x_2348_, 0);
        crate::leanh::lean_inc(v_val_2349_);
        crate::leanh::lean_dec_ref_known(v___x_2348_, 1);
        if crate::leanh::lean_obj_tag(v_val_2349_) == 3 {
            let mut v_v_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_v_2350_ = crate::leanh::lean_ctor_get(v_val_2349_, 0);
            crate::leanh::lean_inc(v_v_2350_);
            crate::leanh::lean_dec_ref_known(v_val_2349_, 1);
            return v_v_2350_;
        } else {
            crate::leanh::lean_dec(v_val_2349_);
            crate::leanh::lean_inc(v_defValue_2346_);
            return v_defValue_2346_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__5___boxed(
    mut v_opts_2351_: *mut crate::leanh::LeanObject,
    mut v_opt_2352_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2353_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__5(v_opts_2351_, v_opt_2352_);
    crate::leanh::lean_dec_ref(v_opt_2352_);
    crate::leanh::lean_dec_ref(v_opts_2351_);
    return v_res_2353_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__4___redArg(
    mut v_x_2354_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2359_: u8 = 0;
    let mut v___x_2361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2363_: u8 = 0;
    let mut v_a_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2367_: u8 = 0;
    let mut v___x_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2371_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2354_) == 0 {
                    v_a_2356_ = crate::leanh::lean_ctor_get(v_x_2354_, 0);
                    v_isSharedCheck_2363_ = (!crate::leanh::lean_is_exclusive(v_x_2354_)) as u8;
                    if v_isSharedCheck_2363_ == 0 {
                        v___x_2358_ = v_x_2354_;
                        v_isShared_2359_ = v_isSharedCheck_2363_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2356_);
                        crate::leanh::lean_dec(v_x_2354_);
                        v___x_2358_ = crate::leanh::lean_box(0);
                        v_isShared_2359_ = v_isSharedCheck_2363_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2364_ = crate::leanh::lean_ctor_get(v_x_2354_, 0);
                    v_isSharedCheck_2371_ = (!crate::leanh::lean_is_exclusive(v_x_2354_)) as u8;
                    if v_isSharedCheck_2371_ == 0 {
                        v___x_2366_ = v_x_2354_;
                        v_isShared_2367_ = v_isSharedCheck_2371_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2364_);
                        crate::leanh::lean_dec(v_x_2354_);
                        v___x_2366_ = crate::leanh::lean_box(0);
                        v_isShared_2367_ = v_isSharedCheck_2371_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2359_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2358_, 1);
                    v___x_2361_ = v___x_2358_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2362_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2362_, 0, v_a_2356_);
                    v___x_2361_ = v_reuseFailAlloc_2362_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2361_;
            }
            3 => {
                if v_isShared_2367_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2366_, 0);
                    v___x_2369_ = v___x_2366_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2370_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2370_, 0, v_a_2364_);
                    v___x_2369_ = v_reuseFailAlloc_2370_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2369_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__4___redArg___boxed(
    mut v_x_2372_: *mut crate::leanh::LeanObject,
    mut v___y_2373_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2374_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__4___redArg(v_x_2372_);
    return v_res_2374_;
}
pub unsafe fn l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__2(
    mut v_e_2375_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_e_2375_) == 0 {
        let mut v___x_2376_: u8 = 0;
        v___x_2376_ = 2;
        return v___x_2376_;
    } else {
        let mut v_a_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_2377_ = crate::leanh::lean_ctor_get(v_e_2375_, 0);
        if crate::leanh::lean_obj_tag(v_a_2377_) == 0 {
            let mut v___x_2378_: u8 = 0;
            v___x_2378_ = 1;
            return v___x_2378_;
        } else {
            let mut v___x_2379_: u8 = 0;
            v___x_2379_ = 0;
            return v___x_2379_;
        }
    }
}
pub unsafe fn l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__2___boxed(
    mut v_e_2380_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2381_: u8 = 0;
    let mut v_r_2382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2381_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__2(v_e_2380_);
    crate::leanh::lean_dec_ref(v_e_2380_);
    v_r_2382_ = crate::leanh::lean_box((v_res_2381_) as usize);
    return v_r_2382_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__3_spec__4(
    mut v_sz_2383_: usize,
    mut v_i_2384_: usize,
    mut v_bs_2385_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2386_: u8 = 0;
    let mut v_v_2387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_2388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: usize = 0;
    let mut v___x_2392_: usize = 0;
    let mut v___x_2393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2386_ = lean_usize_dec_lt(v_i_2384_, v_sz_2383_);
                if v___x_2386_ == 0 {
                    return v_bs_2385_;
                } else {
                    v_v_2387_ = lean_array_uget_borrowed(v_bs_2385_, v_i_2384_);
                    v_msg_2388_ = crate::leanh::lean_ctor_get(v_v_2387_, 1);
                    crate::leanh::lean_inc_ref(v_msg_2388_);
                    v___x_2389_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_2390_ = lean_array_uset(v_bs_2385_, v_i_2384_, v___x_2389_);
                    v___x_2391_ = 1usize;
                    v___x_2392_ = lean_usize_add(v_i_2384_, v___x_2391_);
                    v___x_2393_ = lean_array_uset(v_bs_x27_2390_, v_i_2384_, v_msg_2388_);
                    v_i_2384_ = v___x_2392_;
                    v_bs_2385_ = v___x_2393_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__3_spec__4___boxed(
    mut v_sz_2395_: *mut crate::leanh::LeanObject,
    mut v_i_2396_: *mut crate::leanh::LeanObject,
    mut v_bs_2397_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2398_: usize = 0;
    let mut v_i_boxed_2399_: usize = 0;
    let mut v_res_2400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2398_ = crate::leanh::lean_unbox_usize(v_sz_2395_);
    crate::leanh::lean_dec(v_sz_2395_);
    v_i_boxed_2399_ = crate::leanh::lean_unbox_usize(v_i_2396_);
    crate::leanh::lean_dec(v_i_2396_);
    v_res_2400_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__3_spec__4(v_sz_boxed_2398_, v_i_boxed_2399_, v_bs_2397_);
    return v_res_2400_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__3___redArg(
    mut v_oldTraces_2401_: *mut crate::leanh::LeanObject,
    mut v_data_2402_: *mut crate::leanh::LeanObject,
    mut v_ref_2403_: *mut crate::leanh::LeanObject,
    mut v_msg_2404_: *mut crate::leanh::LeanObject,
    mut v___y_2405_: *mut crate::leanh::LeanObject,
    mut v___y_2406_: *mut crate::leanh::LeanObject,
    mut v___y_2407_: *mut crate::leanh::LeanObject,
    mut v___y_2408_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_2410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_2418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_2419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2422_: u8 = 0;
    let mut v_cancelTk_x3f_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2424_: u8 = 0;
    let mut v_inheritedTraceOptions_2425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traces_2428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2432_: usize = 0;
    let mut v___x_2433_: usize = 0;
    let mut v___x_2434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_2435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2440_: u8 = 0;
    let mut v___x_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2453_: u8 = 0;
    let mut v_tid_2454_: u64 = 0;
    let mut v___x_2456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2457_: u8 = 0;
    let mut v___x_2458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2471_: u8 = 0;
    let mut v_unused_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2473_: u8 = 0;
    let mut v_isSharedCheck_2474_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_2410_ = crate::leanh::lean_ctor_get(v___y_2407_, 0);
                v_fileMap_2411_ = crate::leanh::lean_ctor_get(v___y_2407_, 1);
                v_options_2412_ = crate::leanh::lean_ctor_get(v___y_2407_, 2);
                v_currRecDepth_2413_ = crate::leanh::lean_ctor_get(v___y_2407_, 3);
                v_maxRecDepth_2414_ = crate::leanh::lean_ctor_get(v___y_2407_, 4);
                v_ref_2415_ = crate::leanh::lean_ctor_get(v___y_2407_, 5);
                v_currNamespace_2416_ = crate::leanh::lean_ctor_get(v___y_2407_, 6);
                v_openDecls_2417_ = crate::leanh::lean_ctor_get(v___y_2407_, 7);
                v_initHeartbeats_2418_ = crate::leanh::lean_ctor_get(v___y_2407_, 8);
                v_maxHeartbeats_2419_ = crate::leanh::lean_ctor_get(v___y_2407_, 9);
                v_quotContext_2420_ = crate::leanh::lean_ctor_get(v___y_2407_, 10);
                v_currMacroScope_2421_ = crate::leanh::lean_ctor_get(v___y_2407_, 11);
                v_diag_2422_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_2407_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_2423_ = crate::leanh::lean_ctor_get(v___y_2407_, 12);
                v_suppressElabErrors_2424_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_2407_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_2425_ = crate::leanh::lean_ctor_get(v___y_2407_, 13);
                v___x_2426_ = lean_st_ref_get(v___y_2408_);
                v_traceState_2427_ = crate::leanh::lean_ctor_get(v___x_2426_, 4);
                crate::leanh::lean_inc_ref(v_traceState_2427_);
                crate::leanh::lean_dec(v___x_2426_);
                v_traces_2428_ = crate::leanh::lean_ctor_get(v_traceState_2427_, 0);
                crate::leanh::lean_inc_ref(v_traces_2428_);
                crate::leanh::lean_dec_ref(v_traceState_2427_);
                v_ref_2429_ = l_Lean_replaceRef(v_ref_2403_, v_ref_2415_);
                crate::leanh::lean_inc_ref(v_inheritedTraceOptions_2425_);
                crate::leanh::lean_inc(v_cancelTk_x3f_2423_);
                crate::leanh::lean_inc(v_currMacroScope_2421_);
                crate::leanh::lean_inc(v_quotContext_2420_);
                crate::leanh::lean_inc(v_maxHeartbeats_2419_);
                crate::leanh::lean_inc(v_initHeartbeats_2418_);
                crate::leanh::lean_inc(v_openDecls_2417_);
                crate::leanh::lean_inc(v_currNamespace_2416_);
                crate::leanh::lean_inc(v_maxRecDepth_2414_);
                crate::leanh::lean_inc(v_currRecDepth_2413_);
                crate::leanh::lean_inc_ref(v_options_2412_);
                crate::leanh::lean_inc_ref(v_fileMap_2411_);
                crate::leanh::lean_inc_ref(v_fileName_2410_);
                v___x_2430_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_2430_, 0, v_fileName_2410_);
                crate::leanh::lean_ctor_set(v___x_2430_, 1, v_fileMap_2411_);
                crate::leanh::lean_ctor_set(v___x_2430_, 2, v_options_2412_);
                crate::leanh::lean_ctor_set(v___x_2430_, 3, v_currRecDepth_2413_);
                crate::leanh::lean_ctor_set(v___x_2430_, 4, v_maxRecDepth_2414_);
                crate::leanh::lean_ctor_set(v___x_2430_, 5, v_ref_2429_);
                crate::leanh::lean_ctor_set(v___x_2430_, 6, v_currNamespace_2416_);
                crate::leanh::lean_ctor_set(v___x_2430_, 7, v_openDecls_2417_);
                crate::leanh::lean_ctor_set(v___x_2430_, 8, v_initHeartbeats_2418_);
                crate::leanh::lean_ctor_set(v___x_2430_, 9, v_maxHeartbeats_2419_);
                crate::leanh::lean_ctor_set(v___x_2430_, 10, v_quotContext_2420_);
                crate::leanh::lean_ctor_set(v___x_2430_, 11, v_currMacroScope_2421_);
                crate::leanh::lean_ctor_set(v___x_2430_, 12, v_cancelTk_x3f_2423_);
                crate::leanh::lean_ctor_set(v___x_2430_, 13, v_inheritedTraceOptions_2425_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2430_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                    v_diag_2422_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2430_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_2424_,
                );
                v___x_2431_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2428_);
                crate::leanh::lean_dec_ref(v_traces_2428_);
                v_sz_2432_ = lean_array_size(v___x_2431_);
                v___x_2433_ = 0usize;
                v___x_2434_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__3_spec__4(v_sz_2432_, v___x_2433_, v___x_2431_);
                v_msg_2435_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v_msg_2435_, 0, v_data_2402_);
                crate::leanh::lean_ctor_set(v_msg_2435_, 1, v_msg_2404_);
                crate::leanh::lean_ctor_set(v_msg_2435_, 2, v___x_2434_);
                v___x_2436_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3_spec__7(v_msg_2435_, v___y_2405_, v___y_2406_, v___x_2430_, v___y_2408_);
                crate::leanh::lean_dec_ref_known(v___x_2430_, 14);
                v_a_2437_ = crate::leanh::lean_ctor_get(v___x_2436_, 0);
                v_isSharedCheck_2474_ = (!crate::leanh::lean_is_exclusive(v___x_2436_)) as u8;
                if v_isSharedCheck_2474_ == 0 {
                    v___x_2439_ = v___x_2436_;
                    v_isShared_2440_ = v_isSharedCheck_2474_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_2437_);
                    crate::leanh::lean_dec(v___x_2436_);
                    v___x_2439_ = crate::leanh::lean_box(0);
                    v_isShared_2440_ = v_isSharedCheck_2474_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2441_ = lean_st_ref_take(v___y_2408_);
                v_traceState_2442_ = crate::leanh::lean_ctor_get(v___x_2441_, 4);
                v_env_2443_ = crate::leanh::lean_ctor_get(v___x_2441_, 0);
                v_nextMacroScope_2444_ = crate::leanh::lean_ctor_get(v___x_2441_, 1);
                v_ngen_2445_ = crate::leanh::lean_ctor_get(v___x_2441_, 2);
                v_auxDeclNGen_2446_ = crate::leanh::lean_ctor_get(v___x_2441_, 3);
                v_cache_2447_ = crate::leanh::lean_ctor_get(v___x_2441_, 5);
                v_messages_2448_ = crate::leanh::lean_ctor_get(v___x_2441_, 6);
                v_infoState_2449_ = crate::leanh::lean_ctor_get(v___x_2441_, 7);
                v_snapshotTasks_2450_ = crate::leanh::lean_ctor_get(v___x_2441_, 8);
                v_isSharedCheck_2473_ = (!crate::leanh::lean_is_exclusive(v___x_2441_)) as u8;
                if v_isSharedCheck_2473_ == 0 {
                    v___x_2452_ = v___x_2441_;
                    v_isShared_2453_ = v_isSharedCheck_2473_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_2450_);
                    crate::leanh::lean_inc(v_infoState_2449_);
                    crate::leanh::lean_inc(v_messages_2448_);
                    crate::leanh::lean_inc(v_cache_2447_);
                    crate::leanh::lean_inc(v_traceState_2442_);
                    crate::leanh::lean_inc(v_auxDeclNGen_2446_);
                    crate::leanh::lean_inc(v_ngen_2445_);
                    crate::leanh::lean_inc(v_nextMacroScope_2444_);
                    crate::leanh::lean_inc(v_env_2443_);
                    crate::leanh::lean_dec(v___x_2441_);
                    v___x_2452_ = crate::leanh::lean_box(0);
                    v_isShared_2453_ = v_isSharedCheck_2473_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_2454_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_2442_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_2471_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_2442_)) as u8;
                if v_isSharedCheck_2471_ == 0 {
                    v_unused_2472_ = crate::leanh::lean_ctor_get(v_traceState_2442_, 0);
                    crate::leanh::lean_dec(v_unused_2472_);
                    v___x_2456_ = v_traceState_2442_;
                    v_isShared_2457_ = v_isSharedCheck_2471_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_traceState_2442_);
                    v___x_2456_ = crate::leanh::lean_box(0);
                    v_isShared_2457_ = v_isSharedCheck_2471_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2458_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2458_, 0, v_ref_2403_);
                crate::leanh::lean_ctor_set(v___x_2458_, 1, v_a_2437_);
                v___x_2459_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2401_, v___x_2458_);
                if v_isShared_2457_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2456_, 0, v___x_2459_);
                    v___x_2461_ = v___x_2456_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2470_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2470_, 0, v___x_2459_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_2470_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_2454_,
                    );
                    v___x_2461_ = v_reuseFailAlloc_2470_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2453_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2452_, 4, v___x_2461_);
                    v___x_2463_ = v___x_2452_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2469_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2469_, 0, v_env_2443_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2469_, 1, v_nextMacroScope_2444_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2469_, 2, v_ngen_2445_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2469_, 3, v_auxDeclNGen_2446_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2469_, 4, v___x_2461_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2469_, 5, v_cache_2447_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2469_, 6, v_messages_2448_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2469_, 7, v_infoState_2449_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2469_, 8, v_snapshotTasks_2450_);
                    v___x_2463_ = v_reuseFailAlloc_2469_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2464_ = lean_st_ref_set(v___y_2408_, v___x_2463_);
                v___x_2465_ = crate::leanh::lean_box(0);
                if v_isShared_2440_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2439_, 0, v___x_2465_);
                    v___x_2467_ = v___x_2439_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2468_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2468_, 0, v___x_2465_);
                    v___x_2467_ = v_reuseFailAlloc_2468_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2467_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__3___redArg___boxed(
    mut v_oldTraces_2475_: *mut crate::leanh::LeanObject,
    mut v_data_2476_: *mut crate::leanh::LeanObject,
    mut v_ref_2477_: *mut crate::leanh::LeanObject,
    mut v_msg_2478_: *mut crate::leanh::LeanObject,
    mut v___y_2479_: *mut crate::leanh::LeanObject,
    mut v___y_2480_: *mut crate::leanh::LeanObject,
    mut v___y_2481_: *mut crate::leanh::LeanObject,
    mut v___y_2482_: *mut crate::leanh::LeanObject,
    mut v___y_2483_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2484_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__3___redArg(v_oldTraces_2475_, v_data_2476_, v_ref_2477_, v_msg_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_);
    crate::leanh::lean_dec(v___y_2482_);
    crate::leanh::lean_dec_ref(v___y_2481_);
    crate::leanh::lean_dec(v___y_2480_);
    crate::leanh::lean_dec_ref(v___y_2479_);
    return v_res_2484_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2486_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__0;
    v___x_2487_ = l_Lean_stringToMessageData(v___x_2486_);
    return v___x_2487_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2489_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__2;
    v___x_2490_ = l_Lean_stringToMessageData(v___x_2489_);
    return v___x_2490_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__4()
-> f64 {
    let mut v___x_2491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: f64 = 0.0;
    v___x_2491_ = crate::leanh::lean_unsigned_to_nat(1000);
    v___x_2492_ = lean_float_of_nat(v___x_2491_);
    return v___x_2492_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2(
    mut v_cls_2493_: *mut crate::leanh::LeanObject,
    mut v_collapsed_2494_: u8,
    mut v_tag_2495_: *mut crate::leanh::LeanObject,
    mut v_opts_2496_: *mut crate::leanh::LeanObject,
    mut v_clsEnabled_2497_: u8,
    mut v_oldTraces_2498_: *mut crate::leanh::LeanObject,
    mut v_msg_2499_: *mut crate::leanh::LeanObject,
    mut v_resStartStop_2500_: *mut crate::leanh::LeanObject,
    mut v___y_2501_: *mut crate::leanh::LeanObject,
    mut v___y_2502_: *mut crate::leanh::LeanObject,
    mut v___y_2503_: *mut crate::leanh::LeanObject,
    mut v___y_2504_: *mut crate::leanh::LeanObject,
    mut v___y_2505_: *mut crate::leanh::LeanObject,
    mut v___y_2506_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2512_: u8 = 0;
    let mut v___y_2514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2522_: u8 = 0;
    let mut v___x_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2526_: u8 = 0;
    let mut v_fst_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2531_: u8 = 0;
    let mut v___x_2532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: u8 = 0;
    let mut v___y_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_2537_: u8 = 0;
    let mut v___x_2538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: f64 = 0.0;
    let mut v_data_2548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_2549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: f64 = 0.0;
    let mut v___x_2551_: f64 = 0.0;
    let mut v_reuseFailAlloc_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2560_: u8 = 0;
    let mut v___x_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2573_: u8 = 0;
    let mut v_tid_2574_: u64 = 0;
    let mut v_traces_2575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2578_: u8 = 0;
    let mut v___x_2579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2588_: u8 = 0;
    let mut v_isSharedCheck_2589_: u8 = 0;
    let mut v___y_2591_: f64 = 0.0;
    let mut v___x_2592_: f64 = 0.0;
    let mut v___x_2593_: f64 = 0.0;
    let mut v___x_2594_: f64 = 0.0;
    let mut v___x_2595_: u8 = 0;
    let mut v___x_2596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: u8 = 0;
    let mut v___x_2598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2600_: f64 = 0.0;
    let mut v___x_2601_: f64 = 0.0;
    let mut v___x_2602_: f64 = 0.0;
    let mut v___x_2603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: f64 = 0.0;
    let mut v_isSharedCheck_2606_: u8 = 0;
    let mut v_isSharedCheck_2607_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2508_ = crate::leanh::lean_ctor_get(v_resStartStop_2500_, 0);
                v_snd_2509_ = crate::leanh::lean_ctor_get(v_resStartStop_2500_, 1);
                v_isSharedCheck_2607_ =
                    (!crate::leanh::lean_is_exclusive(v_resStartStop_2500_)) as u8;
                if v_isSharedCheck_2607_ == 0 {
                    v___x_2511_ = v_resStartStop_2500_;
                    v_isShared_2512_ = v_isSharedCheck_2607_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2509_);
                    crate::leanh::lean_inc(v_fst_2508_);
                    crate::leanh::lean_dec(v_resStartStop_2500_);
                    v___x_2511_ = crate::leanh::lean_box(0);
                    v_isShared_2512_ = v_isSharedCheck_2607_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_2527_ = crate::leanh::lean_ctor_get(v_snd_2509_, 0);
                v_snd_2528_ = crate::leanh::lean_ctor_get(v_snd_2509_, 1);
                v_isSharedCheck_2606_ = (!crate::leanh::lean_is_exclusive(v_snd_2509_)) as u8;
                if v_isSharedCheck_2606_ == 0 {
                    v___x_2530_ = v_snd_2509_;
                    v_isShared_2531_ = v_isSharedCheck_2606_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2528_);
                    crate::leanh::lean_inc(v_fst_2527_);
                    crate::leanh::lean_dec(v_snd_2509_);
                    v___x_2530_ = crate::leanh::lean_box(0);
                    v_isShared_2531_ = v_isSharedCheck_2606_;
                    state = 5;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v___y_2515_);
                v___x_2517_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__3___redArg(v_oldTraces_2498_, v_data_2516_, v___y_2515_, v___y_2514_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_);
                if crate::leanh::lean_obj_tag(v___x_2517_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_2517_, 1);
                    v___x_2518_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__4___redArg(v_fst_2508_);
                    return v___x_2518_;
                } else {
                    crate::leanh::lean_dec(v_fst_2508_);
                    v_a_2519_ = crate::leanh::lean_ctor_get(v___x_2517_, 0);
                    v_isSharedCheck_2526_ = (!crate::leanh::lean_is_exclusive(v___x_2517_)) as u8;
                    if v_isSharedCheck_2526_ == 0 {
                        v___x_2521_ = v___x_2517_;
                        v_isShared_2522_ = v_isSharedCheck_2526_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2519_);
                        crate::leanh::lean_dec(v___x_2517_);
                        v___x_2521_ = crate::leanh::lean_box(0);
                        v_isShared_2522_ = v_isSharedCheck_2526_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_2522_ == 0 {
                    v___x_2524_ = v___x_2521_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2525_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2525_, 0, v_a_2519_);
                    v___x_2524_ = v_reuseFailAlloc_2525_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2524_;
            }
            5 => {
                v___x_2532_ = l_Lean_trace_profiler;
                v___x_2533_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__1(v_opts_2496_, v___x_2532_);
                if v___x_2533_ == 0 {
                    v___y_2560_ = v___x_2533_;
                    state = 10;
                    continue;
                } else {
                    v___x_2596_ = l_Lean_trace_profiler_useHeartbeats;
                    v___x_2597_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__1(v_opts_2496_, v___x_2596_);
                    if v___x_2597_ == 0 {
                        v___x_2598_ = l_Lean_trace_profiler_threshold;
                        v___x_2599_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__5(v_opts_2496_, v___x_2598_);
                        v___x_2600_ = lean_float_of_nat(v___x_2599_);
                        v___x_2601_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__4_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__4);
                        v___x_2602_ = lean_float_div(v___x_2600_, v___x_2601_);
                        v___y_2591_ = v___x_2602_;
                        state = 15;
                        continue;
                    } else {
                        v___x_2603_ = l_Lean_trace_profiler_threshold;
                        v___x_2604_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__5(v_opts_2496_, v___x_2603_);
                        v___x_2605_ = lean_float_of_nat(v___x_2604_);
                        v___y_2591_ = v___x_2605_;
                        state = 15;
                        continue;
                    }
                }
            }
            6 => {
                v_result_2537_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__2(v_fst_2508_);
                v___x_2538_ = l_Lean_TraceResult_toEmoji(v_result_2537_);
                v___x_2539_ = l_Lean_stringToMessageData(v___x_2538_);
                v___x_2540_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__1_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__1);
                if v_isShared_2531_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2530_, 7);
                    crate::leanh::lean_ctor_set(v___x_2530_, 1, v___x_2540_);
                    crate::leanh::lean_ctor_set(v___x_2530_, 0, v___x_2539_);
                    v___x_2542_ = v___x_2530_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2553_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2553_, 0, v___x_2539_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2553_, 1, v___x_2540_);
                    v___x_2542_ = v_reuseFailAlloc_2553_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2512_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2511_, 7);
                    crate::leanh::lean_ctor_set(v___x_2511_, 1, v_a_2536_);
                    crate::leanh::lean_ctor_set(v___x_2511_, 0, v___x_2542_);
                    v_m_2544_ = v___x_2511_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2552_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2552_, 0, v___x_2542_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2552_, 1, v_a_2536_);
                    v_m_2544_ = v_reuseFailAlloc_2552_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2545_ = crate::leanh::lean_box((v_result_2537_) as usize);
                v___x_2546_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2546_, 0, v___x_2545_);
                v___x_2547_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__0_once), _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__0);
                crate::leanh::lean_inc_ref(v_tag_2495_);
                crate::leanh::lean_inc_ref(v___x_2546_);
                crate::leanh::lean_inc(v_cls_2493_);
                v_data_2548_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v_data_2548_, 0, v_cls_2493_);
                crate::leanh::lean_ctor_set(v_data_2548_, 1, v___x_2546_);
                crate::leanh::lean_ctor_set(v_data_2548_, 2, v_tag_2495_);
                crate::leanh::lean_ctor_set_float(
                    v_data_2548_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_2547_,
                );
                crate::leanh::lean_ctor_set_float(
                    v_data_2548_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_2547_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v_data_2548_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v_collapsed_2494_,
                );
                if v___x_2533_ == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_2546_, 1);
                    crate::leanh::lean_dec(v_snd_2528_);
                    crate::leanh::lean_dec(v_fst_2527_);
                    crate::leanh::lean_dec_ref(v_tag_2495_);
                    crate::leanh::lean_dec(v_cls_2493_);
                    v___y_2514_ = v_m_2544_;
                    v___y_2515_ = v___y_2535_;
                    v_data_2516_ = v_data_2548_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref_known(v_data_2548_, 3);
                    v_data_2549_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                    crate::leanh::lean_ctor_set(v_data_2549_, 0, v_cls_2493_);
                    crate::leanh::lean_ctor_set(v_data_2549_, 1, v___x_2546_);
                    crate::leanh::lean_ctor_set(v_data_2549_, 2, v_tag_2495_);
                    v___x_2550_ = crate::leanh::lean_unbox_float(v_fst_2527_);
                    crate::leanh::lean_dec(v_fst_2527_);
                    crate::leanh::lean_ctor_set_float(
                        v_data_2549_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v___x_2550_,
                    );
                    v___x_2551_ = crate::leanh::lean_unbox_float(v_snd_2528_);
                    crate::leanh::lean_dec(v_snd_2528_);
                    crate::leanh::lean_ctor_set_float(
                        v_data_2549_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                        v___x_2551_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_data_2549_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                        v_collapsed_2494_,
                    );
                    v___y_2514_ = v_m_2544_;
                    v___y_2515_ = v___y_2535_;
                    v_data_2516_ = v_data_2549_;
                    state = 2;
                    continue;
                }
            }
            9 => {
                v_ref_2555_ = crate::leanh::lean_ctor_get(v___y_2505_, 5);
                crate::leanh::lean_inc(v___y_2506_);
                crate::leanh::lean_inc_ref(v___y_2505_);
                crate::leanh::lean_inc(v___y_2504_);
                crate::leanh::lean_inc_ref(v___y_2503_);
                crate::leanh::lean_inc(v___y_2502_);
                crate::leanh::lean_inc_ref(v___y_2501_);
                crate::leanh::lean_inc(v_fst_2508_);
                v___x_2556_ = crate::leanh::lean_apply_8(
                    v_msg_2499_,
                    v_fst_2508_,
                    v___y_2501_,
                    v___y_2502_,
                    v___y_2503_,
                    v___y_2504_,
                    v___y_2505_,
                    v___y_2506_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_2556_) == 0 {
                    v_a_2557_ = crate::leanh::lean_ctor_get(v___x_2556_, 0);
                    crate::leanh::lean_inc(v_a_2557_);
                    crate::leanh::lean_dec_ref_known(v___x_2556_, 1);
                    v___y_2535_ = v_ref_2555_;
                    v_a_2536_ = v_a_2557_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_2556_, 1);
                    v___x_2558_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__3_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__3);
                    v___y_2535_ = v_ref_2555_;
                    v_a_2536_ = v___x_2558_;
                    state = 6;
                    continue;
                }
            }
            10 => {
                if v_clsEnabled_2497_ == 0 {
                    if v___y_2560_ == 0 {
                        crate::leanh::lean_del_object(v___x_2530_);
                        crate::leanh::lean_dec(v_snd_2528_);
                        crate::leanh::lean_dec(v_fst_2527_);
                        crate::leanh::lean_del_object(v___x_2511_);
                        crate::leanh::lean_dec_ref(v_msg_2499_);
                        crate::leanh::lean_dec_ref(v_tag_2495_);
                        crate::leanh::lean_dec(v_cls_2493_);
                        v___x_2561_ = lean_st_ref_take(v___y_2506_);
                        v_traceState_2562_ = crate::leanh::lean_ctor_get(v___x_2561_, 4);
                        v_env_2563_ = crate::leanh::lean_ctor_get(v___x_2561_, 0);
                        v_nextMacroScope_2564_ = crate::leanh::lean_ctor_get(v___x_2561_, 1);
                        v_ngen_2565_ = crate::leanh::lean_ctor_get(v___x_2561_, 2);
                        v_auxDeclNGen_2566_ = crate::leanh::lean_ctor_get(v___x_2561_, 3);
                        v_cache_2567_ = crate::leanh::lean_ctor_get(v___x_2561_, 5);
                        v_messages_2568_ = crate::leanh::lean_ctor_get(v___x_2561_, 6);
                        v_infoState_2569_ = crate::leanh::lean_ctor_get(v___x_2561_, 7);
                        v_snapshotTasks_2570_ = crate::leanh::lean_ctor_get(v___x_2561_, 8);
                        v_isSharedCheck_2589_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2561_)) as u8;
                        if v_isSharedCheck_2589_ == 0 {
                            v___x_2572_ = v___x_2561_;
                            v_isShared_2573_ = v_isSharedCheck_2589_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snapshotTasks_2570_);
                            crate::leanh::lean_inc(v_infoState_2569_);
                            crate::leanh::lean_inc(v_messages_2568_);
                            crate::leanh::lean_inc(v_cache_2567_);
                            crate::leanh::lean_inc(v_traceState_2562_);
                            crate::leanh::lean_inc(v_auxDeclNGen_2566_);
                            crate::leanh::lean_inc(v_ngen_2565_);
                            crate::leanh::lean_inc(v_nextMacroScope_2564_);
                            crate::leanh::lean_inc(v_env_2563_);
                            crate::leanh::lean_dec(v___x_2561_);
                            v___x_2572_ = crate::leanh::lean_box(0);
                            v_isShared_2573_ = v_isSharedCheck_2589_;
                            state = 11;
                            continue;
                        }
                    } else {
                        state = 9;
                        continue;
                    }
                } else {
                    state = 9;
                    continue;
                }
            }
            11 => {
                v_tid_2574_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_2562_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_2575_ = crate::leanh::lean_ctor_get(v_traceState_2562_, 0);
                v_isSharedCheck_2588_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_2562_)) as u8;
                if v_isSharedCheck_2588_ == 0 {
                    v___x_2577_ = v_traceState_2562_;
                    v_isShared_2578_ = v_isSharedCheck_2588_;
                    state = 12;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_2575_);
                    crate::leanh::lean_dec(v_traceState_2562_);
                    v___x_2577_ = crate::leanh::lean_box(0);
                    v_isShared_2578_ = v_isSharedCheck_2588_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_2579_ =
                    l_Lean_PersistentArray_append___redArg(v_oldTraces_2498_, v_traces_2575_);
                crate::leanh::lean_dec_ref(v_traces_2575_);
                if v_isShared_2578_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2577_, 0, v___x_2579_);
                    v___x_2581_ = v___x_2577_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2587_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2587_, 0, v___x_2579_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_2587_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_2574_,
                    );
                    v___x_2581_ = v_reuseFailAlloc_2587_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_2573_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2572_, 4, v___x_2581_);
                    v___x_2583_ = v___x_2572_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2586_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2586_, 0, v_env_2563_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2586_, 1, v_nextMacroScope_2564_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2586_, 2, v_ngen_2565_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2586_, 3, v_auxDeclNGen_2566_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2586_, 4, v___x_2581_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2586_, 5, v_cache_2567_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2586_, 6, v_messages_2568_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2586_, 7, v_infoState_2569_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2586_, 8, v_snapshotTasks_2570_);
                    v___x_2583_ = v_reuseFailAlloc_2586_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_2584_ = lean_st_ref_set(v___y_2506_, v___x_2583_);
                v___x_2585_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__4___redArg(v_fst_2508_);
                return v___x_2585_;
            }
            15 => {
                v___x_2592_ = crate::leanh::lean_unbox_float(v_snd_2528_);
                v___x_2593_ = crate::leanh::lean_unbox_float(v_fst_2527_);
                v___x_2594_ = lean_float_sub(v___x_2592_, v___x_2593_);
                v___x_2595_ = lean_float_decLt(v___y_2591_, v___x_2594_);
                v___y_2560_ = v___x_2595_;
                state = 10;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___boxed(
    mut v_cls_2608_: *mut crate::leanh::LeanObject,
    mut v_collapsed_2609_: *mut crate::leanh::LeanObject,
    mut v_tag_2610_: *mut crate::leanh::LeanObject,
    mut v_opts_2611_: *mut crate::leanh::LeanObject,
    mut v_clsEnabled_2612_: *mut crate::leanh::LeanObject,
    mut v_oldTraces_2613_: *mut crate::leanh::LeanObject,
    mut v_msg_2614_: *mut crate::leanh::LeanObject,
    mut v_resStartStop_2615_: *mut crate::leanh::LeanObject,
    mut v___y_2616_: *mut crate::leanh::LeanObject,
    mut v___y_2617_: *mut crate::leanh::LeanObject,
    mut v___y_2618_: *mut crate::leanh::LeanObject,
    mut v___y_2619_: *mut crate::leanh::LeanObject,
    mut v___y_2620_: *mut crate::leanh::LeanObject,
    mut v___y_2621_: *mut crate::leanh::LeanObject,
    mut v___y_2622_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_collapsed_boxed_2623_: u8 = 0;
    let mut v_clsEnabled_boxed_2624_: u8 = 0;
    let mut v_res_2625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_2623_ = (crate::leanh::lean_unbox(v_collapsed_2609_) as u8);
    v_clsEnabled_boxed_2624_ = (crate::leanh::lean_unbox(v_clsEnabled_2612_) as u8);
    v_res_2625_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2(v_cls_2608_, v_collapsed_boxed_2623_, v_tag_2610_, v_opts_2611_, v_clsEnabled_boxed_2624_, v_oldTraces_2613_, v_msg_2614_, v_resStartStop_2615_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_);
    crate::leanh::lean_dec(v___y_2621_);
    crate::leanh::lean_dec_ref(v___y_2620_);
    crate::leanh::lean_dec(v___y_2619_);
    crate::leanh::lean_dec_ref(v___y_2618_);
    crate::leanh::lean_dec(v___y_2617_);
    crate::leanh::lean_dec_ref(v___y_2616_);
    crate::leanh::lean_dec_ref(v_opts_2611_);
    return v_res_2625_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__4()
-> f64 {
    let mut v___x_2633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: f64 = 0.0;
    v___x_2633_ = crate::leanh::lean_unsigned_to_nat(1000000000);
    v___x_2634_ = lean_float_of_nat(v___x_2633_);
    return v___x_2634_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2638_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__3;
    v___x_2639_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__6;
    v___x_2640_ = l_Lean_Name_append(v___x_2639_, v___x_2638_);
    return v___x_2640_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2642_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__8;
    v___x_2643_ = l_Lean_stringToMessageData(v___x_2642_);
    return v___x_2643_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2645_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__10;
    v___x_2646_ = l_Lean_stringToMessageData(v___x_2645_);
    return v___x_2646_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go(
    mut v_g_2647_: *mut crate::leanh::LeanObject,
    mut v_a_2648_: *mut crate::leanh::LeanObject,
    mut v_a_2649_: *mut crate::leanh::LeanObject,
    mut v_a_2650_: *mut crate::leanh::LeanObject,
    mut v_a_2651_: *mut crate::leanh::LeanObject,
    mut v_a_2652_: *mut crate::leanh::LeanObject,
    mut v_a_2653_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2660_: u8 = 0;
    let mut v_options_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2665_: u8 = 0;
    let mut v_inheritedTraceOptions_2666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_2667_: u8 = 0;
    let mut v___x_2668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2671_: u8 = 0;
    let mut v___y_2672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2682_: u8 = 0;
    let mut v_a_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: f64 = 0.0;
    let mut v___x_2686_: f64 = 0.0;
    let mut v___x_2687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2694_: u8 = 0;
    let mut v___y_2695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2705_: u8 = 0;
    let mut v_a_2706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: f64 = 0.0;
    let mut v___x_2709_: f64 = 0.0;
    let mut v___x_2710_: f64 = 0.0;
    let mut v___x_2711_: f64 = 0.0;
    let mut v___x_2712_: f64 = 0.0;
    let mut v___x_2713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2720_: u8 = 0;
    let mut v___y_2721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2731_: u8 = 0;
    let mut v___x_2732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: u8 = 0;
    let mut v___x_2736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2741_: u8 = 0;
    let mut v___x_2743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2745_: u8 = 0;
    let mut v_a_2746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2749_: u8 = 0;
    let mut v___x_2751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2753_: u8 = 0;
    let mut v___x_2754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2759_: u8 = 0;
    let mut v___x_2761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2763_: u8 = 0;
    let mut v_a_2764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2767_: u8 = 0;
    let mut v___x_2769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2771_: u8 = 0;
    let mut v___y_2773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_shortCircuit_2785_: u8 = 0;
    let mut v_val_2786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_2789_: u8 = 0;
    let mut v_run_x27_2790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_run_x27_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_2793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: u8 = 0;
    let mut v___x_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: u8 = 0;
    let mut v___x_2800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2803_: u8 = 0;
    let mut v___x_2805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2807_: u8 = 0;
    let mut v_unused_2808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_g_2811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_2819_: u8 = 0;
    let mut v_inheritedTraceOptions_2820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2822_: u8 = 0;
    let mut v___x_2823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2831_: u8 = 0;
    let mut v___x_2833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2835_: u8 = 0;
    let mut v_reuseFailAlloc_2836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2849_: u8 = 0;
    let mut v_val_2850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2854_: u8 = 0;
    let mut v___y_2856_: u8 = 0;
    let mut v___y_2857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2860_: u8 = 0;
    let mut v___y_2861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: f64 = 0.0;
    let mut v___x_2873_: f64 = 0.0;
    let mut v___x_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2880_: u8 = 0;
    let mut v___y_2881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2885_: u8 = 0;
    let mut v___y_2886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: f64 = 0.0;
    let mut v___x_2897_: f64 = 0.0;
    let mut v___x_2898_: f64 = 0.0;
    let mut v___x_2899_: f64 = 0.0;
    let mut v___x_2900_: f64 = 0.0;
    let mut v___x_2901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2907_: u8 = 0;
    let mut v___y_2908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2913_: u8 = 0;
    let mut v___y_2914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: u8 = 0;
    let mut v___x_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2930_: u8 = 0;
    let mut v___x_2932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2934_: u8 = 0;
    let mut v_a_2935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2938_: u8 = 0;
    let mut v___x_2940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2942_: u8 = 0;
    let mut v___x_2943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2948_: u8 = 0;
    let mut v___x_2950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2952_: u8 = 0;
    let mut v_a_2953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2956_: u8 = 0;
    let mut v___x_2958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2960_: u8 = 0;
    let mut v___y_2962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fixedInt_2963_: u8 = 0;
    let mut v_g_2964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_2973_: u8 = 0;
    let mut v_run_x27_2974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_run_x27_2976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_2977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: u8 = 0;
    let mut v___x_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: u8 = 0;
    let mut v___x_2984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2997_: u8 = 0;
    let mut v_val_2998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fixedInt_2999_: u8 = 0;
    let mut v___x_3001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3003_: u8 = 0;
    let mut v___y_3005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3006_: u8 = 0;
    let mut v___y_3007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3018_: u8 = 0;
    let mut v_a_3019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: f64 = 0.0;
    let mut v___x_3022_: f64 = 0.0;
    let mut v___x_3023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3030_: u8 = 0;
    let mut v___y_3031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3042_: u8 = 0;
    let mut v_a_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: f64 = 0.0;
    let mut v___x_3046_: f64 = 0.0;
    let mut v___x_3047_: f64 = 0.0;
    let mut v___x_3048_: f64 = 0.0;
    let mut v___x_3049_: f64 = 0.0;
    let mut v___x_3050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3058_: u8 = 0;
    let mut v___y_3059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3068_: u8 = 0;
    let mut v___y_3069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: u8 = 0;
    let mut v___x_3074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3079_: u8 = 0;
    let mut v___x_3081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3083_: u8 = 0;
    let mut v_a_3084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3087_: u8 = 0;
    let mut v___x_3089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3091_: u8 = 0;
    let mut v___x_3092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3097_: u8 = 0;
    let mut v___x_3099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3101_: u8 = 0;
    let mut v_a_3102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3105_: u8 = 0;
    let mut v___x_3107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3109_: u8 = 0;
    let mut v___y_3111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fixedInt_3112_: u8 = 0;
    let mut v_enums_3113_: u8 = 0;
    let mut v_g_3114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3123_: u8 = 0;
    let mut v_run_x27_3124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_run_x27_3126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_3127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: u8 = 0;
    let mut v___x_3132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: u8 = 0;
    let mut v___x_3134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3147_: u8 = 0;
    let mut v_val_3148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fixedInt_3149_: u8 = 0;
    let mut v_enums_3150_: u8 = 0;
    let mut v___x_3152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3154_: u8 = 0;
    let mut v___y_3156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3158_: u8 = 0;
    let mut v___y_3159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3166_: u8 = 0;
    let mut v___y_3167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: f64 = 0.0;
    let mut v___x_3173_: f64 = 0.0;
    let mut v___x_3174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3182_: u8 = 0;
    let mut v___y_3183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3190_: u8 = 0;
    let mut v___y_3191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3196_: f64 = 0.0;
    let mut v___x_3197_: f64 = 0.0;
    let mut v___x_3198_: f64 = 0.0;
    let mut v___x_3199_: f64 = 0.0;
    let mut v___x_3200_: f64 = 0.0;
    let mut v___x_3201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3211_: u8 = 0;
    let mut v___y_3212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3220_: u8 = 0;
    let mut v___x_3221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: u8 = 0;
    let mut v___x_3225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3230_: u8 = 0;
    let mut v___x_3232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3234_: u8 = 0;
    let mut v_a_3235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3238_: u8 = 0;
    let mut v___x_3240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3242_: u8 = 0;
    let mut v___x_3243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3248_: u8 = 0;
    let mut v___x_3250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3252_: u8 = 0;
    let mut v_a_3253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3256_: u8 = 0;
    let mut v___x_3258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3260_: u8 = 0;
    let mut v___y_3262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3272_: u8 = 0;
    let mut v_structures_3273_: u8 = 0;
    let mut v_val_3274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fixedInt_3275_: u8 = 0;
    let mut v_enums_3276_: u8 = 0;
    let mut v_val_3277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3280_: u8 = 0;
    let mut v_run_x27_3281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_run_x27_3283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_3284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: u8 = 0;
    let mut v___x_3289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: u8 = 0;
    let mut v___x_3291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3295_: u8 = 0;
    let mut v___y_3297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3305_: u8 = 0;
    let mut v___y_3306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3308_: u8 = 0;
    let mut v___y_3309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: f64 = 0.0;
    let mut v___x_3313_: f64 = 0.0;
    let mut v___x_3314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3328_: u8 = 0;
    let mut v___y_3329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3331_: u8 = 0;
    let mut v___y_3332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: f64 = 0.0;
    let mut v___x_3336_: f64 = 0.0;
    let mut v___x_3337_: f64 = 0.0;
    let mut v___x_3338_: f64 = 0.0;
    let mut v___x_3339_: f64 = 0.0;
    let mut v___x_3340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3352_: u8 = 0;
    let mut v___y_3353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3356_: u8 = 0;
    let mut v___y_3357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3361_: u8 = 0;
    let mut v___x_3362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3367_: u8 = 0;
    let mut v___x_3369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3371_: u8 = 0;
    let mut v_a_3372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3375_: u8 = 0;
    let mut v___x_3377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3379_: u8 = 0;
    let mut v___x_3380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3385_: u8 = 0;
    let mut v___x_3387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3389_: u8 = 0;
    let mut v_a_3390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3393_: u8 = 0;
    let mut v___x_3395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3397_: u8 = 0;
    let mut v___y_3399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3407_: u8 = 0;
    let mut v_run_x27_3408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_run_x27_3410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_3411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3415_: u8 = 0;
    let mut v___x_3416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3417_: u8 = 0;
    let mut v___x_3418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_structures_3426_: u8 = 0;
    let mut v_enums_3427_: u8 = 0;
    let mut v_fixedInt_3428_: u8 = 0;
    let mut v___x_3429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: u8 = 0;
    let mut v___x_3431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3438_: u8 = 0;
    let mut v___x_3440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3442_: u8 = 0;
    let mut v_isSharedCheck_3443_: u8 = 0;
    let mut v___x_3445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3447_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2655_ = crate::leanh::lean_box(0);
                v___x_2656_ = l_Lean_MVarId_falseOrByContra(
                    v_g_2647_,
                    v___x_2655_,
                    v_a_2650_,
                    v_a_2651_,
                    v_a_2652_,
                    v_a_2653_,
                );
                if crate::leanh::lean_obj_tag(v___x_2656_) == 0 {
                    v_a_2657_ = crate::leanh::lean_ctor_get(v___x_2656_, 0);
                    v_isSharedCheck_3447_ = (!crate::leanh::lean_is_exclusive(v___x_2656_)) as u8;
                    if v_isSharedCheck_3447_ == 0 {
                        v___x_2659_ = v___x_2656_;
                        v_isShared_2660_ = v_isSharedCheck_3447_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2657_);
                        crate::leanh::lean_dec(v___x_2656_);
                        v___x_2659_ = crate::leanh::lean_box(0);
                        v_isShared_2660_ = v_isSharedCheck_3447_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_2656_;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_2657_) == 1 {
                    crate::leanh::lean_del_object(v___x_2659_);
                    v_options_2661_ = crate::leanh::lean_ctor_get(v_a_2652_, 2);
                    v_val_2662_ = crate::leanh::lean_ctor_get(v_a_2657_, 0);
                    v_isSharedCheck_3443_ = (!crate::leanh::lean_is_exclusive(v_a_2657_)) as u8;
                    if v_isSharedCheck_3443_ == 0 {
                        v___x_2664_ = v_a_2657_;
                        v_isShared_2665_ = v_isSharedCheck_3443_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2662_);
                        crate::leanh::lean_dec(v_a_2657_);
                        v___x_2664_ = crate::leanh::lean_box(0);
                        v_isShared_2665_ = v_isSharedCheck_3443_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2657_);
                    if v_isShared_2660_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2659_, 0, v___x_2655_);
                        v___x_3445_ = v___x_2659_;
                        state = 83;
                        continue;
                    } else {
                        v_reuseFailAlloc_3446_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3446_, 0, v___x_2655_);
                        v___x_3445_ = v_reuseFailAlloc_3446_;
                        state = 83;
                        continue;
                    }
                }
            }
            2 => {
                v_inheritedTraceOptions_2666_ = crate::leanh::lean_ctor_get(v_a_2652_, 13);
                v_hasTrace_2667_ = crate::leanh::lean_ctor_get_uint8(
                    v_options_2661_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v___x_2668_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__3;
                if v_hasTrace_2667_ == 0 {
                    v___y_3420_ = v_a_2648_;
                    v___y_3421_ = v_a_2649_;
                    v___y_3422_ = v_a_2650_;
                    v___y_3423_ = v_a_2651_;
                    v___y_3424_ = v_a_2652_;
                    v___y_3425_ = v_a_2653_;
                    state = 80;
                    continue;
                } else {
                    v___x_3429_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7);
                    v___x_3430_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_2666_,
                        v_options_2661_,
                        v___x_3429_,
                    );
                    if v___x_3430_ == 0 {
                        v___y_3420_ = v_a_2648_;
                        v___y_3421_ = v_a_2649_;
                        v___y_3422_ = v_a_2650_;
                        v___y_3423_ = v_a_2651_;
                        v___y_3424_ = v_a_2652_;
                        v___y_3425_ = v_a_2653_;
                        state = 80;
                        continue;
                    } else {
                        v___x_3431_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__11_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__11);
                        crate::leanh::lean_inc(v_val_2662_);
                        v___x_3432_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3432_, 0, v_val_2662_);
                        v___x_3433_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3433_, 0, v___x_3431_);
                        crate::leanh::lean_ctor_set(v___x_3433_, 1, v___x_3432_);
                        v___x_3434_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg(v___x_2668_, v___x_3433_, v_a_2650_, v_a_2651_, v_a_2652_, v_a_2653_);
                        if crate::leanh::lean_obj_tag(v___x_3434_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_3434_, 1);
                            v___y_3420_ = v_a_2648_;
                            v___y_3421_ = v_a_2649_;
                            v___y_3422_ = v_a_2650_;
                            v___y_3423_ = v_a_2651_;
                            v___y_3424_ = v_a_2652_;
                            v___y_3425_ = v_a_2653_;
                            state = 80;
                            continue;
                        } else {
                            crate::leanh::lean_del_object(v___x_2664_);
                            crate::leanh::lean_dec(v_val_2662_);
                            v_a_3435_ = crate::leanh::lean_ctor_get(v___x_3434_, 0);
                            v_isSharedCheck_3442_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3434_)) as u8;
                            if v_isSharedCheck_3442_ == 0 {
                                v___x_3437_ = v___x_3434_;
                                v_isShared_3438_ = v_isSharedCheck_3442_;
                                state = 81;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3435_);
                                crate::leanh::lean_dec(v___x_3434_);
                                v___x_3437_ = crate::leanh::lean_box(0);
                                v_isShared_3438_ = v_isSharedCheck_3442_;
                                state = 81;
                                continue;
                            }
                        }
                    }
                }
            }
            3 => {
                v___x_2684_ = lean_io_get_num_heartbeats();
                v___x_2685_ = lean_float_of_nat(v___y_2672_);
                v___x_2686_ = lean_float_of_nat(v___x_2684_);
                v___x_2687_ = crate::leanh::lean_box_float(v___x_2685_);
                v___x_2688_ = crate::leanh::lean_box_float(v___x_2686_);
                v___x_2689_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2689_, 0, v___x_2687_);
                crate::leanh::lean_ctor_set(v___x_2689_, 1, v___x_2688_);
                v___x_2690_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2690_, 0, v_a_2683_);
                crate::leanh::lean_ctor_set(v___x_2690_, 1, v___x_2689_);
                crate::leanh::lean_inc_ref(v___y_2677_);
                v___x_2691_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2(v___x_2668_, v___y_2682_, v___y_2677_, v___y_2678_, v___y_2671_, v___y_2676_, v___y_2679_, v___x_2690_, v___y_2670_, v___y_2675_, v___y_2680_, v___y_2673_, v___y_2674_, v___y_2681_);
                return v___x_2691_;
            }
            4 => {
                v___x_2707_ = lean_io_mono_nanos_now();
                v___x_2708_ = lean_float_of_nat(v___y_2696_);
                v___x_2709_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__4_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__4);
                v___x_2710_ = lean_float_div(v___x_2708_, v___x_2709_);
                v___x_2711_ = lean_float_of_nat(v___x_2707_);
                v___x_2712_ = lean_float_div(v___x_2711_, v___x_2709_);
                v___x_2713_ = crate::leanh::lean_box_float(v___x_2710_);
                v___x_2714_ = crate::leanh::lean_box_float(v___x_2712_);
                v___x_2715_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2715_, 0, v___x_2713_);
                crate::leanh::lean_ctor_set(v___x_2715_, 1, v___x_2714_);
                v___x_2716_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2716_, 0, v_a_2706_);
                crate::leanh::lean_ctor_set(v___x_2716_, 1, v___x_2715_);
                crate::leanh::lean_inc_ref(v___y_2700_);
                v___x_2717_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2(v___x_2668_, v___y_2705_, v___y_2700_, v___y_2701_, v___y_2694_, v___y_2699_, v___y_2702_, v___x_2716_, v___y_2693_, v___y_2698_, v___y_2703_, v___y_2695_, v___y_2697_, v___y_2704_);
                return v___x_2717_;
            }
            5 => {
                v___x_2732_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___redArg(v___y_2730_);
                v_a_2733_ = crate::leanh::lean_ctor_get(v___x_2732_, 0);
                crate::leanh::lean_inc(v_a_2733_);
                crate::leanh::lean_dec_ref(v___x_2732_);
                v___x_2734_ = l_Lean_trace_profiler_useHeartbeats;
                v___x_2735_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__1(v___y_2727_, v___x_2734_);
                if v___x_2735_ == 0 {
                    v___x_2736_ = lean_io_mono_nanos_now();
                    crate::leanh::lean_inc(v___y_2730_);
                    crate::leanh::lean_inc_ref(v___y_2724_);
                    crate::leanh::lean_inc(v___y_2721_);
                    crate::leanh::lean_inc_ref(v___y_2729_);
                    crate::leanh::lean_inc(v___y_2725_);
                    crate::leanh::lean_inc_ref(v___y_2719_);
                    v___x_2737_ = crate::leanh::lean_apply_8(
                        v___y_2722_,
                        v___y_2723_,
                        v___y_2719_,
                        v___y_2725_,
                        v___y_2729_,
                        v___y_2721_,
                        v___y_2724_,
                        v___y_2730_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_2737_) == 0 {
                        v_a_2738_ = crate::leanh::lean_ctor_get(v___x_2737_, 0);
                        v_isSharedCheck_2745_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2737_)) as u8;
                        if v_isSharedCheck_2745_ == 0 {
                            v___x_2740_ = v___x_2737_;
                            v_isShared_2741_ = v_isSharedCheck_2745_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2738_);
                            crate::leanh::lean_dec(v___x_2737_);
                            v___x_2740_ = crate::leanh::lean_box(0);
                            v_isShared_2741_ = v_isSharedCheck_2745_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_2746_ = crate::leanh::lean_ctor_get(v___x_2737_, 0);
                        v_isSharedCheck_2753_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2737_)) as u8;
                        if v_isSharedCheck_2753_ == 0 {
                            v___x_2748_ = v___x_2737_;
                            v_isShared_2749_ = v_isSharedCheck_2753_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2746_);
                            crate::leanh::lean_dec(v___x_2737_);
                            v___x_2748_ = crate::leanh::lean_box(0);
                            v_isShared_2749_ = v_isSharedCheck_2753_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    v___x_2754_ = lean_io_get_num_heartbeats();
                    crate::leanh::lean_inc(v___y_2730_);
                    crate::leanh::lean_inc_ref(v___y_2724_);
                    crate::leanh::lean_inc(v___y_2721_);
                    crate::leanh::lean_inc_ref(v___y_2729_);
                    crate::leanh::lean_inc(v___y_2725_);
                    crate::leanh::lean_inc_ref(v___y_2719_);
                    v___x_2755_ = crate::leanh::lean_apply_8(
                        v___y_2722_,
                        v___y_2723_,
                        v___y_2719_,
                        v___y_2725_,
                        v___y_2729_,
                        v___y_2721_,
                        v___y_2724_,
                        v___y_2730_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_2755_) == 0 {
                        v_a_2756_ = crate::leanh::lean_ctor_get(v___x_2755_, 0);
                        v_isSharedCheck_2763_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2755_)) as u8;
                        if v_isSharedCheck_2763_ == 0 {
                            v___x_2758_ = v___x_2755_;
                            v_isShared_2759_ = v_isSharedCheck_2763_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2756_);
                            crate::leanh::lean_dec(v___x_2755_);
                            v___x_2758_ = crate::leanh::lean_box(0);
                            v_isShared_2759_ = v_isSharedCheck_2763_;
                            state = 10;
                            continue;
                        }
                    } else {
                        v_a_2764_ = crate::leanh::lean_ctor_get(v___x_2755_, 0);
                        v_isSharedCheck_2771_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2755_)) as u8;
                        if v_isSharedCheck_2771_ == 0 {
                            v___x_2766_ = v___x_2755_;
                            v_isShared_2767_ = v_isSharedCheck_2771_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2764_);
                            crate::leanh::lean_dec(v___x_2755_);
                            v___x_2766_ = crate::leanh::lean_box(0);
                            v_isShared_2767_ = v_isSharedCheck_2771_;
                            state = 12;
                            continue;
                        }
                    }
                }
            }
            6 => {
                if v_isShared_2741_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2740_, 1);
                    v___x_2743_ = v___x_2740_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2744_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2744_, 0, v_a_2738_);
                    v___x_2743_ = v_reuseFailAlloc_2744_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_2693_ = v___y_2719_;
                v___y_2694_ = v___y_2720_;
                v___y_2695_ = v___y_2721_;
                v___y_2696_ = v___x_2736_;
                v___y_2697_ = v___y_2724_;
                v___y_2698_ = v___y_2725_;
                v___y_2699_ = v_a_2733_;
                v___y_2700_ = v___y_2726_;
                v___y_2701_ = v___y_2727_;
                v___y_2702_ = v___y_2728_;
                v___y_2703_ = v___y_2729_;
                v___y_2704_ = v___y_2730_;
                v___y_2705_ = v___y_2731_;
                v_a_2706_ = v___x_2743_;
                state = 4;
                continue;
            }
            8 => {
                if v_isShared_2749_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2748_, 0);
                    v___x_2751_ = v___x_2748_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2752_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2752_, 0, v_a_2746_);
                    v___x_2751_ = v_reuseFailAlloc_2752_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___y_2693_ = v___y_2719_;
                v___y_2694_ = v___y_2720_;
                v___y_2695_ = v___y_2721_;
                v___y_2696_ = v___x_2736_;
                v___y_2697_ = v___y_2724_;
                v___y_2698_ = v___y_2725_;
                v___y_2699_ = v_a_2733_;
                v___y_2700_ = v___y_2726_;
                v___y_2701_ = v___y_2727_;
                v___y_2702_ = v___y_2728_;
                v___y_2703_ = v___y_2729_;
                v___y_2704_ = v___y_2730_;
                v___y_2705_ = v___y_2731_;
                v_a_2706_ = v___x_2751_;
                state = 4;
                continue;
            }
            10 => {
                if v_isShared_2759_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2758_, 1);
                    v___x_2761_ = v___x_2758_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2762_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2762_, 0, v_a_2756_);
                    v___x_2761_ = v_reuseFailAlloc_2762_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___y_2670_ = v___y_2719_;
                v___y_2671_ = v___y_2720_;
                v___y_2672_ = v___x_2754_;
                v___y_2673_ = v___y_2721_;
                v___y_2674_ = v___y_2724_;
                v___y_2675_ = v___y_2725_;
                v___y_2676_ = v_a_2733_;
                v___y_2677_ = v___y_2726_;
                v___y_2678_ = v___y_2727_;
                v___y_2679_ = v___y_2728_;
                v___y_2680_ = v___y_2729_;
                v___y_2681_ = v___y_2730_;
                v___y_2682_ = v___y_2731_;
                v_a_2683_ = v___x_2761_;
                state = 3;
                continue;
            }
            12 => {
                if v_isShared_2767_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2766_, 0);
                    v___x_2769_ = v___x_2766_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2770_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2770_, 0, v_a_2764_);
                    v___x_2769_ = v_reuseFailAlloc_2770_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___y_2670_ = v___y_2719_;
                v___y_2671_ = v___y_2720_;
                v___y_2672_ = v___x_2754_;
                v___y_2673_ = v___y_2721_;
                v___y_2674_ = v___y_2724_;
                v___y_2675_ = v___y_2725_;
                v___y_2676_ = v_a_2733_;
                v___y_2677_ = v___y_2726_;
                v___y_2678_ = v___y_2727_;
                v___y_2679_ = v___y_2728_;
                v___y_2680_ = v___y_2729_;
                v___y_2681_ = v___y_2730_;
                v___y_2682_ = v___y_2731_;
                v_a_2683_ = v___x_2769_;
                state = 3;
                continue;
            }
            14 => {
                v___x_2781_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg(v___y_2775_);
                v_a_2782_ = crate::leanh::lean_ctor_get(v___x_2781_, 0);
                crate::leanh::lean_inc(v_a_2782_);
                crate::leanh::lean_dec_ref(v___x_2781_);
                v___x_2783_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline(
                    v_a_2782_,
                    v___y_2773_,
                    v___y_2775_,
                    v___y_2776_,
                    v___y_2777_,
                    v___y_2778_,
                    v___y_2779_,
                    v___y_2780_,
                );
                crate::leanh::lean_dec(v_a_2782_);
                if crate::leanh::lean_obj_tag(v___x_2783_) == 0 {
                    v_a_2784_ = crate::leanh::lean_ctor_get(v___x_2783_, 0);
                    crate::leanh::lean_inc(v_a_2784_);
                    if crate::leanh::lean_obj_tag(v_a_2784_) == 1 {
                        v_shortCircuit_2785_ = crate::leanh::lean_ctor_get_uint8(
                            v___y_2774_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 9) as u32,
                        );
                        if v_shortCircuit_2785_ == 0 {
                            crate::leanh::lean_dec_ref_known(v_a_2784_, 1);
                            return v___x_2783_;
                        } else {
                            crate::leanh::lean_dec_ref_known(v___x_2783_, 1);
                            v_val_2786_ = crate::leanh::lean_ctor_get(v_a_2784_, 0);
                            crate::leanh::lean_inc(v_val_2786_);
                            crate::leanh::lean_dec_ref_known(v_a_2784_, 1);
                            v___x_2787_ = l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass;
                            v_options_2788_ = crate::leanh::lean_ctor_get(v___y_2779_, 2);
                            v_hasTrace_2789_ = crate::leanh::lean_ctor_get_uint8(
                                v_options_2788_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            );
                            if v_hasTrace_2789_ == 0 {
                                v_run_x27_2790_ = crate::leanh::lean_ctor_get(v___x_2787_, 1);
                                crate::leanh::lean_inc_ref(v_run_x27_2790_);
                                crate::leanh::lean_inc(v___y_2780_);
                                crate::leanh::lean_inc_ref(v___y_2779_);
                                crate::leanh::lean_inc(v___y_2778_);
                                crate::leanh::lean_inc_ref(v___y_2777_);
                                crate::leanh::lean_inc(v___y_2776_);
                                crate::leanh::lean_inc_ref(v___y_2775_);
                                v___x_2791_ = crate::leanh::lean_apply_8(
                                    v_run_x27_2790_,
                                    v_val_2786_,
                                    v___y_2775_,
                                    v___y_2776_,
                                    v___y_2777_,
                                    v___y_2778_,
                                    v___y_2779_,
                                    v___y_2780_,
                                    crate::leanh::lean_box(0),
                                );
                                return v___x_2791_;
                            } else {
                                v_run_x27_2792_ = crate::leanh::lean_ctor_get(v___x_2787_, 1);
                                v_inheritedTraceOptions_2793_ =
                                    crate::leanh::lean_ctor_get(v___y_2779_, 13);
                                crate::leanh::lean_inc(v_val_2786_);
                                v___f_2794_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___boxed as *mut core::ffi::c_void, 10, 2);
                                crate::leanh::lean_closure_set(v___f_2794_, 0, v___x_2787_);
                                crate::leanh::lean_closure_set(v___f_2794_, 1, v_val_2786_);
                                v___x_2795_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__1;
                                v___x_2796_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7);
                                v___x_2797_ =
                                    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                        v_inheritedTraceOptions_2793_,
                                        v_options_2788_,
                                        v___x_2796_,
                                    );
                                if v___x_2797_ == 0 {
                                    v___x_2798_ = l_Lean_trace_profiler;
                                    v___x_2799_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__1(v_options_2788_, v___x_2798_);
                                    if v___x_2799_ == 0 {
                                        crate::leanh::lean_dec_ref(v___f_2794_);
                                        crate::leanh::lean_inc_ref(v_run_x27_2792_);
                                        crate::leanh::lean_inc(v___y_2780_);
                                        crate::leanh::lean_inc_ref(v___y_2779_);
                                        crate::leanh::lean_inc(v___y_2778_);
                                        crate::leanh::lean_inc_ref(v___y_2777_);
                                        crate::leanh::lean_inc(v___y_2776_);
                                        crate::leanh::lean_inc_ref(v___y_2775_);
                                        v___x_2800_ = crate::leanh::lean_apply_8(
                                            v_run_x27_2792_,
                                            v_val_2786_,
                                            v___y_2775_,
                                            v___y_2776_,
                                            v___y_2777_,
                                            v___y_2778_,
                                            v___y_2779_,
                                            v___y_2780_,
                                            crate::leanh::lean_box(0),
                                        );
                                        return v___x_2800_;
                                    } else {
                                        crate::leanh::lean_inc_ref(v_run_x27_2792_);
                                        v___y_2719_ = v___y_2775_;
                                        v___y_2720_ = v___x_2797_;
                                        v___y_2721_ = v___y_2778_;
                                        v___y_2722_ = v_run_x27_2792_;
                                        v___y_2723_ = v_val_2786_;
                                        v___y_2724_ = v___y_2779_;
                                        v___y_2725_ = v___y_2776_;
                                        v___y_2726_ = v___x_2795_;
                                        v___y_2727_ = v_options_2788_;
                                        v___y_2728_ = v___f_2794_;
                                        v___y_2729_ = v___y_2777_;
                                        v___y_2730_ = v___y_2780_;
                                        v___y_2731_ = v_hasTrace_2789_;
                                        state = 5;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_inc_ref(v_run_x27_2792_);
                                    v___y_2719_ = v___y_2775_;
                                    v___y_2720_ = v___x_2797_;
                                    v___y_2721_ = v___y_2778_;
                                    v___y_2722_ = v_run_x27_2792_;
                                    v___y_2723_ = v_val_2786_;
                                    v___y_2724_ = v___y_2779_;
                                    v___y_2725_ = v___y_2776_;
                                    v___y_2726_ = v___x_2795_;
                                    v___y_2727_ = v_options_2788_;
                                    v___y_2728_ = v___f_2794_;
                                    v___y_2729_ = v___y_2777_;
                                    v___y_2730_ = v___y_2780_;
                                    v___y_2731_ = v_hasTrace_2789_;
                                    state = 5;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2784_);
                        v_isSharedCheck_2807_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2783_)) as u8;
                        if v_isSharedCheck_2807_ == 0 {
                            v_unused_2808_ = crate::leanh::lean_ctor_get(v___x_2783_, 0);
                            crate::leanh::lean_dec(v_unused_2808_);
                            v___x_2802_ = v___x_2783_;
                            v_isShared_2803_ = v_isSharedCheck_2807_;
                            state = 15;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_2783_);
                            v___x_2802_ = crate::leanh::lean_box(0);
                            v_isShared_2803_ = v_isSharedCheck_2807_;
                            state = 15;
                            continue;
                        }
                    }
                } else {
                    return v___x_2783_;
                }
            }
            15 => {
                if v_isShared_2803_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2802_, 0, v___x_2655_);
                    v___x_2805_ = v___x_2802_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2806_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2806_, 0, v___x_2655_);
                    v___x_2805_ = v_reuseFailAlloc_2806_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_2805_;
            }
            17 => {
                v_options_2818_ = crate::leanh::lean_ctor_get(v___y_2816_, 2);
                v_hasTrace_2819_ = crate::leanh::lean_ctor_get_uint8(
                    v_options_2818_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                if v_hasTrace_2819_ == 0 {
                    crate::leanh::lean_del_object(v___x_2664_);
                    v___y_2773_ = v_g_2811_;
                    v___y_2774_ = v___y_2810_;
                    v___y_2775_ = v___y_2812_;
                    v___y_2776_ = v___y_2813_;
                    v___y_2777_ = v___y_2814_;
                    v___y_2778_ = v___y_2815_;
                    v___y_2779_ = v___y_2816_;
                    v___y_2780_ = v___y_2817_;
                    state = 14;
                    continue;
                } else {
                    v_inheritedTraceOptions_2820_ = crate::leanh::lean_ctor_get(v___y_2816_, 13);
                    v___x_2821_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7);
                    v___x_2822_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_2820_,
                        v_options_2818_,
                        v___x_2821_,
                    );
                    if v___x_2822_ == 0 {
                        crate::leanh::lean_del_object(v___x_2664_);
                        v___y_2773_ = v_g_2811_;
                        v___y_2774_ = v___y_2810_;
                        v___y_2775_ = v___y_2812_;
                        v___y_2776_ = v___y_2813_;
                        v___y_2777_ = v___y_2814_;
                        v___y_2778_ = v___y_2815_;
                        v___y_2779_ = v___y_2816_;
                        v___y_2780_ = v___y_2817_;
                        state = 14;
                        continue;
                    } else {
                        v___x_2823_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__9_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__9);
                        crate::leanh::lean_inc(v_g_2811_);
                        if v_isShared_2665_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2664_, 0, v_g_2811_);
                            v___x_2825_ = v___x_2664_;
                            state = 18;
                            continue;
                        } else {
                            v_reuseFailAlloc_2836_ =
                                crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2836_, 0, v_g_2811_);
                            v___x_2825_ = v_reuseFailAlloc_2836_;
                            state = 18;
                            continue;
                        }
                    }
                }
            }
            18 => {
                v___x_2826_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2826_, 0, v___x_2823_);
                crate::leanh::lean_ctor_set(v___x_2826_, 1, v___x_2825_);
                v___x_2827_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg(v___x_2668_, v___x_2826_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_);
                if crate::leanh::lean_obj_tag(v___x_2827_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_2827_, 1);
                    v___y_2773_ = v_g_2811_;
                    v___y_2774_ = v___y_2810_;
                    v___y_2775_ = v___y_2812_;
                    v___y_2776_ = v___y_2813_;
                    v___y_2777_ = v___y_2814_;
                    v___y_2778_ = v___y_2815_;
                    v___y_2779_ = v___y_2816_;
                    v___y_2780_ = v___y_2817_;
                    state = 14;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_g_2811_);
                    v_a_2828_ = crate::leanh::lean_ctor_get(v___x_2827_, 0);
                    v_isSharedCheck_2835_ = (!crate::leanh::lean_is_exclusive(v___x_2827_)) as u8;
                    if v_isSharedCheck_2835_ == 0 {
                        v___x_2830_ = v___x_2827_;
                        v_isShared_2831_ = v_isSharedCheck_2835_;
                        state = 19;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2828_);
                        crate::leanh::lean_dec(v___x_2827_);
                        v___x_2830_ = crate::leanh::lean_box(0);
                        v_isShared_2831_ = v_isSharedCheck_2835_;
                        state = 19;
                        continue;
                    }
                }
            }
            19 => {
                if v_isShared_2831_ == 0 {
                    v___x_2833_ = v___x_2830_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_2834_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2834_, 0, v_a_2828_);
                    v___x_2833_ = v_reuseFailAlloc_2834_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_2833_;
            }
            21 => {
                if crate::leanh::lean_obj_tag(v___y_2845_) == 0 {
                    v_a_2846_ = crate::leanh::lean_ctor_get(v___y_2845_, 0);
                    v_isSharedCheck_2854_ = (!crate::leanh::lean_is_exclusive(v___y_2845_)) as u8;
                    if v_isSharedCheck_2854_ == 0 {
                        v___x_2848_ = v___y_2845_;
                        v_isShared_2849_ = v_isSharedCheck_2854_;
                        state = 22;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2846_);
                        crate::leanh::lean_dec(v___y_2845_);
                        v___x_2848_ = crate::leanh::lean_box(0);
                        v_isShared_2849_ = v_isSharedCheck_2854_;
                        state = 22;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2664_);
                    return v___y_2845_;
                }
            }
            22 => {
                if crate::leanh::lean_obj_tag(v_a_2846_) == 1 {
                    crate::leanh::lean_del_object(v___x_2848_);
                    v_val_2850_ = crate::leanh::lean_ctor_get(v_a_2846_, 0);
                    crate::leanh::lean_inc(v_val_2850_);
                    crate::leanh::lean_dec_ref_known(v_a_2846_, 1);
                    v___y_2810_ = v___y_2844_;
                    v_g_2811_ = v_val_2850_;
                    v___y_2812_ = v___y_2841_;
                    v___y_2813_ = v___y_2843_;
                    v___y_2814_ = v___y_2839_;
                    v___y_2815_ = v___y_2840_;
                    v___y_2816_ = v___y_2842_;
                    v___y_2817_ = v___y_2838_;
                    state = 17;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_a_2846_);
                    crate::leanh::lean_del_object(v___x_2664_);
                    if v_isShared_2849_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2848_, 0, v___x_2655_);
                        v___x_2852_ = v___x_2848_;
                        state = 23;
                        continue;
                    } else {
                        v_reuseFailAlloc_2853_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2853_, 0, v___x_2655_);
                        v___x_2852_ = v_reuseFailAlloc_2853_;
                        state = 23;
                        continue;
                    }
                }
            }
            23 => {
                return v___x_2852_;
            }
            24 => {
                v___x_2871_ = lean_io_get_num_heartbeats();
                v___x_2872_ = lean_float_of_nat(v___y_2866_);
                v___x_2873_ = lean_float_of_nat(v___x_2871_);
                v___x_2874_ = crate::leanh::lean_box_float(v___x_2872_);
                v___x_2875_ = crate::leanh::lean_box_float(v___x_2873_);
                v___x_2876_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2876_, 0, v___x_2874_);
                crate::leanh::lean_ctor_set(v___x_2876_, 1, v___x_2875_);
                v___x_2877_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2877_, 0, v_a_2870_);
                crate::leanh::lean_ctor_set(v___x_2877_, 1, v___x_2876_);
                crate::leanh::lean_inc_ref(v___y_2859_);
                v___x_2878_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2(v___x_2668_, v___y_2860_, v___y_2859_, v___y_2858_, v___y_2856_, v___y_2865_, v___y_2867_, v___x_2877_, v___y_2864_, v___y_2868_, v___y_2857_, v___y_2863_, v___y_2869_, v___y_2862_);
                v___y_2838_ = v___y_2862_;
                v___y_2839_ = v___y_2857_;
                v___y_2840_ = v___y_2863_;
                v___y_2841_ = v___y_2864_;
                v___y_2842_ = v___y_2869_;
                v___y_2843_ = v___y_2868_;
                v___y_2844_ = v___y_2861_;
                v___y_2845_ = v___x_2878_;
                state = 21;
                continue;
            }
            25 => {
                v___x_2895_ = lean_io_mono_nanos_now();
                v___x_2896_ = lean_float_of_nat(v___y_2884_);
                v___x_2897_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__4_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__4);
                v___x_2898_ = lean_float_div(v___x_2896_, v___x_2897_);
                v___x_2899_ = lean_float_of_nat(v___x_2895_);
                v___x_2900_ = lean_float_div(v___x_2899_, v___x_2897_);
                v___x_2901_ = crate::leanh::lean_box_float(v___x_2898_);
                v___x_2902_ = crate::leanh::lean_box_float(v___x_2900_);
                v___x_2903_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2903_, 0, v___x_2901_);
                crate::leanh::lean_ctor_set(v___x_2903_, 1, v___x_2902_);
                v___x_2904_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2904_, 0, v_a_2894_);
                crate::leanh::lean_ctor_set(v___x_2904_, 1, v___x_2903_);
                crate::leanh::lean_inc_ref(v___y_2883_);
                v___x_2905_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2(v___x_2668_, v___y_2885_, v___y_2883_, v___y_2882_, v___y_2880_, v___y_2890_, v___y_2891_, v___x_2904_, v___y_2889_, v___y_2892_, v___y_2881_, v___y_2888_, v___y_2893_, v___y_2887_);
                v___y_2838_ = v___y_2887_;
                v___y_2839_ = v___y_2881_;
                v___y_2840_ = v___y_2888_;
                v___y_2841_ = v___y_2889_;
                v___y_2842_ = v___y_2893_;
                v___y_2843_ = v___y_2892_;
                v___y_2844_ = v___y_2886_;
                v___y_2845_ = v___x_2905_;
                state = 21;
                continue;
            }
            26 => {
                v___x_2921_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___redArg(v___y_2915_);
                v_a_2922_ = crate::leanh::lean_ctor_get(v___x_2921_, 0);
                crate::leanh::lean_inc(v_a_2922_);
                crate::leanh::lean_dec_ref(v___x_2921_);
                v___x_2923_ = l_Lean_trace_profiler_useHeartbeats;
                v___x_2924_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__1(v___y_2909_, v___x_2923_);
                if v___x_2924_ == 0 {
                    v___x_2925_ = lean_io_mono_nanos_now();
                    crate::leanh::lean_inc(v___y_2915_);
                    crate::leanh::lean_inc_ref(v___y_2920_);
                    crate::leanh::lean_inc(v___y_2916_);
                    crate::leanh::lean_inc_ref(v___y_2908_);
                    crate::leanh::lean_inc(v___y_2919_);
                    crate::leanh::lean_inc_ref(v___y_2917_);
                    v___x_2926_ = crate::leanh::lean_apply_8(
                        v___y_2912_,
                        v___y_2910_,
                        v___y_2917_,
                        v___y_2919_,
                        v___y_2908_,
                        v___y_2916_,
                        v___y_2920_,
                        v___y_2915_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_2926_) == 0 {
                        v_a_2927_ = crate::leanh::lean_ctor_get(v___x_2926_, 0);
                        v_isSharedCheck_2934_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2926_)) as u8;
                        if v_isSharedCheck_2934_ == 0 {
                            v___x_2929_ = v___x_2926_;
                            v_isShared_2930_ = v_isSharedCheck_2934_;
                            state = 27;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2927_);
                            crate::leanh::lean_dec(v___x_2926_);
                            v___x_2929_ = crate::leanh::lean_box(0);
                            v_isShared_2930_ = v_isSharedCheck_2934_;
                            state = 27;
                            continue;
                        }
                    } else {
                        v_a_2935_ = crate::leanh::lean_ctor_get(v___x_2926_, 0);
                        v_isSharedCheck_2942_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2926_)) as u8;
                        if v_isSharedCheck_2942_ == 0 {
                            v___x_2937_ = v___x_2926_;
                            v_isShared_2938_ = v_isSharedCheck_2942_;
                            state = 29;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2935_);
                            crate::leanh::lean_dec(v___x_2926_);
                            v___x_2937_ = crate::leanh::lean_box(0);
                            v_isShared_2938_ = v_isSharedCheck_2942_;
                            state = 29;
                            continue;
                        }
                    }
                } else {
                    v___x_2943_ = lean_io_get_num_heartbeats();
                    crate::leanh::lean_inc(v___y_2915_);
                    crate::leanh::lean_inc_ref(v___y_2920_);
                    crate::leanh::lean_inc(v___y_2916_);
                    crate::leanh::lean_inc_ref(v___y_2908_);
                    crate::leanh::lean_inc(v___y_2919_);
                    crate::leanh::lean_inc_ref(v___y_2917_);
                    v___x_2944_ = crate::leanh::lean_apply_8(
                        v___y_2912_,
                        v___y_2910_,
                        v___y_2917_,
                        v___y_2919_,
                        v___y_2908_,
                        v___y_2916_,
                        v___y_2920_,
                        v___y_2915_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_2944_) == 0 {
                        v_a_2945_ = crate::leanh::lean_ctor_get(v___x_2944_, 0);
                        v_isSharedCheck_2952_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2944_)) as u8;
                        if v_isSharedCheck_2952_ == 0 {
                            v___x_2947_ = v___x_2944_;
                            v_isShared_2948_ = v_isSharedCheck_2952_;
                            state = 31;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2945_);
                            crate::leanh::lean_dec(v___x_2944_);
                            v___x_2947_ = crate::leanh::lean_box(0);
                            v_isShared_2948_ = v_isSharedCheck_2952_;
                            state = 31;
                            continue;
                        }
                    } else {
                        v_a_2953_ = crate::leanh::lean_ctor_get(v___x_2944_, 0);
                        v_isSharedCheck_2960_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2944_)) as u8;
                        if v_isSharedCheck_2960_ == 0 {
                            v___x_2955_ = v___x_2944_;
                            v_isShared_2956_ = v_isSharedCheck_2960_;
                            state = 33;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2953_);
                            crate::leanh::lean_dec(v___x_2944_);
                            v___x_2955_ = crate::leanh::lean_box(0);
                            v_isShared_2956_ = v_isSharedCheck_2960_;
                            state = 33;
                            continue;
                        }
                    }
                }
            }
            27 => {
                if v_isShared_2930_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2929_, 1);
                    v___x_2932_ = v___x_2929_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_2933_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2933_, 0, v_a_2927_);
                    v___x_2932_ = v_reuseFailAlloc_2933_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                v___y_2880_ = v___y_2907_;
                v___y_2881_ = v___y_2908_;
                v___y_2882_ = v___y_2909_;
                v___y_2883_ = v___y_2911_;
                v___y_2884_ = v___x_2925_;
                v___y_2885_ = v___y_2913_;
                v___y_2886_ = v___y_2914_;
                v___y_2887_ = v___y_2915_;
                v___y_2888_ = v___y_2916_;
                v___y_2889_ = v___y_2917_;
                v___y_2890_ = v_a_2922_;
                v___y_2891_ = v___y_2918_;
                v___y_2892_ = v___y_2919_;
                v___y_2893_ = v___y_2920_;
                v_a_2894_ = v___x_2932_;
                state = 25;
                continue;
            }
            29 => {
                if v_isShared_2938_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2937_, 0);
                    v___x_2940_ = v___x_2937_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_2941_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2941_, 0, v_a_2935_);
                    v___x_2940_ = v_reuseFailAlloc_2941_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                v___y_2880_ = v___y_2907_;
                v___y_2881_ = v___y_2908_;
                v___y_2882_ = v___y_2909_;
                v___y_2883_ = v___y_2911_;
                v___y_2884_ = v___x_2925_;
                v___y_2885_ = v___y_2913_;
                v___y_2886_ = v___y_2914_;
                v___y_2887_ = v___y_2915_;
                v___y_2888_ = v___y_2916_;
                v___y_2889_ = v___y_2917_;
                v___y_2890_ = v_a_2922_;
                v___y_2891_ = v___y_2918_;
                v___y_2892_ = v___y_2919_;
                v___y_2893_ = v___y_2920_;
                v_a_2894_ = v___x_2940_;
                state = 25;
                continue;
            }
            31 => {
                if v_isShared_2948_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2947_, 1);
                    v___x_2950_ = v___x_2947_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_2951_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2951_, 0, v_a_2945_);
                    v___x_2950_ = v_reuseFailAlloc_2951_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                v___y_2856_ = v___y_2907_;
                v___y_2857_ = v___y_2908_;
                v___y_2858_ = v___y_2909_;
                v___y_2859_ = v___y_2911_;
                v___y_2860_ = v___y_2913_;
                v___y_2861_ = v___y_2914_;
                v___y_2862_ = v___y_2915_;
                v___y_2863_ = v___y_2916_;
                v___y_2864_ = v___y_2917_;
                v___y_2865_ = v_a_2922_;
                v___y_2866_ = v___x_2943_;
                v___y_2867_ = v___y_2918_;
                v___y_2868_ = v___y_2919_;
                v___y_2869_ = v___y_2920_;
                v_a_2870_ = v___x_2950_;
                state = 24;
                continue;
            }
            33 => {
                if v_isShared_2956_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2955_, 0);
                    v___x_2958_ = v___x_2955_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_2959_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2959_, 0, v_a_2953_);
                    v___x_2958_ = v_reuseFailAlloc_2959_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                v___y_2856_ = v___y_2907_;
                v___y_2857_ = v___y_2908_;
                v___y_2858_ = v___y_2909_;
                v___y_2859_ = v___y_2911_;
                v___y_2860_ = v___y_2913_;
                v___y_2861_ = v___y_2914_;
                v___y_2862_ = v___y_2915_;
                v___y_2863_ = v___y_2916_;
                v___y_2864_ = v___y_2917_;
                v___y_2865_ = v_a_2922_;
                v___y_2866_ = v___x_2943_;
                v___y_2867_ = v___y_2918_;
                v___y_2868_ = v___y_2919_;
                v___y_2869_ = v___y_2920_;
                v_a_2870_ = v___x_2958_;
                state = 24;
                continue;
            }
            35 => {
                if v_fixedInt_2963_ == 0 {
                    v___y_2810_ = v___y_2962_;
                    v_g_2811_ = v_g_2964_;
                    v___y_2812_ = v___y_2965_;
                    v___y_2813_ = v___y_2966_;
                    v___y_2814_ = v___y_2967_;
                    v___y_2815_ = v___y_2968_;
                    v___y_2816_ = v___y_2969_;
                    v___y_2817_ = v___y_2970_;
                    state = 17;
                    continue;
                } else {
                    v___x_2971_ = l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass;
                    v_options_2972_ = crate::leanh::lean_ctor_get(v___y_2969_, 2);
                    v_hasTrace_2973_ = crate::leanh::lean_ctor_get_uint8(
                        v_options_2972_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_2973_ == 0 {
                        v_run_x27_2974_ = crate::leanh::lean_ctor_get(v___x_2971_, 1);
                        crate::leanh::lean_inc_ref(v_run_x27_2974_);
                        crate::leanh::lean_inc(v___y_2970_);
                        crate::leanh::lean_inc_ref(v___y_2969_);
                        crate::leanh::lean_inc(v___y_2968_);
                        crate::leanh::lean_inc_ref(v___y_2967_);
                        crate::leanh::lean_inc(v___y_2966_);
                        crate::leanh::lean_inc_ref(v___y_2965_);
                        v___x_2975_ = crate::leanh::lean_apply_8(
                            v_run_x27_2974_,
                            v_g_2964_,
                            v___y_2965_,
                            v___y_2966_,
                            v___y_2967_,
                            v___y_2968_,
                            v___y_2969_,
                            v___y_2970_,
                            crate::leanh::lean_box(0),
                        );
                        v___y_2838_ = v___y_2970_;
                        v___y_2839_ = v___y_2967_;
                        v___y_2840_ = v___y_2968_;
                        v___y_2841_ = v___y_2965_;
                        v___y_2842_ = v___y_2969_;
                        v___y_2843_ = v___y_2966_;
                        v___y_2844_ = v___y_2962_;
                        v___y_2845_ = v___x_2975_;
                        state = 21;
                        continue;
                    } else {
                        v_run_x27_2976_ = crate::leanh::lean_ctor_get(v___x_2971_, 1);
                        v_inheritedTraceOptions_2977_ =
                            crate::leanh::lean_ctor_get(v___y_2969_, 13);
                        crate::leanh::lean_inc(v_g_2964_);
                        v___f_2978_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__1___boxed as *mut core::ffi::c_void, 10, 2);
                        crate::leanh::lean_closure_set(v___f_2978_, 0, v___x_2971_);
                        crate::leanh::lean_closure_set(v___f_2978_, 1, v_g_2964_);
                        v___x_2979_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__1;
                        v___x_2980_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7);
                        v___x_2981_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_2977_,
                            v_options_2972_,
                            v___x_2980_,
                        );
                        if v___x_2981_ == 0 {
                            v___x_2982_ = l_Lean_trace_profiler;
                            v___x_2983_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__1(v_options_2972_, v___x_2982_);
                            if v___x_2983_ == 0 {
                                crate::leanh::lean_dec_ref(v___f_2978_);
                                crate::leanh::lean_inc_ref(v_run_x27_2976_);
                                crate::leanh::lean_inc(v___y_2970_);
                                crate::leanh::lean_inc_ref(v___y_2969_);
                                crate::leanh::lean_inc(v___y_2968_);
                                crate::leanh::lean_inc_ref(v___y_2967_);
                                crate::leanh::lean_inc(v___y_2966_);
                                crate::leanh::lean_inc_ref(v___y_2965_);
                                v___x_2984_ = crate::leanh::lean_apply_8(
                                    v_run_x27_2976_,
                                    v_g_2964_,
                                    v___y_2965_,
                                    v___y_2966_,
                                    v___y_2967_,
                                    v___y_2968_,
                                    v___y_2969_,
                                    v___y_2970_,
                                    crate::leanh::lean_box(0),
                                );
                                v___y_2838_ = v___y_2970_;
                                v___y_2839_ = v___y_2967_;
                                v___y_2840_ = v___y_2968_;
                                v___y_2841_ = v___y_2965_;
                                v___y_2842_ = v___y_2969_;
                                v___y_2843_ = v___y_2966_;
                                v___y_2844_ = v___y_2962_;
                                v___y_2845_ = v___x_2984_;
                                state = 21;
                                continue;
                            } else {
                                crate::leanh::lean_inc_ref(v_run_x27_2976_);
                                v___y_2907_ = v___x_2981_;
                                v___y_2908_ = v___y_2967_;
                                v___y_2909_ = v_options_2972_;
                                v___y_2910_ = v_g_2964_;
                                v___y_2911_ = v___x_2979_;
                                v___y_2912_ = v_run_x27_2976_;
                                v___y_2913_ = v_hasTrace_2973_;
                                v___y_2914_ = v___y_2962_;
                                v___y_2915_ = v___y_2970_;
                                v___y_2916_ = v___y_2968_;
                                v___y_2917_ = v___y_2965_;
                                v___y_2918_ = v___f_2978_;
                                v___y_2919_ = v___y_2966_;
                                v___y_2920_ = v___y_2969_;
                                state = 26;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_inc_ref(v_run_x27_2976_);
                            v___y_2907_ = v___x_2981_;
                            v___y_2908_ = v___y_2967_;
                            v___y_2909_ = v_options_2972_;
                            v___y_2910_ = v_g_2964_;
                            v___y_2911_ = v___x_2979_;
                            v___y_2912_ = v_run_x27_2976_;
                            v___y_2913_ = v_hasTrace_2973_;
                            v___y_2914_ = v___y_2962_;
                            v___y_2915_ = v___y_2970_;
                            v___y_2916_ = v___y_2968_;
                            v___y_2917_ = v___y_2965_;
                            v___y_2918_ = v___f_2978_;
                            v___y_2919_ = v___y_2966_;
                            v___y_2920_ = v___y_2969_;
                            state = 26;
                            continue;
                        }
                    }
                }
            }
            36 => {
                if crate::leanh::lean_obj_tag(v___y_2993_) == 0 {
                    v_a_2994_ = crate::leanh::lean_ctor_get(v___y_2993_, 0);
                    v_isSharedCheck_3003_ = (!crate::leanh::lean_is_exclusive(v___y_2993_)) as u8;
                    if v_isSharedCheck_3003_ == 0 {
                        v___x_2996_ = v___y_2993_;
                        v_isShared_2997_ = v_isSharedCheck_3003_;
                        state = 37;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2994_);
                        crate::leanh::lean_dec(v___y_2993_);
                        v___x_2996_ = crate::leanh::lean_box(0);
                        v_isShared_2997_ = v_isSharedCheck_3003_;
                        state = 37;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2664_);
                    return v___y_2993_;
                }
            }
            37 => {
                if crate::leanh::lean_obj_tag(v_a_2994_) == 1 {
                    crate::leanh::lean_del_object(v___x_2996_);
                    v_val_2998_ = crate::leanh::lean_ctor_get(v_a_2994_, 0);
                    crate::leanh::lean_inc(v_val_2998_);
                    crate::leanh::lean_dec_ref_known(v_a_2994_, 1);
                    v_fixedInt_2999_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_2992_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 6) as u32,
                    );
                    v___y_2962_ = v___y_2992_;
                    v_fixedInt_2963_ = v_fixedInt_2999_;
                    v_g_2964_ = v_val_2998_;
                    v___y_2965_ = v___y_2988_;
                    v___y_2966_ = v___y_2990_;
                    v___y_2967_ = v___y_2989_;
                    v___y_2968_ = v___y_2986_;
                    v___y_2969_ = v___y_2991_;
                    v___y_2970_ = v___y_2987_;
                    state = 35;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_a_2994_);
                    crate::leanh::lean_del_object(v___x_2664_);
                    if v_isShared_2997_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2996_, 0, v___x_2655_);
                        v___x_3001_ = v___x_2996_;
                        state = 38;
                        continue;
                    } else {
                        v_reuseFailAlloc_3002_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3002_, 0, v___x_2655_);
                        v___x_3001_ = v_reuseFailAlloc_3002_;
                        state = 38;
                        continue;
                    }
                }
            }
            38 => {
                return v___x_3001_;
            }
            39 => {
                v___x_3020_ = lean_io_get_num_heartbeats();
                v___x_3021_ = lean_float_of_nat(v___y_3017_);
                v___x_3022_ = lean_float_of_nat(v___x_3020_);
                v___x_3023_ = crate::leanh::lean_box_float(v___x_3021_);
                v___x_3024_ = crate::leanh::lean_box_float(v___x_3022_);
                v___x_3025_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3025_, 0, v___x_3023_);
                crate::leanh::lean_ctor_set(v___x_3025_, 1, v___x_3024_);
                v___x_3026_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3026_, 0, v_a_3019_);
                crate::leanh::lean_ctor_set(v___x_3026_, 1, v___x_3025_);
                crate::leanh::lean_inc_ref(v___y_3013_);
                v___x_3027_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2(v___x_2668_, v___y_3006_, v___y_3013_, v___y_3016_, v___y_3018_, v___y_3014_, v___y_3009_, v___x_3026_, v___y_3007_, v___y_3015_, v___y_3008_, v___y_3012_, v___y_3010_, v___y_3005_);
                v___y_2986_ = v___y_3012_;
                v___y_2987_ = v___y_3005_;
                v___y_2988_ = v___y_3007_;
                v___y_2989_ = v___y_3008_;
                v___y_2990_ = v___y_3015_;
                v___y_2991_ = v___y_3010_;
                v___y_2992_ = v___y_3011_;
                v___y_2993_ = v___x_3027_;
                state = 36;
                continue;
            }
            40 => {
                v___x_3044_ = lean_io_mono_nanos_now();
                v___x_3045_ = lean_float_of_nat(v___y_3033_);
                v___x_3046_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__4_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__4);
                v___x_3047_ = lean_float_div(v___x_3045_, v___x_3046_);
                v___x_3048_ = lean_float_of_nat(v___x_3044_);
                v___x_3049_ = lean_float_div(v___x_3048_, v___x_3046_);
                v___x_3050_ = crate::leanh::lean_box_float(v___x_3047_);
                v___x_3051_ = crate::leanh::lean_box_float(v___x_3049_);
                v___x_3052_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3052_, 0, v___x_3050_);
                crate::leanh::lean_ctor_set(v___x_3052_, 1, v___x_3051_);
                v___x_3053_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3053_, 0, v_a_3043_);
                crate::leanh::lean_ctor_set(v___x_3053_, 1, v___x_3052_);
                crate::leanh::lean_inc_ref(v___y_3038_);
                v___x_3054_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2(v___x_2668_, v___y_3030_, v___y_3038_, v___y_3041_, v___y_3042_, v___y_3039_, v___y_3034_, v___x_3053_, v___y_3031_, v___y_3040_, v___y_3032_, v___y_3037_, v___y_3035_, v___y_3029_);
                v___y_2986_ = v___y_3037_;
                v___y_2987_ = v___y_3029_;
                v___y_2988_ = v___y_3031_;
                v___y_2989_ = v___y_3032_;
                v___y_2990_ = v___y_3040_;
                v___y_2991_ = v___y_3035_;
                v___y_2992_ = v___y_3036_;
                v___y_2993_ = v___x_3054_;
                state = 36;
                continue;
            }
            41 => {
                v___x_3070_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___redArg(v___y_3056_);
                v_a_3071_ = crate::leanh::lean_ctor_get(v___x_3070_, 0);
                crate::leanh::lean_inc(v_a_3071_);
                crate::leanh::lean_dec_ref(v___x_3070_);
                v___x_3072_ = l_Lean_trace_profiler_useHeartbeats;
                v___x_3073_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__1(v___y_3067_, v___x_3072_);
                if v___x_3073_ == 0 {
                    v___x_3074_ = lean_io_mono_nanos_now();
                    crate::leanh::lean_inc(v___y_3056_);
                    crate::leanh::lean_inc_ref(v___y_3061_);
                    crate::leanh::lean_inc(v___y_3063_);
                    crate::leanh::lean_inc_ref(v___y_3059_);
                    crate::leanh::lean_inc(v___y_3066_);
                    crate::leanh::lean_inc_ref(v___y_3057_);
                    v___x_3075_ = crate::leanh::lean_apply_8(
                        v___y_3065_,
                        v___y_3069_,
                        v___y_3057_,
                        v___y_3066_,
                        v___y_3059_,
                        v___y_3063_,
                        v___y_3061_,
                        v___y_3056_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_3075_) == 0 {
                        v_a_3076_ = crate::leanh::lean_ctor_get(v___x_3075_, 0);
                        v_isSharedCheck_3083_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3075_)) as u8;
                        if v_isSharedCheck_3083_ == 0 {
                            v___x_3078_ = v___x_3075_;
                            v_isShared_3079_ = v_isSharedCheck_3083_;
                            state = 42;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3076_);
                            crate::leanh::lean_dec(v___x_3075_);
                            v___x_3078_ = crate::leanh::lean_box(0);
                            v_isShared_3079_ = v_isSharedCheck_3083_;
                            state = 42;
                            continue;
                        }
                    } else {
                        v_a_3084_ = crate::leanh::lean_ctor_get(v___x_3075_, 0);
                        v_isSharedCheck_3091_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3075_)) as u8;
                        if v_isSharedCheck_3091_ == 0 {
                            v___x_3086_ = v___x_3075_;
                            v_isShared_3087_ = v_isSharedCheck_3091_;
                            state = 44;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3084_);
                            crate::leanh::lean_dec(v___x_3075_);
                            v___x_3086_ = crate::leanh::lean_box(0);
                            v_isShared_3087_ = v_isSharedCheck_3091_;
                            state = 44;
                            continue;
                        }
                    }
                } else {
                    v___x_3092_ = lean_io_get_num_heartbeats();
                    crate::leanh::lean_inc(v___y_3056_);
                    crate::leanh::lean_inc_ref(v___y_3061_);
                    crate::leanh::lean_inc(v___y_3063_);
                    crate::leanh::lean_inc_ref(v___y_3059_);
                    crate::leanh::lean_inc(v___y_3066_);
                    crate::leanh::lean_inc_ref(v___y_3057_);
                    v___x_3093_ = crate::leanh::lean_apply_8(
                        v___y_3065_,
                        v___y_3069_,
                        v___y_3057_,
                        v___y_3066_,
                        v___y_3059_,
                        v___y_3063_,
                        v___y_3061_,
                        v___y_3056_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_3093_) == 0 {
                        v_a_3094_ = crate::leanh::lean_ctor_get(v___x_3093_, 0);
                        v_isSharedCheck_3101_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3093_)) as u8;
                        if v_isSharedCheck_3101_ == 0 {
                            v___x_3096_ = v___x_3093_;
                            v_isShared_3097_ = v_isSharedCheck_3101_;
                            state = 46;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3094_);
                            crate::leanh::lean_dec(v___x_3093_);
                            v___x_3096_ = crate::leanh::lean_box(0);
                            v_isShared_3097_ = v_isSharedCheck_3101_;
                            state = 46;
                            continue;
                        }
                    } else {
                        v_a_3102_ = crate::leanh::lean_ctor_get(v___x_3093_, 0);
                        v_isSharedCheck_3109_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3093_)) as u8;
                        if v_isSharedCheck_3109_ == 0 {
                            v___x_3104_ = v___x_3093_;
                            v_isShared_3105_ = v_isSharedCheck_3109_;
                            state = 48;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3102_);
                            crate::leanh::lean_dec(v___x_3093_);
                            v___x_3104_ = crate::leanh::lean_box(0);
                            v_isShared_3105_ = v_isSharedCheck_3109_;
                            state = 48;
                            continue;
                        }
                    }
                }
            }
            42 => {
                if v_isShared_3079_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3078_, 1);
                    v___x_3081_ = v___x_3078_;
                    state = 43;
                    continue;
                } else {
                    v_reuseFailAlloc_3082_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3082_, 0, v_a_3076_);
                    v___x_3081_ = v_reuseFailAlloc_3082_;
                    state = 43;
                    continue;
                }
            }
            43 => {
                v___y_3029_ = v___y_3056_;
                v___y_3030_ = v___y_3058_;
                v___y_3031_ = v___y_3057_;
                v___y_3032_ = v___y_3059_;
                v___y_3033_ = v___x_3074_;
                v___y_3034_ = v___y_3060_;
                v___y_3035_ = v___y_3061_;
                v___y_3036_ = v___y_3062_;
                v___y_3037_ = v___y_3063_;
                v___y_3038_ = v___y_3064_;
                v___y_3039_ = v_a_3071_;
                v___y_3040_ = v___y_3066_;
                v___y_3041_ = v___y_3067_;
                v___y_3042_ = v___y_3068_;
                v_a_3043_ = v___x_3081_;
                state = 40;
                continue;
            }
            44 => {
                if v_isShared_3087_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3086_, 0);
                    v___x_3089_ = v___x_3086_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_3090_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3090_, 0, v_a_3084_);
                    v___x_3089_ = v_reuseFailAlloc_3090_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                v___y_3029_ = v___y_3056_;
                v___y_3030_ = v___y_3058_;
                v___y_3031_ = v___y_3057_;
                v___y_3032_ = v___y_3059_;
                v___y_3033_ = v___x_3074_;
                v___y_3034_ = v___y_3060_;
                v___y_3035_ = v___y_3061_;
                v___y_3036_ = v___y_3062_;
                v___y_3037_ = v___y_3063_;
                v___y_3038_ = v___y_3064_;
                v___y_3039_ = v_a_3071_;
                v___y_3040_ = v___y_3066_;
                v___y_3041_ = v___y_3067_;
                v___y_3042_ = v___y_3068_;
                v_a_3043_ = v___x_3089_;
                state = 40;
                continue;
            }
            46 => {
                if v_isShared_3097_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3096_, 1);
                    v___x_3099_ = v___x_3096_;
                    state = 47;
                    continue;
                } else {
                    v_reuseFailAlloc_3100_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3100_, 0, v_a_3094_);
                    v___x_3099_ = v_reuseFailAlloc_3100_;
                    state = 47;
                    continue;
                }
            }
            47 => {
                v___y_3005_ = v___y_3056_;
                v___y_3006_ = v___y_3058_;
                v___y_3007_ = v___y_3057_;
                v___y_3008_ = v___y_3059_;
                v___y_3009_ = v___y_3060_;
                v___y_3010_ = v___y_3061_;
                v___y_3011_ = v___y_3062_;
                v___y_3012_ = v___y_3063_;
                v___y_3013_ = v___y_3064_;
                v___y_3014_ = v_a_3071_;
                v___y_3015_ = v___y_3066_;
                v___y_3016_ = v___y_3067_;
                v___y_3017_ = v___x_3092_;
                v___y_3018_ = v___y_3068_;
                v_a_3019_ = v___x_3099_;
                state = 39;
                continue;
            }
            48 => {
                if v_isShared_3105_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3104_, 0);
                    v___x_3107_ = v___x_3104_;
                    state = 49;
                    continue;
                } else {
                    v_reuseFailAlloc_3108_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3108_, 0, v_a_3102_);
                    v___x_3107_ = v_reuseFailAlloc_3108_;
                    state = 49;
                    continue;
                }
            }
            49 => {
                v___y_3005_ = v___y_3056_;
                v___y_3006_ = v___y_3058_;
                v___y_3007_ = v___y_3057_;
                v___y_3008_ = v___y_3059_;
                v___y_3009_ = v___y_3060_;
                v___y_3010_ = v___y_3061_;
                v___y_3011_ = v___y_3062_;
                v___y_3012_ = v___y_3063_;
                v___y_3013_ = v___y_3064_;
                v___y_3014_ = v_a_3071_;
                v___y_3015_ = v___y_3066_;
                v___y_3016_ = v___y_3067_;
                v___y_3017_ = v___x_3092_;
                v___y_3018_ = v___y_3068_;
                v_a_3019_ = v___x_3107_;
                state = 39;
                continue;
            }
            50 => {
                if v_enums_3113_ == 0 {
                    v___y_2962_ = v___y_3111_;
                    v_fixedInt_2963_ = v_fixedInt_3112_;
                    v_g_2964_ = v_g_3114_;
                    v___y_2965_ = v___y_3115_;
                    v___y_2966_ = v___y_3116_;
                    v___y_2967_ = v___y_3117_;
                    v___y_2968_ = v___y_3118_;
                    v___y_2969_ = v___y_3119_;
                    v___y_2970_ = v___y_3120_;
                    state = 35;
                    continue;
                } else {
                    v___x_3121_ = l_Lean_Meta_Tactic_BVDecide_Normalize_enumsPass;
                    v_options_3122_ = crate::leanh::lean_ctor_get(v___y_3119_, 2);
                    v_hasTrace_3123_ = crate::leanh::lean_ctor_get_uint8(
                        v_options_3122_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_3123_ == 0 {
                        v_run_x27_3124_ = crate::leanh::lean_ctor_get(v___x_3121_, 1);
                        crate::leanh::lean_inc_ref(v_run_x27_3124_);
                        crate::leanh::lean_inc(v___y_3120_);
                        crate::leanh::lean_inc_ref(v___y_3119_);
                        crate::leanh::lean_inc(v___y_3118_);
                        crate::leanh::lean_inc_ref(v___y_3117_);
                        crate::leanh::lean_inc(v___y_3116_);
                        crate::leanh::lean_inc_ref(v___y_3115_);
                        v___x_3125_ = crate::leanh::lean_apply_8(
                            v_run_x27_3124_,
                            v_g_3114_,
                            v___y_3115_,
                            v___y_3116_,
                            v___y_3117_,
                            v___y_3118_,
                            v___y_3119_,
                            v___y_3120_,
                            crate::leanh::lean_box(0),
                        );
                        v___y_2986_ = v___y_3118_;
                        v___y_2987_ = v___y_3120_;
                        v___y_2988_ = v___y_3115_;
                        v___y_2989_ = v___y_3117_;
                        v___y_2990_ = v___y_3116_;
                        v___y_2991_ = v___y_3119_;
                        v___y_2992_ = v___y_3111_;
                        v___y_2993_ = v___x_3125_;
                        state = 36;
                        continue;
                    } else {
                        v_run_x27_3126_ = crate::leanh::lean_ctor_get(v___x_3121_, 1);
                        v_inheritedTraceOptions_3127_ =
                            crate::leanh::lean_ctor_get(v___y_3119_, 13);
                        crate::leanh::lean_inc(v_g_3114_);
                        v___f_3128_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__1___boxed as *mut core::ffi::c_void, 10, 2);
                        crate::leanh::lean_closure_set(v___f_3128_, 0, v___x_3121_);
                        crate::leanh::lean_closure_set(v___f_3128_, 1, v_g_3114_);
                        v___x_3129_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__1;
                        v___x_3130_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7);
                        v___x_3131_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_3127_,
                            v_options_3122_,
                            v___x_3130_,
                        );
                        if v___x_3131_ == 0 {
                            v___x_3132_ = l_Lean_trace_profiler;
                            v___x_3133_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__1(v_options_3122_, v___x_3132_);
                            if v___x_3133_ == 0 {
                                crate::leanh::lean_dec_ref(v___f_3128_);
                                crate::leanh::lean_inc_ref(v_run_x27_3126_);
                                crate::leanh::lean_inc(v___y_3120_);
                                crate::leanh::lean_inc_ref(v___y_3119_);
                                crate::leanh::lean_inc(v___y_3118_);
                                crate::leanh::lean_inc_ref(v___y_3117_);
                                crate::leanh::lean_inc(v___y_3116_);
                                crate::leanh::lean_inc_ref(v___y_3115_);
                                v___x_3134_ = crate::leanh::lean_apply_8(
                                    v_run_x27_3126_,
                                    v_g_3114_,
                                    v___y_3115_,
                                    v___y_3116_,
                                    v___y_3117_,
                                    v___y_3118_,
                                    v___y_3119_,
                                    v___y_3120_,
                                    crate::leanh::lean_box(0),
                                );
                                v___y_2986_ = v___y_3118_;
                                v___y_2987_ = v___y_3120_;
                                v___y_2988_ = v___y_3115_;
                                v___y_2989_ = v___y_3117_;
                                v___y_2990_ = v___y_3116_;
                                v___y_2991_ = v___y_3119_;
                                v___y_2992_ = v___y_3111_;
                                v___y_2993_ = v___x_3134_;
                                state = 36;
                                continue;
                            } else {
                                crate::leanh::lean_inc_ref(v_run_x27_3126_);
                                v___y_3056_ = v___y_3120_;
                                v___y_3057_ = v___y_3115_;
                                v___y_3058_ = v_hasTrace_3123_;
                                v___y_3059_ = v___y_3117_;
                                v___y_3060_ = v___f_3128_;
                                v___y_3061_ = v___y_3119_;
                                v___y_3062_ = v___y_3111_;
                                v___y_3063_ = v___y_3118_;
                                v___y_3064_ = v___x_3129_;
                                v___y_3065_ = v_run_x27_3126_;
                                v___y_3066_ = v___y_3116_;
                                v___y_3067_ = v_options_3122_;
                                v___y_3068_ = v___x_3131_;
                                v___y_3069_ = v_g_3114_;
                                state = 41;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_inc_ref(v_run_x27_3126_);
                            v___y_3056_ = v___y_3120_;
                            v___y_3057_ = v___y_3115_;
                            v___y_3058_ = v_hasTrace_3123_;
                            v___y_3059_ = v___y_3117_;
                            v___y_3060_ = v___f_3128_;
                            v___y_3061_ = v___y_3119_;
                            v___y_3062_ = v___y_3111_;
                            v___y_3063_ = v___y_3118_;
                            v___y_3064_ = v___x_3129_;
                            v___y_3065_ = v_run_x27_3126_;
                            v___y_3066_ = v___y_3116_;
                            v___y_3067_ = v_options_3122_;
                            v___y_3068_ = v___x_3131_;
                            v___y_3069_ = v_g_3114_;
                            state = 41;
                            continue;
                        }
                    }
                }
            }
            51 => {
                if crate::leanh::lean_obj_tag(v___y_3143_) == 0 {
                    v_a_3144_ = crate::leanh::lean_ctor_get(v___y_3143_, 0);
                    v_isSharedCheck_3154_ = (!crate::leanh::lean_is_exclusive(v___y_3143_)) as u8;
                    if v_isSharedCheck_3154_ == 0 {
                        v___x_3146_ = v___y_3143_;
                        v_isShared_3147_ = v_isSharedCheck_3154_;
                        state = 52;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3144_);
                        crate::leanh::lean_dec(v___y_3143_);
                        v___x_3146_ = crate::leanh::lean_box(0);
                        v_isShared_3147_ = v_isSharedCheck_3154_;
                        state = 52;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2664_);
                    return v___y_3143_;
                }
            }
            52 => {
                if crate::leanh::lean_obj_tag(v_a_3144_) == 1 {
                    crate::leanh::lean_del_object(v___x_3146_);
                    v_val_3148_ = crate::leanh::lean_ctor_get(v_a_3144_, 0);
                    crate::leanh::lean_inc(v_val_3148_);
                    crate::leanh::lean_dec_ref_known(v_a_3144_, 1);
                    v_fixedInt_3149_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_3141_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 6) as u32,
                    );
                    v_enums_3150_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_3141_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 7) as u32,
                    );
                    v___y_3111_ = v___y_3141_;
                    v_fixedInt_3112_ = v_fixedInt_3149_;
                    v_enums_3113_ = v_enums_3150_;
                    v_g_3114_ = v_val_3148_;
                    v___y_3115_ = v___y_3138_;
                    v___y_3116_ = v___y_3140_;
                    v___y_3117_ = v___y_3139_;
                    v___y_3118_ = v___y_3142_;
                    v___y_3119_ = v___y_3137_;
                    v___y_3120_ = v___y_3136_;
                    state = 50;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_a_3144_);
                    crate::leanh::lean_del_object(v___x_2664_);
                    if v_isShared_3147_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3146_, 0, v___x_2655_);
                        v___x_3152_ = v___x_3146_;
                        state = 53;
                        continue;
                    } else {
                        v_reuseFailAlloc_3153_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3153_, 0, v___x_2655_);
                        v___x_3152_ = v_reuseFailAlloc_3153_;
                        state = 53;
                        continue;
                    }
                }
            }
            53 => {
                return v___x_3152_;
            }
            54 => {
                v___x_3171_ = lean_io_get_num_heartbeats();
                v___x_3172_ = lean_float_of_nat(v___y_3161_);
                v___x_3173_ = lean_float_of_nat(v___x_3171_);
                v___x_3174_ = crate::leanh::lean_box_float(v___x_3172_);
                v___x_3175_ = crate::leanh::lean_box_float(v___x_3173_);
                v___x_3176_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3176_, 0, v___x_3174_);
                crate::leanh::lean_ctor_set(v___x_3176_, 1, v___x_3175_);
                v___x_3177_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3177_, 0, v_a_3170_);
                crate::leanh::lean_ctor_set(v___x_3177_, 1, v___x_3176_);
                crate::leanh::lean_inc_ref(v___y_3156_);
                v___x_3178_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2(v___x_2668_, v___y_3158_, v___y_3156_, v___y_3160_, v___y_3166_, v___y_3169_, v___y_3157_, v___x_3177_, v___y_3159_, v___y_3162_, v___y_3163_, v___y_3165_, v___y_3167_, v___y_3168_);
                v___y_3136_ = v___y_3168_;
                v___y_3137_ = v___y_3167_;
                v___y_3138_ = v___y_3159_;
                v___y_3139_ = v___y_3163_;
                v___y_3140_ = v___y_3162_;
                v___y_3141_ = v___y_3164_;
                v___y_3142_ = v___y_3165_;
                v___y_3143_ = v___x_3178_;
                state = 51;
                continue;
            }
            55 => {
                v___x_3195_ = lean_io_mono_nanos_now();
                v___x_3196_ = lean_float_of_nat(v___y_3188_);
                v___x_3197_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__4_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__4);
                v___x_3198_ = lean_float_div(v___x_3196_, v___x_3197_);
                v___x_3199_ = lean_float_of_nat(v___x_3195_);
                v___x_3200_ = lean_float_div(v___x_3199_, v___x_3197_);
                v___x_3201_ = crate::leanh::lean_box_float(v___x_3198_);
                v___x_3202_ = crate::leanh::lean_box_float(v___x_3200_);
                v___x_3203_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3203_, 0, v___x_3201_);
                crate::leanh::lean_ctor_set(v___x_3203_, 1, v___x_3202_);
                v___x_3204_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3204_, 0, v_a_3194_);
                crate::leanh::lean_ctor_set(v___x_3204_, 1, v___x_3203_);
                crate::leanh::lean_inc_ref(v___y_3180_);
                v___x_3205_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2(v___x_2668_, v___y_3182_, v___y_3180_, v___y_3184_, v___y_3190_, v___y_3193_, v___y_3181_, v___x_3204_, v___y_3183_, v___y_3185_, v___y_3186_, v___y_3189_, v___y_3191_, v___y_3192_);
                v___y_3136_ = v___y_3192_;
                v___y_3137_ = v___y_3191_;
                v___y_3138_ = v___y_3183_;
                v___y_3139_ = v___y_3186_;
                v___y_3140_ = v___y_3185_;
                v___y_3141_ = v___y_3187_;
                v___y_3142_ = v___y_3189_;
                v___y_3143_ = v___x_3205_;
                state = 51;
                continue;
            }
            56 => {
                v___x_3221_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___redArg(v___y_3219_);
                v_a_3222_ = crate::leanh::lean_ctor_get(v___x_3221_, 0);
                crate::leanh::lean_inc(v_a_3222_);
                crate::leanh::lean_dec_ref(v___x_3221_);
                v___x_3223_ = l_Lean_trace_profiler_useHeartbeats;
                v___x_3224_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__1(v___y_3213_, v___x_3223_);
                if v___x_3224_ == 0 {
                    v___x_3225_ = lean_io_mono_nanos_now();
                    crate::leanh::lean_inc(v___y_3219_);
                    crate::leanh::lean_inc_ref(v___y_3218_);
                    crate::leanh::lean_inc(v___y_3216_);
                    crate::leanh::lean_inc_ref(v___y_3215_);
                    crate::leanh::lean_inc(v___y_3214_);
                    crate::leanh::lean_inc_ref(v___y_3210_);
                    v___x_3226_ = crate::leanh::lean_apply_8(
                        v___y_3209_,
                        v___y_3212_,
                        v___y_3210_,
                        v___y_3214_,
                        v___y_3215_,
                        v___y_3216_,
                        v___y_3218_,
                        v___y_3219_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_3226_) == 0 {
                        v_a_3227_ = crate::leanh::lean_ctor_get(v___x_3226_, 0);
                        v_isSharedCheck_3234_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3226_)) as u8;
                        if v_isSharedCheck_3234_ == 0 {
                            v___x_3229_ = v___x_3226_;
                            v_isShared_3230_ = v_isSharedCheck_3234_;
                            state = 57;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3227_);
                            crate::leanh::lean_dec(v___x_3226_);
                            v___x_3229_ = crate::leanh::lean_box(0);
                            v_isShared_3230_ = v_isSharedCheck_3234_;
                            state = 57;
                            continue;
                        }
                    } else {
                        v_a_3235_ = crate::leanh::lean_ctor_get(v___x_3226_, 0);
                        v_isSharedCheck_3242_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3226_)) as u8;
                        if v_isSharedCheck_3242_ == 0 {
                            v___x_3237_ = v___x_3226_;
                            v_isShared_3238_ = v_isSharedCheck_3242_;
                            state = 59;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3235_);
                            crate::leanh::lean_dec(v___x_3226_);
                            v___x_3237_ = crate::leanh::lean_box(0);
                            v_isShared_3238_ = v_isSharedCheck_3242_;
                            state = 59;
                            continue;
                        }
                    }
                } else {
                    v___x_3243_ = lean_io_get_num_heartbeats();
                    crate::leanh::lean_inc(v___y_3219_);
                    crate::leanh::lean_inc_ref(v___y_3218_);
                    crate::leanh::lean_inc(v___y_3216_);
                    crate::leanh::lean_inc_ref(v___y_3215_);
                    crate::leanh::lean_inc(v___y_3214_);
                    crate::leanh::lean_inc_ref(v___y_3210_);
                    v___x_3244_ = crate::leanh::lean_apply_8(
                        v___y_3209_,
                        v___y_3212_,
                        v___y_3210_,
                        v___y_3214_,
                        v___y_3215_,
                        v___y_3216_,
                        v___y_3218_,
                        v___y_3219_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_3244_) == 0 {
                        v_a_3245_ = crate::leanh::lean_ctor_get(v___x_3244_, 0);
                        v_isSharedCheck_3252_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3244_)) as u8;
                        if v_isSharedCheck_3252_ == 0 {
                            v___x_3247_ = v___x_3244_;
                            v_isShared_3248_ = v_isSharedCheck_3252_;
                            state = 61;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3245_);
                            crate::leanh::lean_dec(v___x_3244_);
                            v___x_3247_ = crate::leanh::lean_box(0);
                            v_isShared_3248_ = v_isSharedCheck_3252_;
                            state = 61;
                            continue;
                        }
                    } else {
                        v_a_3253_ = crate::leanh::lean_ctor_get(v___x_3244_, 0);
                        v_isSharedCheck_3260_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3244_)) as u8;
                        if v_isSharedCheck_3260_ == 0 {
                            v___x_3255_ = v___x_3244_;
                            v_isShared_3256_ = v_isSharedCheck_3260_;
                            state = 63;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3253_);
                            crate::leanh::lean_dec(v___x_3244_);
                            v___x_3255_ = crate::leanh::lean_box(0);
                            v_isShared_3256_ = v_isSharedCheck_3260_;
                            state = 63;
                            continue;
                        }
                    }
                }
            }
            57 => {
                if v_isShared_3230_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3229_, 1);
                    v___x_3232_ = v___x_3229_;
                    state = 58;
                    continue;
                } else {
                    v_reuseFailAlloc_3233_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3233_, 0, v_a_3227_);
                    v___x_3232_ = v_reuseFailAlloc_3233_;
                    state = 58;
                    continue;
                }
            }
            58 => {
                v___y_3180_ = v___y_3207_;
                v___y_3181_ = v___y_3208_;
                v___y_3182_ = v___y_3211_;
                v___y_3183_ = v___y_3210_;
                v___y_3184_ = v___y_3213_;
                v___y_3185_ = v___y_3214_;
                v___y_3186_ = v___y_3215_;
                v___y_3187_ = v___y_3217_;
                v___y_3188_ = v___x_3225_;
                v___y_3189_ = v___y_3216_;
                v___y_3190_ = v___y_3220_;
                v___y_3191_ = v___y_3218_;
                v___y_3192_ = v___y_3219_;
                v___y_3193_ = v_a_3222_;
                v_a_3194_ = v___x_3232_;
                state = 55;
                continue;
            }
            59 => {
                if v_isShared_3238_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3237_, 0);
                    v___x_3240_ = v___x_3237_;
                    state = 60;
                    continue;
                } else {
                    v_reuseFailAlloc_3241_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3241_, 0, v_a_3235_);
                    v___x_3240_ = v_reuseFailAlloc_3241_;
                    state = 60;
                    continue;
                }
            }
            60 => {
                v___y_3180_ = v___y_3207_;
                v___y_3181_ = v___y_3208_;
                v___y_3182_ = v___y_3211_;
                v___y_3183_ = v___y_3210_;
                v___y_3184_ = v___y_3213_;
                v___y_3185_ = v___y_3214_;
                v___y_3186_ = v___y_3215_;
                v___y_3187_ = v___y_3217_;
                v___y_3188_ = v___x_3225_;
                v___y_3189_ = v___y_3216_;
                v___y_3190_ = v___y_3220_;
                v___y_3191_ = v___y_3218_;
                v___y_3192_ = v___y_3219_;
                v___y_3193_ = v_a_3222_;
                v_a_3194_ = v___x_3240_;
                state = 55;
                continue;
            }
            61 => {
                if v_isShared_3248_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3247_, 1);
                    v___x_3250_ = v___x_3247_;
                    state = 62;
                    continue;
                } else {
                    v_reuseFailAlloc_3251_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3251_, 0, v_a_3245_);
                    v___x_3250_ = v_reuseFailAlloc_3251_;
                    state = 62;
                    continue;
                }
            }
            62 => {
                v___y_3156_ = v___y_3207_;
                v___y_3157_ = v___y_3208_;
                v___y_3158_ = v___y_3211_;
                v___y_3159_ = v___y_3210_;
                v___y_3160_ = v___y_3213_;
                v___y_3161_ = v___x_3243_;
                v___y_3162_ = v___y_3214_;
                v___y_3163_ = v___y_3215_;
                v___y_3164_ = v___y_3217_;
                v___y_3165_ = v___y_3216_;
                v___y_3166_ = v___y_3220_;
                v___y_3167_ = v___y_3218_;
                v___y_3168_ = v___y_3219_;
                v___y_3169_ = v_a_3222_;
                v_a_3170_ = v___x_3250_;
                state = 54;
                continue;
            }
            63 => {
                if v_isShared_3256_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3255_, 0);
                    v___x_3258_ = v___x_3255_;
                    state = 64;
                    continue;
                } else {
                    v_reuseFailAlloc_3259_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3259_, 0, v_a_3253_);
                    v___x_3258_ = v_reuseFailAlloc_3259_;
                    state = 64;
                    continue;
                }
            }
            64 => {
                v___y_3156_ = v___y_3207_;
                v___y_3157_ = v___y_3208_;
                v___y_3158_ = v___y_3211_;
                v___y_3159_ = v___y_3210_;
                v___y_3160_ = v___y_3213_;
                v___y_3161_ = v___x_3243_;
                v___y_3162_ = v___y_3214_;
                v___y_3163_ = v___y_3215_;
                v___y_3164_ = v___y_3217_;
                v___y_3165_ = v___y_3216_;
                v___y_3166_ = v___y_3220_;
                v___y_3167_ = v___y_3218_;
                v___y_3168_ = v___y_3219_;
                v___y_3169_ = v_a_3222_;
                v_a_3170_ = v___x_3258_;
                state = 54;
                continue;
            }
            65 => {
                if crate::leanh::lean_obj_tag(v___y_3268_) == 0 {
                    v_a_3269_ = crate::leanh::lean_ctor_get(v___y_3268_, 0);
                    v_isSharedCheck_3295_ = (!crate::leanh::lean_is_exclusive(v___y_3268_)) as u8;
                    if v_isSharedCheck_3295_ == 0 {
                        v___x_3271_ = v___y_3268_;
                        v_isShared_3272_ = v_isSharedCheck_3295_;
                        state = 66;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3269_);
                        crate::leanh::lean_dec(v___y_3268_);
                        v___x_3271_ = crate::leanh::lean_box(0);
                        v_isShared_3272_ = v_isSharedCheck_3295_;
                        state = 66;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2664_);
                    return v___y_3268_;
                }
            }
            66 => {
                if crate::leanh::lean_obj_tag(v_a_3269_) == 1 {
                    crate::leanh::lean_del_object(v___x_3271_);
                    v_structures_3273_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_3267_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 5) as u32,
                    );
                    if v_structures_3273_ == 0 {
                        v_val_3274_ = crate::leanh::lean_ctor_get(v_a_3269_, 0);
                        crate::leanh::lean_inc(v_val_3274_);
                        crate::leanh::lean_dec_ref_known(v_a_3269_, 1);
                        v_fixedInt_3275_ = crate::leanh::lean_ctor_get_uint8(
                            v___y_3267_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 6) as u32,
                        );
                        v_enums_3276_ = crate::leanh::lean_ctor_get_uint8(
                            v___y_3267_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 7) as u32,
                        );
                        v___y_3111_ = v___y_3267_;
                        v_fixedInt_3112_ = v_fixedInt_3275_;
                        v_enums_3113_ = v_enums_3276_;
                        v_g_3114_ = v_val_3274_;
                        v___y_3115_ = v___y_3267_;
                        v___y_3116_ = v___y_3266_;
                        v___y_3117_ = v___y_3265_;
                        v___y_3118_ = v___y_3262_;
                        v___y_3119_ = v___y_3264_;
                        v___y_3120_ = v___y_3263_;
                        state = 50;
                        continue;
                    } else {
                        v_val_3277_ = crate::leanh::lean_ctor_get(v_a_3269_, 0);
                        crate::leanh::lean_inc(v_val_3277_);
                        crate::leanh::lean_dec_ref_known(v_a_3269_, 1);
                        v___x_3278_ = l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass;
                        v_options_3279_ = crate::leanh::lean_ctor_get(v___y_3264_, 2);
                        v_hasTrace_3280_ = crate::leanh::lean_ctor_get_uint8(
                            v_options_3279_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        );
                        if v_hasTrace_3280_ == 0 {
                            v_run_x27_3281_ = crate::leanh::lean_ctor_get(v___x_3278_, 1);
                            crate::leanh::lean_inc_ref(v_run_x27_3281_);
                            crate::leanh::lean_inc(v___y_3263_);
                            crate::leanh::lean_inc_ref(v___y_3264_);
                            crate::leanh::lean_inc(v___y_3262_);
                            crate::leanh::lean_inc_ref(v___y_3265_);
                            crate::leanh::lean_inc(v___y_3266_);
                            crate::leanh::lean_inc_ref(v___y_3267_);
                            v___x_3282_ = crate::leanh::lean_apply_8(
                                v_run_x27_3281_,
                                v_val_3277_,
                                v___y_3267_,
                                v___y_3266_,
                                v___y_3265_,
                                v___y_3262_,
                                v___y_3264_,
                                v___y_3263_,
                                crate::leanh::lean_box(0),
                            );
                            v___y_3136_ = v___y_3263_;
                            v___y_3137_ = v___y_3264_;
                            v___y_3138_ = v___y_3267_;
                            v___y_3139_ = v___y_3265_;
                            v___y_3140_ = v___y_3266_;
                            v___y_3141_ = v___y_3267_;
                            v___y_3142_ = v___y_3262_;
                            v___y_3143_ = v___x_3282_;
                            state = 51;
                            continue;
                        } else {
                            v_run_x27_3283_ = crate::leanh::lean_ctor_get(v___x_3278_, 1);
                            v_inheritedTraceOptions_3284_ =
                                crate::leanh::lean_ctor_get(v___y_3264_, 13);
                            crate::leanh::lean_inc(v_val_3277_);
                            v___f_3285_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___boxed as *mut core::ffi::c_void, 10, 2);
                            crate::leanh::lean_closure_set(v___f_3285_, 0, v___x_3278_);
                            crate::leanh::lean_closure_set(v___f_3285_, 1, v_val_3277_);
                            v___x_3286_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__1;
                            v___x_3287_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7);
                            v___x_3288_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                v_inheritedTraceOptions_3284_,
                                v_options_3279_,
                                v___x_3287_,
                            );
                            if v___x_3288_ == 0 {
                                v___x_3289_ = l_Lean_trace_profiler;
                                v___x_3290_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__1(v_options_3279_, v___x_3289_);
                                if v___x_3290_ == 0 {
                                    crate::leanh::lean_dec_ref(v___f_3285_);
                                    crate::leanh::lean_inc_ref(v_run_x27_3283_);
                                    crate::leanh::lean_inc(v___y_3263_);
                                    crate::leanh::lean_inc_ref(v___y_3264_);
                                    crate::leanh::lean_inc(v___y_3262_);
                                    crate::leanh::lean_inc_ref(v___y_3265_);
                                    crate::leanh::lean_inc(v___y_3266_);
                                    crate::leanh::lean_inc_ref(v___y_3267_);
                                    v___x_3291_ = crate::leanh::lean_apply_8(
                                        v_run_x27_3283_,
                                        v_val_3277_,
                                        v___y_3267_,
                                        v___y_3266_,
                                        v___y_3265_,
                                        v___y_3262_,
                                        v___y_3264_,
                                        v___y_3263_,
                                        crate::leanh::lean_box(0),
                                    );
                                    v___y_3136_ = v___y_3263_;
                                    v___y_3137_ = v___y_3264_;
                                    v___y_3138_ = v___y_3267_;
                                    v___y_3139_ = v___y_3265_;
                                    v___y_3140_ = v___y_3266_;
                                    v___y_3141_ = v___y_3267_;
                                    v___y_3142_ = v___y_3262_;
                                    v___y_3143_ = v___x_3291_;
                                    state = 51;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc_ref(v_run_x27_3283_);
                                    v___y_3207_ = v___x_3286_;
                                    v___y_3208_ = v___f_3285_;
                                    v___y_3209_ = v_run_x27_3283_;
                                    v___y_3210_ = v___y_3267_;
                                    v___y_3211_ = v_hasTrace_3280_;
                                    v___y_3212_ = v_val_3277_;
                                    v___y_3213_ = v_options_3279_;
                                    v___y_3214_ = v___y_3266_;
                                    v___y_3215_ = v___y_3265_;
                                    v___y_3216_ = v___y_3262_;
                                    v___y_3217_ = v___y_3267_;
                                    v___y_3218_ = v___y_3264_;
                                    v___y_3219_ = v___y_3263_;
                                    v___y_3220_ = v___x_3288_;
                                    state = 56;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_inc_ref(v_run_x27_3283_);
                                v___y_3207_ = v___x_3286_;
                                v___y_3208_ = v___f_3285_;
                                v___y_3209_ = v_run_x27_3283_;
                                v___y_3210_ = v___y_3267_;
                                v___y_3211_ = v_hasTrace_3280_;
                                v___y_3212_ = v_val_3277_;
                                v___y_3213_ = v_options_3279_;
                                v___y_3214_ = v___y_3266_;
                                v___y_3215_ = v___y_3265_;
                                v___y_3216_ = v___y_3262_;
                                v___y_3217_ = v___y_3267_;
                                v___y_3218_ = v___y_3264_;
                                v___y_3219_ = v___y_3263_;
                                v___y_3220_ = v___x_3288_;
                                state = 56;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3269_);
                    crate::leanh::lean_del_object(v___x_2664_);
                    if v_isShared_3272_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3271_, 0, v___x_2655_);
                        v___x_3293_ = v___x_3271_;
                        state = 67;
                        continue;
                    } else {
                        v_reuseFailAlloc_3294_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3294_, 0, v___x_2655_);
                        v___x_3293_ = v_reuseFailAlloc_3294_;
                        state = 67;
                        continue;
                    }
                }
            }
            67 => {
                return v___x_3293_;
            }
            68 => {
                v___x_3311_ = lean_io_get_num_heartbeats();
                v___x_3312_ = lean_float_of_nat(v___y_3302_);
                v___x_3313_ = lean_float_of_nat(v___x_3311_);
                v___x_3314_ = crate::leanh::lean_box_float(v___x_3312_);
                v___x_3315_ = crate::leanh::lean_box_float(v___x_3313_);
                v___x_3316_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3316_, 0, v___x_3314_);
                crate::leanh::lean_ctor_set(v___x_3316_, 1, v___x_3315_);
                v___x_3317_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3317_, 0, v_a_3310_);
                crate::leanh::lean_ctor_set(v___x_3317_, 1, v___x_3316_);
                crate::leanh::lean_inc_ref(v___y_3301_);
                v___x_3318_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2(v___x_2668_, v___y_3305_, v___y_3301_, v___y_3298_, v___y_3308_, v___y_3304_, v___y_3309_, v___x_3317_, v___y_3303_, v___y_3307_, v___y_3306_, v___y_3297_, v___y_3300_, v___y_3299_);
                v___y_3262_ = v___y_3297_;
                v___y_3263_ = v___y_3299_;
                v___y_3264_ = v___y_3300_;
                v___y_3265_ = v___y_3306_;
                v___y_3266_ = v___y_3307_;
                v___y_3267_ = v___y_3303_;
                v___y_3268_ = v___x_3318_;
                state = 65;
                continue;
            }
            69 => {
                v___x_3334_ = lean_io_mono_nanos_now();
                v___x_3335_ = lean_float_of_nat(v___y_3326_);
                v___x_3336_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__4_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__4);
                v___x_3337_ = lean_float_div(v___x_3335_, v___x_3336_);
                v___x_3338_ = lean_float_of_nat(v___x_3334_);
                v___x_3339_ = lean_float_div(v___x_3338_, v___x_3336_);
                v___x_3340_ = crate::leanh::lean_box_float(v___x_3337_);
                v___x_3341_ = crate::leanh::lean_box_float(v___x_3339_);
                v___x_3342_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3342_, 0, v___x_3340_);
                crate::leanh::lean_ctor_set(v___x_3342_, 1, v___x_3341_);
                v___x_3343_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3343_, 0, v_a_3333_);
                crate::leanh::lean_ctor_set(v___x_3343_, 1, v___x_3342_);
                crate::leanh::lean_inc_ref(v___y_3324_);
                v___x_3344_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2(v___x_2668_, v___y_3328_, v___y_3324_, v___y_3321_, v___y_3331_, v___y_3327_, v___y_3332_, v___x_3343_, v___y_3325_, v___y_3330_, v___y_3329_, v___y_3320_, v___y_3323_, v___y_3322_);
                v___y_3262_ = v___y_3320_;
                v___y_3263_ = v___y_3322_;
                v___y_3264_ = v___y_3323_;
                v___y_3265_ = v___y_3329_;
                v___y_3266_ = v___y_3330_;
                v___y_3267_ = v___y_3325_;
                v___y_3268_ = v___x_3344_;
                state = 65;
                continue;
            }
            70 => {
                v___x_3358_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___redArg(v___y_3348_);
                v_a_3359_ = crate::leanh::lean_ctor_get(v___x_3358_, 0);
                crate::leanh::lean_inc(v_a_3359_);
                crate::leanh::lean_dec_ref(v___x_3358_);
                v___x_3360_ = l_Lean_trace_profiler_useHeartbeats;
                v___x_3361_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__1(v___y_3347_, v___x_3360_);
                if v___x_3361_ == 0 {
                    v___x_3362_ = lean_io_mono_nanos_now();
                    crate::leanh::lean_inc(v___y_3348_);
                    crate::leanh::lean_inc_ref(v___y_3349_);
                    crate::leanh::lean_inc(v___y_3346_);
                    crate::leanh::lean_inc_ref(v___y_3354_);
                    crate::leanh::lean_inc(v___y_3355_);
                    crate::leanh::lean_inc_ref(v___y_3351_);
                    v___x_3363_ = crate::leanh::lean_apply_8(
                        v___y_3353_,
                        v_val_2662_,
                        v___y_3351_,
                        v___y_3355_,
                        v___y_3354_,
                        v___y_3346_,
                        v___y_3349_,
                        v___y_3348_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_3363_) == 0 {
                        v_a_3364_ = crate::leanh::lean_ctor_get(v___x_3363_, 0);
                        v_isSharedCheck_3371_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3363_)) as u8;
                        if v_isSharedCheck_3371_ == 0 {
                            v___x_3366_ = v___x_3363_;
                            v_isShared_3367_ = v_isSharedCheck_3371_;
                            state = 71;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3364_);
                            crate::leanh::lean_dec(v___x_3363_);
                            v___x_3366_ = crate::leanh::lean_box(0);
                            v_isShared_3367_ = v_isSharedCheck_3371_;
                            state = 71;
                            continue;
                        }
                    } else {
                        v_a_3372_ = crate::leanh::lean_ctor_get(v___x_3363_, 0);
                        v_isSharedCheck_3379_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3363_)) as u8;
                        if v_isSharedCheck_3379_ == 0 {
                            v___x_3374_ = v___x_3363_;
                            v_isShared_3375_ = v_isSharedCheck_3379_;
                            state = 73;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3372_);
                            crate::leanh::lean_dec(v___x_3363_);
                            v___x_3374_ = crate::leanh::lean_box(0);
                            v_isShared_3375_ = v_isSharedCheck_3379_;
                            state = 73;
                            continue;
                        }
                    }
                } else {
                    v___x_3380_ = lean_io_get_num_heartbeats();
                    crate::leanh::lean_inc(v___y_3348_);
                    crate::leanh::lean_inc_ref(v___y_3349_);
                    crate::leanh::lean_inc(v___y_3346_);
                    crate::leanh::lean_inc_ref(v___y_3354_);
                    crate::leanh::lean_inc(v___y_3355_);
                    crate::leanh::lean_inc_ref(v___y_3351_);
                    v___x_3381_ = crate::leanh::lean_apply_8(
                        v___y_3353_,
                        v_val_2662_,
                        v___y_3351_,
                        v___y_3355_,
                        v___y_3354_,
                        v___y_3346_,
                        v___y_3349_,
                        v___y_3348_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_3381_) == 0 {
                        v_a_3382_ = crate::leanh::lean_ctor_get(v___x_3381_, 0);
                        v_isSharedCheck_3389_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3381_)) as u8;
                        if v_isSharedCheck_3389_ == 0 {
                            v___x_3384_ = v___x_3381_;
                            v_isShared_3385_ = v_isSharedCheck_3389_;
                            state = 75;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3382_);
                            crate::leanh::lean_dec(v___x_3381_);
                            v___x_3384_ = crate::leanh::lean_box(0);
                            v_isShared_3385_ = v_isSharedCheck_3389_;
                            state = 75;
                            continue;
                        }
                    } else {
                        v_a_3390_ = crate::leanh::lean_ctor_get(v___x_3381_, 0);
                        v_isSharedCheck_3397_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3381_)) as u8;
                        if v_isSharedCheck_3397_ == 0 {
                            v___x_3392_ = v___x_3381_;
                            v_isShared_3393_ = v_isSharedCheck_3397_;
                            state = 77;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3390_);
                            crate::leanh::lean_dec(v___x_3381_);
                            v___x_3392_ = crate::leanh::lean_box(0);
                            v_isShared_3393_ = v_isSharedCheck_3397_;
                            state = 77;
                            continue;
                        }
                    }
                }
            }
            71 => {
                if v_isShared_3367_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3366_, 1);
                    v___x_3369_ = v___x_3366_;
                    state = 72;
                    continue;
                } else {
                    v_reuseFailAlloc_3370_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3370_, 0, v_a_3364_);
                    v___x_3369_ = v_reuseFailAlloc_3370_;
                    state = 72;
                    continue;
                }
            }
            72 => {
                v___y_3320_ = v___y_3346_;
                v___y_3321_ = v___y_3347_;
                v___y_3322_ = v___y_3348_;
                v___y_3323_ = v___y_3349_;
                v___y_3324_ = v___y_3350_;
                v___y_3325_ = v___y_3351_;
                v___y_3326_ = v___x_3362_;
                v___y_3327_ = v_a_3359_;
                v___y_3328_ = v___y_3352_;
                v___y_3329_ = v___y_3354_;
                v___y_3330_ = v___y_3355_;
                v___y_3331_ = v___y_3356_;
                v___y_3332_ = v___y_3357_;
                v_a_3333_ = v___x_3369_;
                state = 69;
                continue;
            }
            73 => {
                if v_isShared_3375_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3374_, 0);
                    v___x_3377_ = v___x_3374_;
                    state = 74;
                    continue;
                } else {
                    v_reuseFailAlloc_3378_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3378_, 0, v_a_3372_);
                    v___x_3377_ = v_reuseFailAlloc_3378_;
                    state = 74;
                    continue;
                }
            }
            74 => {
                v___y_3320_ = v___y_3346_;
                v___y_3321_ = v___y_3347_;
                v___y_3322_ = v___y_3348_;
                v___y_3323_ = v___y_3349_;
                v___y_3324_ = v___y_3350_;
                v___y_3325_ = v___y_3351_;
                v___y_3326_ = v___x_3362_;
                v___y_3327_ = v_a_3359_;
                v___y_3328_ = v___y_3352_;
                v___y_3329_ = v___y_3354_;
                v___y_3330_ = v___y_3355_;
                v___y_3331_ = v___y_3356_;
                v___y_3332_ = v___y_3357_;
                v_a_3333_ = v___x_3377_;
                state = 69;
                continue;
            }
            75 => {
                if v_isShared_3385_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3384_, 1);
                    v___x_3387_ = v___x_3384_;
                    state = 76;
                    continue;
                } else {
                    v_reuseFailAlloc_3388_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3388_, 0, v_a_3382_);
                    v___x_3387_ = v_reuseFailAlloc_3388_;
                    state = 76;
                    continue;
                }
            }
            76 => {
                v___y_3297_ = v___y_3346_;
                v___y_3298_ = v___y_3347_;
                v___y_3299_ = v___y_3348_;
                v___y_3300_ = v___y_3349_;
                v___y_3301_ = v___y_3350_;
                v___y_3302_ = v___x_3380_;
                v___y_3303_ = v___y_3351_;
                v___y_3304_ = v_a_3359_;
                v___y_3305_ = v___y_3352_;
                v___y_3306_ = v___y_3354_;
                v___y_3307_ = v___y_3355_;
                v___y_3308_ = v___y_3356_;
                v___y_3309_ = v___y_3357_;
                v_a_3310_ = v___x_3387_;
                state = 68;
                continue;
            }
            77 => {
                if v_isShared_3393_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3392_, 0);
                    v___x_3395_ = v___x_3392_;
                    state = 78;
                    continue;
                } else {
                    v_reuseFailAlloc_3396_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3396_, 0, v_a_3390_);
                    v___x_3395_ = v_reuseFailAlloc_3396_;
                    state = 78;
                    continue;
                }
            }
            78 => {
                v___y_3297_ = v___y_3346_;
                v___y_3298_ = v___y_3347_;
                v___y_3299_ = v___y_3348_;
                v___y_3300_ = v___y_3349_;
                v___y_3301_ = v___y_3350_;
                v___y_3302_ = v___x_3380_;
                v___y_3303_ = v___y_3351_;
                v___y_3304_ = v_a_3359_;
                v___y_3305_ = v___y_3352_;
                v___y_3306_ = v___y_3354_;
                v___y_3307_ = v___y_3355_;
                v___y_3308_ = v___y_3356_;
                v___y_3309_ = v___y_3357_;
                v_a_3310_ = v___x_3395_;
                state = 68;
                continue;
            }
            79 => {
                v___x_3405_ = l_Lean_Meta_Tactic_BVDecide_Normalize_typeAnalysisPass;
                v_options_3406_ = crate::leanh::lean_ctor_get(v___y_3401_, 2);
                v_hasTrace_3407_ = crate::leanh::lean_ctor_get_uint8(
                    v_options_3406_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                if v_hasTrace_3407_ == 0 {
                    v_run_x27_3408_ = crate::leanh::lean_ctor_get(v___x_3405_, 1);
                    crate::leanh::lean_inc_ref(v_run_x27_3408_);
                    crate::leanh::lean_inc(v___y_3400_);
                    crate::leanh::lean_inc_ref(v___y_3401_);
                    crate::leanh::lean_inc(v___y_3399_);
                    crate::leanh::lean_inc_ref(v___y_3402_);
                    crate::leanh::lean_inc(v___y_3403_);
                    crate::leanh::lean_inc_ref(v___y_3404_);
                    v___x_3409_ = crate::leanh::lean_apply_8(
                        v_run_x27_3408_,
                        v_val_2662_,
                        v___y_3404_,
                        v___y_3403_,
                        v___y_3402_,
                        v___y_3399_,
                        v___y_3401_,
                        v___y_3400_,
                        crate::leanh::lean_box(0),
                    );
                    v___y_3262_ = v___y_3399_;
                    v___y_3263_ = v___y_3400_;
                    v___y_3264_ = v___y_3401_;
                    v___y_3265_ = v___y_3402_;
                    v___y_3266_ = v___y_3403_;
                    v___y_3267_ = v___y_3404_;
                    v___y_3268_ = v___x_3409_;
                    state = 65;
                    continue;
                } else {
                    v_run_x27_3410_ = crate::leanh::lean_ctor_get(v___x_3405_, 1);
                    v_inheritedTraceOptions_3411_ = crate::leanh::lean_ctor_get(v___y_3401_, 13);
                    crate::leanh::lean_inc(v_val_2662_);
                    v___f_3412_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___boxed as *mut core::ffi::c_void, 10, 2);
                    crate::leanh::lean_closure_set(v___f_3412_, 0, v___x_3405_);
                    crate::leanh::lean_closure_set(v___f_3412_, 1, v_val_2662_);
                    v___x_3413_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__1;
                    v___x_3414_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7);
                    v___x_3415_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_3411_,
                        v_options_3406_,
                        v___x_3414_,
                    );
                    if v___x_3415_ == 0 {
                        v___x_3416_ = l_Lean_trace_profiler;
                        v___x_3417_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__1(v_options_3406_, v___x_3416_);
                        if v___x_3417_ == 0 {
                            crate::leanh::lean_dec_ref(v___f_3412_);
                            crate::leanh::lean_inc_ref(v_run_x27_3410_);
                            crate::leanh::lean_inc(v___y_3400_);
                            crate::leanh::lean_inc_ref(v___y_3401_);
                            crate::leanh::lean_inc(v___y_3399_);
                            crate::leanh::lean_inc_ref(v___y_3402_);
                            crate::leanh::lean_inc(v___y_3403_);
                            crate::leanh::lean_inc_ref(v___y_3404_);
                            v___x_3418_ = crate::leanh::lean_apply_8(
                                v_run_x27_3410_,
                                v_val_2662_,
                                v___y_3404_,
                                v___y_3403_,
                                v___y_3402_,
                                v___y_3399_,
                                v___y_3401_,
                                v___y_3400_,
                                crate::leanh::lean_box(0),
                            );
                            v___y_3262_ = v___y_3399_;
                            v___y_3263_ = v___y_3400_;
                            v___y_3264_ = v___y_3401_;
                            v___y_3265_ = v___y_3402_;
                            v___y_3266_ = v___y_3403_;
                            v___y_3267_ = v___y_3404_;
                            v___y_3268_ = v___x_3418_;
                            state = 65;
                            continue;
                        } else {
                            crate::leanh::lean_inc_ref(v_run_x27_3410_);
                            v___y_3346_ = v___y_3399_;
                            v___y_3347_ = v_options_3406_;
                            v___y_3348_ = v___y_3400_;
                            v___y_3349_ = v___y_3401_;
                            v___y_3350_ = v___x_3413_;
                            v___y_3351_ = v___y_3404_;
                            v___y_3352_ = v_hasTrace_3407_;
                            v___y_3353_ = v_run_x27_3410_;
                            v___y_3354_ = v___y_3402_;
                            v___y_3355_ = v___y_3403_;
                            v___y_3356_ = v___x_3415_;
                            v___y_3357_ = v___f_3412_;
                            state = 70;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_inc_ref(v_run_x27_3410_);
                        v___y_3346_ = v___y_3399_;
                        v___y_3347_ = v_options_3406_;
                        v___y_3348_ = v___y_3400_;
                        v___y_3349_ = v___y_3401_;
                        v___y_3350_ = v___x_3413_;
                        v___y_3351_ = v___y_3404_;
                        v___y_3352_ = v_hasTrace_3407_;
                        v___y_3353_ = v_run_x27_3410_;
                        v___y_3354_ = v___y_3402_;
                        v___y_3355_ = v___y_3403_;
                        v___y_3356_ = v___x_3415_;
                        v___y_3357_ = v___f_3412_;
                        state = 70;
                        continue;
                    }
                }
            }
            80 => {
                v_structures_3426_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_3420_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 5) as u32,
                );
                if v_structures_3426_ == 0 {
                    v_enums_3427_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_3420_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 7) as u32,
                    );
                    if v_enums_3427_ == 0 {
                        v_fixedInt_3428_ = crate::leanh::lean_ctor_get_uint8(
                            v___y_3420_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 6) as u32,
                        );
                        v___y_2962_ = v___y_3420_;
                        v_fixedInt_2963_ = v_fixedInt_3428_;
                        v_g_2964_ = v_val_2662_;
                        v___y_2965_ = v___y_3420_;
                        v___y_2966_ = v___y_3421_;
                        v___y_2967_ = v___y_3422_;
                        v___y_2968_ = v___y_3423_;
                        v___y_2969_ = v___y_3424_;
                        v___y_2970_ = v___y_3425_;
                        state = 35;
                        continue;
                    } else {
                        v___y_3399_ = v___y_3423_;
                        v___y_3400_ = v___y_3425_;
                        v___y_3401_ = v___y_3424_;
                        v___y_3402_ = v___y_3422_;
                        v___y_3403_ = v___y_3421_;
                        v___y_3404_ = v___y_3420_;
                        state = 79;
                        continue;
                    }
                } else {
                    v___y_3399_ = v___y_3423_;
                    v___y_3400_ = v___y_3425_;
                    v___y_3401_ = v___y_3424_;
                    v___y_3402_ = v___y_3422_;
                    v___y_3403_ = v___y_3421_;
                    v___y_3404_ = v___y_3420_;
                    state = 79;
                    continue;
                }
            }
            81 => {
                if v_isShared_3438_ == 0 {
                    v___x_3440_ = v___x_3437_;
                    state = 82;
                    continue;
                } else {
                    v_reuseFailAlloc_3441_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3441_, 0, v_a_3435_);
                    v___x_3440_ = v_reuseFailAlloc_3441_;
                    state = 82;
                    continue;
                }
            }
            82 => {
                return v___x_3440_;
            }
            83 => {
                return v___x_3445_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___boxed(
    mut v_g_3448_: *mut crate::leanh::LeanObject,
    mut v_a_3449_: *mut crate::leanh::LeanObject,
    mut v_a_3450_: *mut crate::leanh::LeanObject,
    mut v_a_3451_: *mut crate::leanh::LeanObject,
    mut v_a_3452_: *mut crate::leanh::LeanObject,
    mut v_a_3453_: *mut crate::leanh::LeanObject,
    mut v_a_3454_: *mut crate::leanh::LeanObject,
    mut v_a_3455_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3456_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go(v_g_3448_, v_a_3449_, v_a_3450_, v_a_3451_, v_a_3452_, v_a_3453_, v_a_3454_);
    crate::leanh::lean_dec(v_a_3454_);
    crate::leanh::lean_dec_ref(v_a_3453_);
    crate::leanh::lean_dec(v_a_3452_);
    crate::leanh::lean_dec_ref(v_a_3451_);
    crate::leanh::lean_dec(v_a_3450_);
    crate::leanh::lean_dec_ref(v_a_3449_);
    return v_res_3456_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__4(
    mut v_00_u03b1_3457_: *mut crate::leanh::LeanObject,
    mut v_x_3458_: *mut crate::leanh::LeanObject,
    mut v___y_3459_: *mut crate::leanh::LeanObject,
    mut v___y_3460_: *mut crate::leanh::LeanObject,
    mut v___y_3461_: *mut crate::leanh::LeanObject,
    mut v___y_3462_: *mut crate::leanh::LeanObject,
    mut v___y_3463_: *mut crate::leanh::LeanObject,
    mut v___y_3464_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3466_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__4___redArg(v_x_3458_);
    return v___x_3466_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__4___boxed(
    mut v_00_u03b1_3467_: *mut crate::leanh::LeanObject,
    mut v_x_3468_: *mut crate::leanh::LeanObject,
    mut v___y_3469_: *mut crate::leanh::LeanObject,
    mut v___y_3470_: *mut crate::leanh::LeanObject,
    mut v___y_3471_: *mut crate::leanh::LeanObject,
    mut v___y_3472_: *mut crate::leanh::LeanObject,
    mut v___y_3473_: *mut crate::leanh::LeanObject,
    mut v___y_3474_: *mut crate::leanh::LeanObject,
    mut v___y_3475_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3476_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__4(v_00_u03b1_3467_, v_x_3468_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_);
    crate::leanh::lean_dec(v___y_3474_);
    crate::leanh::lean_dec_ref(v___y_3473_);
    crate::leanh::lean_dec(v___y_3472_);
    crate::leanh::lean_dec_ref(v___y_3471_);
    crate::leanh::lean_dec(v___y_3470_);
    crate::leanh::lean_dec_ref(v___y_3469_);
    return v_res_3476_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3(
    mut v_cls_3477_: *mut crate::leanh::LeanObject,
    mut v_msg_3478_: *mut crate::leanh::LeanObject,
    mut v___y_3479_: *mut crate::leanh::LeanObject,
    mut v___y_3480_: *mut crate::leanh::LeanObject,
    mut v___y_3481_: *mut crate::leanh::LeanObject,
    mut v___y_3482_: *mut crate::leanh::LeanObject,
    mut v___y_3483_: *mut crate::leanh::LeanObject,
    mut v___y_3484_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3486_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg(v_cls_3477_, v_msg_3478_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_);
    return v___x_3486_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___boxed(
    mut v_cls_3487_: *mut crate::leanh::LeanObject,
    mut v_msg_3488_: *mut crate::leanh::LeanObject,
    mut v___y_3489_: *mut crate::leanh::LeanObject,
    mut v___y_3490_: *mut crate::leanh::LeanObject,
    mut v___y_3491_: *mut crate::leanh::LeanObject,
    mut v___y_3492_: *mut crate::leanh::LeanObject,
    mut v___y_3493_: *mut crate::leanh::LeanObject,
    mut v___y_3494_: *mut crate::leanh::LeanObject,
    mut v___y_3495_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3496_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3(v_cls_3487_, v_msg_3488_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_);
    crate::leanh::lean_dec(v___y_3494_);
    crate::leanh::lean_dec_ref(v___y_3493_);
    crate::leanh::lean_dec(v___y_3492_);
    crate::leanh::lean_dec_ref(v___y_3491_);
    crate::leanh::lean_dec(v___y_3490_);
    crate::leanh::lean_dec_ref(v___y_3489_);
    return v_res_3496_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__3(
    mut v_oldTraces_3497_: *mut crate::leanh::LeanObject,
    mut v_data_3498_: *mut crate::leanh::LeanObject,
    mut v_ref_3499_: *mut crate::leanh::LeanObject,
    mut v_msg_3500_: *mut crate::leanh::LeanObject,
    mut v___y_3501_: *mut crate::leanh::LeanObject,
    mut v___y_3502_: *mut crate::leanh::LeanObject,
    mut v___y_3503_: *mut crate::leanh::LeanObject,
    mut v___y_3504_: *mut crate::leanh::LeanObject,
    mut v___y_3505_: *mut crate::leanh::LeanObject,
    mut v___y_3506_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3508_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__3___redArg(v_oldTraces_3497_, v_data_3498_, v_ref_3499_, v_msg_3500_, v___y_3503_, v___y_3504_, v___y_3505_, v___y_3506_);
    return v___x_3508_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__3___boxed(
    mut v_oldTraces_3509_: *mut crate::leanh::LeanObject,
    mut v_data_3510_: *mut crate::leanh::LeanObject,
    mut v_ref_3511_: *mut crate::leanh::LeanObject,
    mut v_msg_3512_: *mut crate::leanh::LeanObject,
    mut v___y_3513_: *mut crate::leanh::LeanObject,
    mut v___y_3514_: *mut crate::leanh::LeanObject,
    mut v___y_3515_: *mut crate::leanh::LeanObject,
    mut v___y_3516_: *mut crate::leanh::LeanObject,
    mut v___y_3517_: *mut crate::leanh::LeanObject,
    mut v___y_3518_: *mut crate::leanh::LeanObject,
    mut v___y_3519_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3520_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__3(v_oldTraces_3509_, v_data_3510_, v_ref_3511_, v_msg_3512_, v___y_3513_, v___y_3514_, v___y_3515_, v___y_3516_, v___y_3517_, v___y_3518_);
    crate::leanh::lean_dec(v___y_3518_);
    crate::leanh::lean_dec_ref(v___y_3517_);
    crate::leanh::lean_dec(v___y_3516_);
    crate::leanh::lean_dec_ref(v___y_3515_);
    crate::leanh::lean_dec(v___y_3514_);
    crate::leanh::lean_dec_ref(v___y_3513_);
    return v_res_3520_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg(
    mut v_mvarId_3521_: *mut crate::leanh::LeanObject,
    mut v_x_3522_: *mut crate::leanh::LeanObject,
    mut v___y_3523_: *mut crate::leanh::LeanObject,
    mut v___y_3524_: *mut crate::leanh::LeanObject,
    mut v___y_3525_: *mut crate::leanh::LeanObject,
    mut v___y_3526_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3532_: u8 = 0;
    let mut v___x_3534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3536_: u8 = 0;
    let mut v_a_3537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3540_: u8 = 0;
    let mut v___x_3542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3544_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3528_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    crate::leanh::lean_box(0),
                    v_mvarId_3521_,
                    v_x_3522_,
                    v___y_3523_,
                    v___y_3524_,
                    v___y_3525_,
                    v___y_3526_,
                );
                if crate::leanh::lean_obj_tag(v___x_3528_) == 0 {
                    v_a_3529_ = crate::leanh::lean_ctor_get(v___x_3528_, 0);
                    v_isSharedCheck_3536_ = (!crate::leanh::lean_is_exclusive(v___x_3528_)) as u8;
                    if v_isSharedCheck_3536_ == 0 {
                        v___x_3531_ = v___x_3528_;
                        v_isShared_3532_ = v_isSharedCheck_3536_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3529_);
                        crate::leanh::lean_dec(v___x_3528_);
                        v___x_3531_ = crate::leanh::lean_box(0);
                        v_isShared_3532_ = v_isSharedCheck_3536_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3537_ = crate::leanh::lean_ctor_get(v___x_3528_, 0);
                    v_isSharedCheck_3544_ = (!crate::leanh::lean_is_exclusive(v___x_3528_)) as u8;
                    if v_isSharedCheck_3544_ == 0 {
                        v___x_3539_ = v___x_3528_;
                        v_isShared_3540_ = v_isSharedCheck_3544_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3537_);
                        crate::leanh::lean_dec(v___x_3528_);
                        v___x_3539_ = crate::leanh::lean_box(0);
                        v_isShared_3540_ = v_isSharedCheck_3544_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3532_ == 0 {
                    v___x_3534_ = v___x_3531_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3535_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3535_, 0, v_a_3529_);
                    v___x_3534_ = v_reuseFailAlloc_3535_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3534_;
            }
            3 => {
                if v_isShared_3540_ == 0 {
                    v___x_3542_ = v___x_3539_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3543_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3543_, 0, v_a_3537_);
                    v___x_3542_ = v_reuseFailAlloc_3543_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3542_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg___boxed(
    mut v_mvarId_3545_: *mut crate::leanh::LeanObject,
    mut v_x_3546_: *mut crate::leanh::LeanObject,
    mut v___y_3547_: *mut crate::leanh::LeanObject,
    mut v___y_3548_: *mut crate::leanh::LeanObject,
    mut v___y_3549_: *mut crate::leanh::LeanObject,
    mut v___y_3550_: *mut crate::leanh::LeanObject,
    mut v___y_3551_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3552_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg(v_mvarId_3545_, v_x_3546_, v___y_3547_, v___y_3548_, v___y_3549_, v___y_3550_);
    crate::leanh::lean_dec(v___y_3550_);
    crate::leanh::lean_dec_ref(v___y_3549_);
    crate::leanh::lean_dec(v___y_3548_);
    crate::leanh::lean_dec_ref(v___y_3547_);
    return v_res_3552_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0(
    mut v_00_u03b1_3553_: *mut crate::leanh::LeanObject,
    mut v_mvarId_3554_: *mut crate::leanh::LeanObject,
    mut v_x_3555_: *mut crate::leanh::LeanObject,
    mut v___y_3556_: *mut crate::leanh::LeanObject,
    mut v___y_3557_: *mut crate::leanh::LeanObject,
    mut v___y_3558_: *mut crate::leanh::LeanObject,
    mut v___y_3559_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3561_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg(v_mvarId_3554_, v_x_3555_, v___y_3556_, v___y_3557_, v___y_3558_, v___y_3559_);
    return v___x_3561_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___boxed(
    mut v_00_u03b1_3562_: *mut crate::leanh::LeanObject,
    mut v_mvarId_3563_: *mut crate::leanh::LeanObject,
    mut v_x_3564_: *mut crate::leanh::LeanObject,
    mut v___y_3565_: *mut crate::leanh::LeanObject,
    mut v___y_3566_: *mut crate::leanh::LeanObject,
    mut v___y_3567_: *mut crate::leanh::LeanObject,
    mut v___y_3568_: *mut crate::leanh::LeanObject,
    mut v___y_3569_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3570_ =
        l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0(
            v_00_u03b1_3562_,
            v_mvarId_3563_,
            v_x_3564_,
            v___y_3565_,
            v___y_3566_,
            v___y_3567_,
            v___y_3568_,
        );
    crate::leanh::lean_dec(v___y_3568_);
    crate::leanh::lean_dec_ref(v___y_3567_);
    crate::leanh::lean_dec(v___y_3566_);
    crate::leanh::lean_dec_ref(v___y_3565_);
    return v_res_3570_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1___redArg(
    mut v___y_3571_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traces_3575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3588_: u8 = 0;
    let mut v_tid_3589_: u64 = 0;
    let mut v___x_3591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3592_: u8 = 0;
    let mut v___x_3593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3604_: u8 = 0;
    let mut v_unused_3605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3606_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3573_ = lean_st_ref_get(v___y_3571_);
                v_traceState_3574_ = crate::leanh::lean_ctor_get(v___x_3573_, 4);
                crate::leanh::lean_inc_ref(v_traceState_3574_);
                crate::leanh::lean_dec(v___x_3573_);
                v_traces_3575_ = crate::leanh::lean_ctor_get(v_traceState_3574_, 0);
                crate::leanh::lean_inc_ref(v_traces_3575_);
                crate::leanh::lean_dec_ref(v_traceState_3574_);
                v___x_3576_ = lean_st_ref_take(v___y_3571_);
                v_traceState_3577_ = crate::leanh::lean_ctor_get(v___x_3576_, 4);
                v_env_3578_ = crate::leanh::lean_ctor_get(v___x_3576_, 0);
                v_nextMacroScope_3579_ = crate::leanh::lean_ctor_get(v___x_3576_, 1);
                v_ngen_3580_ = crate::leanh::lean_ctor_get(v___x_3576_, 2);
                v_auxDeclNGen_3581_ = crate::leanh::lean_ctor_get(v___x_3576_, 3);
                v_cache_3582_ = crate::leanh::lean_ctor_get(v___x_3576_, 5);
                v_messages_3583_ = crate::leanh::lean_ctor_get(v___x_3576_, 6);
                v_infoState_3584_ = crate::leanh::lean_ctor_get(v___x_3576_, 7);
                v_snapshotTasks_3585_ = crate::leanh::lean_ctor_get(v___x_3576_, 8);
                v_isSharedCheck_3606_ = (!crate::leanh::lean_is_exclusive(v___x_3576_)) as u8;
                if v_isSharedCheck_3606_ == 0 {
                    v___x_3587_ = v___x_3576_;
                    v_isShared_3588_ = v_isSharedCheck_3606_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_3585_);
                    crate::leanh::lean_inc(v_infoState_3584_);
                    crate::leanh::lean_inc(v_messages_3583_);
                    crate::leanh::lean_inc(v_cache_3582_);
                    crate::leanh::lean_inc(v_traceState_3577_);
                    crate::leanh::lean_inc(v_auxDeclNGen_3581_);
                    crate::leanh::lean_inc(v_ngen_3580_);
                    crate::leanh::lean_inc(v_nextMacroScope_3579_);
                    crate::leanh::lean_inc(v_env_3578_);
                    crate::leanh::lean_dec(v___x_3576_);
                    v___x_3587_ = crate::leanh::lean_box(0);
                    v_isShared_3588_ = v_isSharedCheck_3606_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_tid_3589_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_3577_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_3604_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_3577_)) as u8;
                if v_isSharedCheck_3604_ == 0 {
                    v_unused_3605_ = crate::leanh::lean_ctor_get(v_traceState_3577_, 0);
                    crate::leanh::lean_dec(v_unused_3605_);
                    v___x_3591_ = v_traceState_3577_;
                    v_isShared_3592_ = v_isSharedCheck_3604_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_traceState_3577_);
                    v___x_3591_ = crate::leanh::lean_box(0);
                    v_isShared_3592_ = v_isSharedCheck_3604_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3593_ = crate::leanh::lean_unsigned_to_nat(32);
                v___x_3594_ = lean_mk_empty_array_with_capacity(v___x_3593_);
                crate::leanh::lean_dec_ref(v___x_3594_);
                v___x_3595_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___redArg___closed__1_once), _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___redArg___closed__1);
                if v_isShared_3592_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3591_, 0, v___x_3595_);
                    v___x_3597_ = v___x_3591_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3603_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3603_, 0, v___x_3595_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_3603_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_3589_,
                    );
                    v___x_3597_ = v_reuseFailAlloc_3603_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3588_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3587_, 4, v___x_3597_);
                    v___x_3599_ = v___x_3587_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3602_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3602_, 0, v_env_3578_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3602_, 1, v_nextMacroScope_3579_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3602_, 2, v_ngen_3580_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3602_, 3, v_auxDeclNGen_3581_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3602_, 4, v___x_3597_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3602_, 5, v_cache_3582_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3602_, 6, v_messages_3583_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3602_, 7, v_infoState_3584_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3602_, 8, v_snapshotTasks_3585_);
                    v___x_3599_ = v_reuseFailAlloc_3602_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3600_ = lean_st_ref_set(v___y_3571_, v___x_3599_);
                v___x_3601_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3601_, 0, v_traces_3575_);
                return v___x_3601_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1___redArg___boxed(
    mut v___y_3607_: *mut crate::leanh::LeanObject,
    mut v___y_3608_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3609_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1___redArg(v___y_3607_);
    crate::leanh::lean_dec(v___y_3607_);
    return v_res_3609_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(
    mut v___y_3610_: *mut crate::leanh::LeanObject,
    mut v___y_3611_: *mut crate::leanh::LeanObject,
    mut v___y_3612_: *mut crate::leanh::LeanObject,
    mut v___y_3613_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3615_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1___redArg(v___y_3613_);
    return v___x_3615_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1___boxed(
    mut v___y_3616_: *mut crate::leanh::LeanObject,
    mut v___y_3617_: *mut crate::leanh::LeanObject,
    mut v___y_3618_: *mut crate::leanh::LeanObject,
    mut v___y_3619_: *mut crate::leanh::LeanObject,
    mut v___y_3620_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3621_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v___y_3616_, v___y_3617_, v___y_3618_, v___y_3619_);
    crate::leanh::lean_dec(v___y_3619_);
    crate::leanh::lean_dec_ref(v___y_3618_);
    crate::leanh::lean_dec(v___y_3617_);
    crate::leanh::lean_dec_ref(v___y_3616_);
    return v_res_3621_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3625_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___closed__1;
    v___x_3626_ = l_Lean_MessageData_ofFormat(v___x_3625_);
    return v___x_3626_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0(
    mut v_x_3627_: *mut crate::leanh::LeanObject,
    mut v___y_3628_: *mut crate::leanh::LeanObject,
    mut v___y_3629_: *mut crate::leanh::LeanObject,
    mut v___y_3630_: *mut crate::leanh::LeanObject,
    mut v___y_3631_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3633_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___closed__2_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___closed__2,
    );
    v___x_3634_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3634_, 0, v___x_3633_);
    return v___x_3634_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___boxed(
    mut v_x_3635_: *mut crate::leanh::LeanObject,
    mut v___y_3636_: *mut crate::leanh::LeanObject,
    mut v___y_3637_: *mut crate::leanh::LeanObject,
    mut v___y_3638_: *mut crate::leanh::LeanObject,
    mut v___y_3639_: *mut crate::leanh::LeanObject,
    mut v___y_3640_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3641_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0(
        v_x_3635_,
        v___y_3636_,
        v___y_3637_,
        v___y_3638_,
        v___y_3639_,
    );
    crate::leanh::lean_dec(v___y_3639_);
    crate::leanh::lean_dec_ref(v___y_3638_);
    crate::leanh::lean_dec(v___y_3637_);
    crate::leanh::lean_dec_ref(v___y_3636_);
    crate::leanh::lean_dec_ref(v_x_3635_);
    return v_res_3641_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__2(
    mut v_oldTraces_3642_: *mut crate::leanh::LeanObject,
    mut v_data_3643_: *mut crate::leanh::LeanObject,
    mut v_ref_3644_: *mut crate::leanh::LeanObject,
    mut v_msg_3645_: *mut crate::leanh::LeanObject,
    mut v___y_3646_: *mut crate::leanh::LeanObject,
    mut v___y_3647_: *mut crate::leanh::LeanObject,
    mut v___y_3648_: *mut crate::leanh::LeanObject,
    mut v___y_3649_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_3651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_3655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_3659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3663_: u8 = 0;
    let mut v_cancelTk_x3f_3664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3665_: u8 = 0;
    let mut v_inheritedTraceOptions_3666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traces_3669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3673_: usize = 0;
    let mut v___x_3674_: usize = 0;
    let mut v___x_3675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_3676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3681_: u8 = 0;
    let mut v___x_3682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3694_: u8 = 0;
    let mut v_tid_3695_: u64 = 0;
    let mut v___x_3697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3698_: u8 = 0;
    let mut v___x_3699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3712_: u8 = 0;
    let mut v_unused_3713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3714_: u8 = 0;
    let mut v_isSharedCheck_3715_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_3651_ = crate::leanh::lean_ctor_get(v___y_3648_, 0);
                v_fileMap_3652_ = crate::leanh::lean_ctor_get(v___y_3648_, 1);
                v_options_3653_ = crate::leanh::lean_ctor_get(v___y_3648_, 2);
                v_currRecDepth_3654_ = crate::leanh::lean_ctor_get(v___y_3648_, 3);
                v_maxRecDepth_3655_ = crate::leanh::lean_ctor_get(v___y_3648_, 4);
                v_ref_3656_ = crate::leanh::lean_ctor_get(v___y_3648_, 5);
                v_currNamespace_3657_ = crate::leanh::lean_ctor_get(v___y_3648_, 6);
                v_openDecls_3658_ = crate::leanh::lean_ctor_get(v___y_3648_, 7);
                v_initHeartbeats_3659_ = crate::leanh::lean_ctor_get(v___y_3648_, 8);
                v_maxHeartbeats_3660_ = crate::leanh::lean_ctor_get(v___y_3648_, 9);
                v_quotContext_3661_ = crate::leanh::lean_ctor_get(v___y_3648_, 10);
                v_currMacroScope_3662_ = crate::leanh::lean_ctor_get(v___y_3648_, 11);
                v_diag_3663_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_3648_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_3664_ = crate::leanh::lean_ctor_get(v___y_3648_, 12);
                v_suppressElabErrors_3665_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_3648_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_3666_ = crate::leanh::lean_ctor_get(v___y_3648_, 13);
                v___x_3667_ = lean_st_ref_get(v___y_3649_);
                v_traceState_3668_ = crate::leanh::lean_ctor_get(v___x_3667_, 4);
                crate::leanh::lean_inc_ref(v_traceState_3668_);
                crate::leanh::lean_dec(v___x_3667_);
                v_traces_3669_ = crate::leanh::lean_ctor_get(v_traceState_3668_, 0);
                crate::leanh::lean_inc_ref(v_traces_3669_);
                crate::leanh::lean_dec_ref(v_traceState_3668_);
                v_ref_3670_ = l_Lean_replaceRef(v_ref_3644_, v_ref_3656_);
                crate::leanh::lean_inc_ref(v_inheritedTraceOptions_3666_);
                crate::leanh::lean_inc(v_cancelTk_x3f_3664_);
                crate::leanh::lean_inc(v_currMacroScope_3662_);
                crate::leanh::lean_inc(v_quotContext_3661_);
                crate::leanh::lean_inc(v_maxHeartbeats_3660_);
                crate::leanh::lean_inc(v_initHeartbeats_3659_);
                crate::leanh::lean_inc(v_openDecls_3658_);
                crate::leanh::lean_inc(v_currNamespace_3657_);
                crate::leanh::lean_inc(v_maxRecDepth_3655_);
                crate::leanh::lean_inc(v_currRecDepth_3654_);
                crate::leanh::lean_inc_ref(v_options_3653_);
                crate::leanh::lean_inc_ref(v_fileMap_3652_);
                crate::leanh::lean_inc_ref(v_fileName_3651_);
                v___x_3671_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_3671_, 0, v_fileName_3651_);
                crate::leanh::lean_ctor_set(v___x_3671_, 1, v_fileMap_3652_);
                crate::leanh::lean_ctor_set(v___x_3671_, 2, v_options_3653_);
                crate::leanh::lean_ctor_set(v___x_3671_, 3, v_currRecDepth_3654_);
                crate::leanh::lean_ctor_set(v___x_3671_, 4, v_maxRecDepth_3655_);
                crate::leanh::lean_ctor_set(v___x_3671_, 5, v_ref_3670_);
                crate::leanh::lean_ctor_set(v___x_3671_, 6, v_currNamespace_3657_);
                crate::leanh::lean_ctor_set(v___x_3671_, 7, v_openDecls_3658_);
                crate::leanh::lean_ctor_set(v___x_3671_, 8, v_initHeartbeats_3659_);
                crate::leanh::lean_ctor_set(v___x_3671_, 9, v_maxHeartbeats_3660_);
                crate::leanh::lean_ctor_set(v___x_3671_, 10, v_quotContext_3661_);
                crate::leanh::lean_ctor_set(v___x_3671_, 11, v_currMacroScope_3662_);
                crate::leanh::lean_ctor_set(v___x_3671_, 12, v_cancelTk_x3f_3664_);
                crate::leanh::lean_ctor_set(v___x_3671_, 13, v_inheritedTraceOptions_3666_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3671_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                    v_diag_3663_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3671_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_3665_,
                );
                v___x_3672_ = l_Lean_PersistentArray_toArray___redArg(v_traces_3669_);
                crate::leanh::lean_dec_ref(v_traces_3669_);
                v_sz_3673_ = lean_array_size(v___x_3672_);
                v___x_3674_ = 0usize;
                v___x_3675_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__3_spec__4(v_sz_3673_, v___x_3674_, v___x_3672_);
                v_msg_3676_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v_msg_3676_, 0, v_data_3643_);
                crate::leanh::lean_ctor_set(v_msg_3676_, 1, v_msg_3645_);
                crate::leanh::lean_ctor_set(v_msg_3676_, 2, v___x_3675_);
                v___x_3677_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3_spec__7(v_msg_3676_, v___y_3646_, v___y_3647_, v___x_3671_, v___y_3649_);
                crate::leanh::lean_dec_ref_known(v___x_3671_, 14);
                v_a_3678_ = crate::leanh::lean_ctor_get(v___x_3677_, 0);
                v_isSharedCheck_3715_ = (!crate::leanh::lean_is_exclusive(v___x_3677_)) as u8;
                if v_isSharedCheck_3715_ == 0 {
                    v___x_3680_ = v___x_3677_;
                    v_isShared_3681_ = v_isSharedCheck_3715_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3678_);
                    crate::leanh::lean_dec(v___x_3677_);
                    v___x_3680_ = crate::leanh::lean_box(0);
                    v_isShared_3681_ = v_isSharedCheck_3715_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3682_ = lean_st_ref_take(v___y_3649_);
                v_traceState_3683_ = crate::leanh::lean_ctor_get(v___x_3682_, 4);
                v_env_3684_ = crate::leanh::lean_ctor_get(v___x_3682_, 0);
                v_nextMacroScope_3685_ = crate::leanh::lean_ctor_get(v___x_3682_, 1);
                v_ngen_3686_ = crate::leanh::lean_ctor_get(v___x_3682_, 2);
                v_auxDeclNGen_3687_ = crate::leanh::lean_ctor_get(v___x_3682_, 3);
                v_cache_3688_ = crate::leanh::lean_ctor_get(v___x_3682_, 5);
                v_messages_3689_ = crate::leanh::lean_ctor_get(v___x_3682_, 6);
                v_infoState_3690_ = crate::leanh::lean_ctor_get(v___x_3682_, 7);
                v_snapshotTasks_3691_ = crate::leanh::lean_ctor_get(v___x_3682_, 8);
                v_isSharedCheck_3714_ = (!crate::leanh::lean_is_exclusive(v___x_3682_)) as u8;
                if v_isSharedCheck_3714_ == 0 {
                    v___x_3693_ = v___x_3682_;
                    v_isShared_3694_ = v_isSharedCheck_3714_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_3691_);
                    crate::leanh::lean_inc(v_infoState_3690_);
                    crate::leanh::lean_inc(v_messages_3689_);
                    crate::leanh::lean_inc(v_cache_3688_);
                    crate::leanh::lean_inc(v_traceState_3683_);
                    crate::leanh::lean_inc(v_auxDeclNGen_3687_);
                    crate::leanh::lean_inc(v_ngen_3686_);
                    crate::leanh::lean_inc(v_nextMacroScope_3685_);
                    crate::leanh::lean_inc(v_env_3684_);
                    crate::leanh::lean_dec(v___x_3682_);
                    v___x_3693_ = crate::leanh::lean_box(0);
                    v_isShared_3694_ = v_isSharedCheck_3714_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_3695_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_3683_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_3712_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_3683_)) as u8;
                if v_isSharedCheck_3712_ == 0 {
                    v_unused_3713_ = crate::leanh::lean_ctor_get(v_traceState_3683_, 0);
                    crate::leanh::lean_dec(v_unused_3713_);
                    v___x_3697_ = v_traceState_3683_;
                    v_isShared_3698_ = v_isSharedCheck_3712_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_traceState_3683_);
                    v___x_3697_ = crate::leanh::lean_box(0);
                    v_isShared_3698_ = v_isSharedCheck_3712_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3699_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3699_, 0, v_ref_3644_);
                crate::leanh::lean_ctor_set(v___x_3699_, 1, v_a_3678_);
                v___x_3700_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_3642_, v___x_3699_);
                if v_isShared_3698_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3697_, 0, v___x_3700_);
                    v___x_3702_ = v___x_3697_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3711_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3711_, 0, v___x_3700_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_3711_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_3695_,
                    );
                    v___x_3702_ = v_reuseFailAlloc_3711_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3694_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3693_, 4, v___x_3702_);
                    v___x_3704_ = v___x_3693_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3710_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3710_, 0, v_env_3684_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3710_, 1, v_nextMacroScope_3685_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3710_, 2, v_ngen_3686_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3710_, 3, v_auxDeclNGen_3687_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3710_, 4, v___x_3702_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3710_, 5, v_cache_3688_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3710_, 6, v_messages_3689_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3710_, 7, v_infoState_3690_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3710_, 8, v_snapshotTasks_3691_);
                    v___x_3704_ = v_reuseFailAlloc_3710_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3705_ = lean_st_ref_set(v___y_3649_, v___x_3704_);
                v___x_3706_ = crate::leanh::lean_box(0);
                if v_isShared_3681_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3680_, 0, v___x_3706_);
                    v___x_3708_ = v___x_3680_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3709_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3709_, 0, v___x_3706_);
                    v___x_3708_ = v_reuseFailAlloc_3709_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3708_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__2___boxed(
    mut v_oldTraces_3716_: *mut crate::leanh::LeanObject,
    mut v_data_3717_: *mut crate::leanh::LeanObject,
    mut v_ref_3718_: *mut crate::leanh::LeanObject,
    mut v_msg_3719_: *mut crate::leanh::LeanObject,
    mut v___y_3720_: *mut crate::leanh::LeanObject,
    mut v___y_3721_: *mut crate::leanh::LeanObject,
    mut v___y_3722_: *mut crate::leanh::LeanObject,
    mut v___y_3723_: *mut crate::leanh::LeanObject,
    mut v___y_3724_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3725_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__2(v_oldTraces_3716_, v_data_3717_, v_ref_3718_, v_msg_3719_, v___y_3720_, v___y_3721_, v___y_3722_, v___y_3723_);
    crate::leanh::lean_dec(v___y_3723_);
    crate::leanh::lean_dec_ref(v___y_3722_);
    crate::leanh::lean_dec(v___y_3721_);
    crate::leanh::lean_dec_ref(v___y_3720_);
    return v_res_3725_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__3___redArg(
    mut v_x_3726_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3731_: u8 = 0;
    let mut v___x_3733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3735_: u8 = 0;
    let mut v_a_3736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3739_: u8 = 0;
    let mut v___x_3741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3743_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3726_) == 0 {
                    v_a_3728_ = crate::leanh::lean_ctor_get(v_x_3726_, 0);
                    v_isSharedCheck_3735_ = (!crate::leanh::lean_is_exclusive(v_x_3726_)) as u8;
                    if v_isSharedCheck_3735_ == 0 {
                        v___x_3730_ = v_x_3726_;
                        v_isShared_3731_ = v_isSharedCheck_3735_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3728_);
                        crate::leanh::lean_dec(v_x_3726_);
                        v___x_3730_ = crate::leanh::lean_box(0);
                        v_isShared_3731_ = v_isSharedCheck_3735_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3736_ = crate::leanh::lean_ctor_get(v_x_3726_, 0);
                    v_isSharedCheck_3743_ = (!crate::leanh::lean_is_exclusive(v_x_3726_)) as u8;
                    if v_isSharedCheck_3743_ == 0 {
                        v___x_3738_ = v_x_3726_;
                        v_isShared_3739_ = v_isSharedCheck_3743_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3736_);
                        crate::leanh::lean_dec(v_x_3726_);
                        v___x_3738_ = crate::leanh::lean_box(0);
                        v_isShared_3739_ = v_isSharedCheck_3743_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3731_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3730_, 1);
                    v___x_3733_ = v___x_3730_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3734_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3734_, 0, v_a_3728_);
                    v___x_3733_ = v_reuseFailAlloc_3734_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3733_;
            }
            3 => {
                if v_isShared_3739_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3738_, 0);
                    v___x_3741_ = v___x_3738_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3742_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3742_, 0, v_a_3736_);
                    v___x_3741_ = v_reuseFailAlloc_3742_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3741_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__3___redArg___boxed(
    mut v_x_3744_: *mut crate::leanh::LeanObject,
    mut v___y_3745_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3746_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__3___redArg(v_x_3744_);
    return v_res_3746_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(
    mut v_cls_3747_: *mut crate::leanh::LeanObject,
    mut v_collapsed_3748_: u8,
    mut v_tag_3749_: *mut crate::leanh::LeanObject,
    mut v_opts_3750_: *mut crate::leanh::LeanObject,
    mut v_clsEnabled_3751_: u8,
    mut v_oldTraces_3752_: *mut crate::leanh::LeanObject,
    mut v_msg_3753_: *mut crate::leanh::LeanObject,
    mut v_resStartStop_3754_: *mut crate::leanh::LeanObject,
    mut v___y_3755_: *mut crate::leanh::LeanObject,
    mut v___y_3756_: *mut crate::leanh::LeanObject,
    mut v___y_3757_: *mut crate::leanh::LeanObject,
    mut v___y_3758_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_3760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3764_: u8 = 0;
    let mut v___y_3766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_3768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3774_: u8 = 0;
    let mut v___x_3776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3778_: u8 = 0;
    let mut v_fst_3779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3783_: u8 = 0;
    let mut v___x_3784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3785_: u8 = 0;
    let mut v___y_3787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_3789_: u8 = 0;
    let mut v___x_3790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_3796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3799_: f64 = 0.0;
    let mut v_data_3800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_3801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3802_: f64 = 0.0;
    let mut v___x_3803_: f64 = 0.0;
    let mut v_reuseFailAlloc_3804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3812_: u8 = 0;
    let mut v___x_3813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3825_: u8 = 0;
    let mut v_tid_3826_: u64 = 0;
    let mut v_traces_3827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3830_: u8 = 0;
    let mut v___x_3831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3840_: u8 = 0;
    let mut v_isSharedCheck_3841_: u8 = 0;
    let mut v___y_3843_: f64 = 0.0;
    let mut v___x_3844_: f64 = 0.0;
    let mut v___x_3845_: f64 = 0.0;
    let mut v___x_3846_: f64 = 0.0;
    let mut v___x_3847_: u8 = 0;
    let mut v___x_3848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3849_: u8 = 0;
    let mut v___x_3850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3852_: f64 = 0.0;
    let mut v___x_3853_: f64 = 0.0;
    let mut v___x_3854_: f64 = 0.0;
    let mut v___x_3855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3857_: f64 = 0.0;
    let mut v_isSharedCheck_3858_: u8 = 0;
    let mut v_isSharedCheck_3859_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_3760_ = crate::leanh::lean_ctor_get(v_resStartStop_3754_, 0);
                v_snd_3761_ = crate::leanh::lean_ctor_get(v_resStartStop_3754_, 1);
                v_isSharedCheck_3859_ =
                    (!crate::leanh::lean_is_exclusive(v_resStartStop_3754_)) as u8;
                if v_isSharedCheck_3859_ == 0 {
                    v___x_3763_ = v_resStartStop_3754_;
                    v_isShared_3764_ = v_isSharedCheck_3859_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3761_);
                    crate::leanh::lean_inc(v_fst_3760_);
                    crate::leanh::lean_dec(v_resStartStop_3754_);
                    v___x_3763_ = crate::leanh::lean_box(0);
                    v_isShared_3764_ = v_isSharedCheck_3859_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_3779_ = crate::leanh::lean_ctor_get(v_snd_3761_, 0);
                v_snd_3780_ = crate::leanh::lean_ctor_get(v_snd_3761_, 1);
                v_isSharedCheck_3858_ = (!crate::leanh::lean_is_exclusive(v_snd_3761_)) as u8;
                if v_isSharedCheck_3858_ == 0 {
                    v___x_3782_ = v_snd_3761_;
                    v_isShared_3783_ = v_isSharedCheck_3858_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3780_);
                    crate::leanh::lean_inc(v_fst_3779_);
                    crate::leanh::lean_dec(v_snd_3761_);
                    v___x_3782_ = crate::leanh::lean_box(0);
                    v_isShared_3783_ = v_isSharedCheck_3858_;
                    state = 5;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v___y_3766_);
                v___x_3769_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__2(v_oldTraces_3752_, v_data_3768_, v___y_3766_, v___y_3767_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_);
                if crate::leanh::lean_obj_tag(v___x_3769_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_3769_, 1);
                    v___x_3770_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__3___redArg(v_fst_3760_);
                    return v___x_3770_;
                } else {
                    crate::leanh::lean_dec(v_fst_3760_);
                    v_a_3771_ = crate::leanh::lean_ctor_get(v___x_3769_, 0);
                    v_isSharedCheck_3778_ = (!crate::leanh::lean_is_exclusive(v___x_3769_)) as u8;
                    if v_isSharedCheck_3778_ == 0 {
                        v___x_3773_ = v___x_3769_;
                        v_isShared_3774_ = v_isSharedCheck_3778_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3771_);
                        crate::leanh::lean_dec(v___x_3769_);
                        v___x_3773_ = crate::leanh::lean_box(0);
                        v_isShared_3774_ = v_isSharedCheck_3778_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_3774_ == 0 {
                    v___x_3776_ = v___x_3773_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3777_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3777_, 0, v_a_3771_);
                    v___x_3776_ = v_reuseFailAlloc_3777_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3776_;
            }
            5 => {
                v___x_3784_ = l_Lean_trace_profiler;
                v___x_3785_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__1(v_opts_3750_, v___x_3784_);
                if v___x_3785_ == 0 {
                    v___y_3812_ = v___x_3785_;
                    state = 10;
                    continue;
                } else {
                    v___x_3848_ = l_Lean_trace_profiler_useHeartbeats;
                    v___x_3849_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__1(v_opts_3750_, v___x_3848_);
                    if v___x_3849_ == 0 {
                        v___x_3850_ = l_Lean_trace_profiler_threshold;
                        v___x_3851_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__5(v_opts_3750_, v___x_3850_);
                        v___x_3852_ = lean_float_of_nat(v___x_3851_);
                        v___x_3853_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__4_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__4);
                        v___x_3854_ = lean_float_div(v___x_3852_, v___x_3853_);
                        v___y_3843_ = v___x_3854_;
                        state = 15;
                        continue;
                    } else {
                        v___x_3855_ = l_Lean_trace_profiler_threshold;
                        v___x_3856_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__5(v_opts_3750_, v___x_3855_);
                        v___x_3857_ = lean_float_of_nat(v___x_3856_);
                        v___y_3843_ = v___x_3857_;
                        state = 15;
                        continue;
                    }
                }
            }
            6 => {
                v_result_3789_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__2(v_fst_3760_);
                v___x_3790_ = l_Lean_TraceResult_toEmoji(v_result_3789_);
                v___x_3791_ = l_Lean_stringToMessageData(v___x_3790_);
                v___x_3792_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__1_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__1);
                if v_isShared_3783_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3782_, 7);
                    crate::leanh::lean_ctor_set(v___x_3782_, 1, v___x_3792_);
                    crate::leanh::lean_ctor_set(v___x_3782_, 0, v___x_3791_);
                    v___x_3794_ = v___x_3782_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3805_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3805_, 0, v___x_3791_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3805_, 1, v___x_3792_);
                    v___x_3794_ = v_reuseFailAlloc_3805_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_3764_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3763_, 7);
                    crate::leanh::lean_ctor_set(v___x_3763_, 1, v_a_3788_);
                    crate::leanh::lean_ctor_set(v___x_3763_, 0, v___x_3794_);
                    v_m_3796_ = v___x_3763_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3804_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3804_, 0, v___x_3794_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3804_, 1, v_a_3788_);
                    v_m_3796_ = v_reuseFailAlloc_3804_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_3797_ = crate::leanh::lean_box((v_result_3789_) as usize);
                v___x_3798_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3798_, 0, v___x_3797_);
                v___x_3799_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__0_once), _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__0);
                crate::leanh::lean_inc_ref(v_tag_3749_);
                crate::leanh::lean_inc_ref(v___x_3798_);
                crate::leanh::lean_inc(v_cls_3747_);
                v_data_3800_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v_data_3800_, 0, v_cls_3747_);
                crate::leanh::lean_ctor_set(v_data_3800_, 1, v___x_3798_);
                crate::leanh::lean_ctor_set(v_data_3800_, 2, v_tag_3749_);
                crate::leanh::lean_ctor_set_float(
                    v_data_3800_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_3799_,
                );
                crate::leanh::lean_ctor_set_float(
                    v_data_3800_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_3799_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v_data_3800_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v_collapsed_3748_,
                );
                if v___x_3785_ == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_3798_, 1);
                    crate::leanh::lean_dec(v_snd_3780_);
                    crate::leanh::lean_dec(v_fst_3779_);
                    crate::leanh::lean_dec_ref(v_tag_3749_);
                    crate::leanh::lean_dec(v_cls_3747_);
                    v___y_3766_ = v___y_3787_;
                    v___y_3767_ = v_m_3796_;
                    v_data_3768_ = v_data_3800_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref_known(v_data_3800_, 3);
                    v_data_3801_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                    crate::leanh::lean_ctor_set(v_data_3801_, 0, v_cls_3747_);
                    crate::leanh::lean_ctor_set(v_data_3801_, 1, v___x_3798_);
                    crate::leanh::lean_ctor_set(v_data_3801_, 2, v_tag_3749_);
                    v___x_3802_ = crate::leanh::lean_unbox_float(v_fst_3779_);
                    crate::leanh::lean_dec(v_fst_3779_);
                    crate::leanh::lean_ctor_set_float(
                        v_data_3801_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v___x_3802_,
                    );
                    v___x_3803_ = crate::leanh::lean_unbox_float(v_snd_3780_);
                    crate::leanh::lean_dec(v_snd_3780_);
                    crate::leanh::lean_ctor_set_float(
                        v_data_3801_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                        v___x_3803_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_data_3801_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                        v_collapsed_3748_,
                    );
                    v___y_3766_ = v___y_3787_;
                    v___y_3767_ = v_m_3796_;
                    v_data_3768_ = v_data_3801_;
                    state = 2;
                    continue;
                }
            }
            9 => {
                v_ref_3807_ = crate::leanh::lean_ctor_get(v___y_3757_, 5);
                crate::leanh::lean_inc(v___y_3758_);
                crate::leanh::lean_inc_ref(v___y_3757_);
                crate::leanh::lean_inc(v___y_3756_);
                crate::leanh::lean_inc_ref(v___y_3755_);
                crate::leanh::lean_inc(v_fst_3760_);
                v___x_3808_ = crate::leanh::lean_apply_6(
                    v_msg_3753_,
                    v_fst_3760_,
                    v___y_3755_,
                    v___y_3756_,
                    v___y_3757_,
                    v___y_3758_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_3808_) == 0 {
                    v_a_3809_ = crate::leanh::lean_ctor_get(v___x_3808_, 0);
                    crate::leanh::lean_inc(v_a_3809_);
                    crate::leanh::lean_dec_ref_known(v___x_3808_, 1);
                    v___y_3787_ = v_ref_3807_;
                    v_a_3788_ = v_a_3809_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_3808_, 1);
                    v___x_3810_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__3_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__3);
                    v___y_3787_ = v_ref_3807_;
                    v_a_3788_ = v___x_3810_;
                    state = 6;
                    continue;
                }
            }
            10 => {
                if v_clsEnabled_3751_ == 0 {
                    if v___y_3812_ == 0 {
                        crate::leanh::lean_del_object(v___x_3782_);
                        crate::leanh::lean_dec(v_snd_3780_);
                        crate::leanh::lean_dec(v_fst_3779_);
                        crate::leanh::lean_del_object(v___x_3763_);
                        crate::leanh::lean_dec_ref(v_msg_3753_);
                        crate::leanh::lean_dec_ref(v_tag_3749_);
                        crate::leanh::lean_dec(v_cls_3747_);
                        v___x_3813_ = lean_st_ref_take(v___y_3758_);
                        v_traceState_3814_ = crate::leanh::lean_ctor_get(v___x_3813_, 4);
                        v_env_3815_ = crate::leanh::lean_ctor_get(v___x_3813_, 0);
                        v_nextMacroScope_3816_ = crate::leanh::lean_ctor_get(v___x_3813_, 1);
                        v_ngen_3817_ = crate::leanh::lean_ctor_get(v___x_3813_, 2);
                        v_auxDeclNGen_3818_ = crate::leanh::lean_ctor_get(v___x_3813_, 3);
                        v_cache_3819_ = crate::leanh::lean_ctor_get(v___x_3813_, 5);
                        v_messages_3820_ = crate::leanh::lean_ctor_get(v___x_3813_, 6);
                        v_infoState_3821_ = crate::leanh::lean_ctor_get(v___x_3813_, 7);
                        v_snapshotTasks_3822_ = crate::leanh::lean_ctor_get(v___x_3813_, 8);
                        v_isSharedCheck_3841_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3813_)) as u8;
                        if v_isSharedCheck_3841_ == 0 {
                            v___x_3824_ = v___x_3813_;
                            v_isShared_3825_ = v_isSharedCheck_3841_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snapshotTasks_3822_);
                            crate::leanh::lean_inc(v_infoState_3821_);
                            crate::leanh::lean_inc(v_messages_3820_);
                            crate::leanh::lean_inc(v_cache_3819_);
                            crate::leanh::lean_inc(v_traceState_3814_);
                            crate::leanh::lean_inc(v_auxDeclNGen_3818_);
                            crate::leanh::lean_inc(v_ngen_3817_);
                            crate::leanh::lean_inc(v_nextMacroScope_3816_);
                            crate::leanh::lean_inc(v_env_3815_);
                            crate::leanh::lean_dec(v___x_3813_);
                            v___x_3824_ = crate::leanh::lean_box(0);
                            v_isShared_3825_ = v_isSharedCheck_3841_;
                            state = 11;
                            continue;
                        }
                    } else {
                        state = 9;
                        continue;
                    }
                } else {
                    state = 9;
                    continue;
                }
            }
            11 => {
                v_tid_3826_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_3814_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_3827_ = crate::leanh::lean_ctor_get(v_traceState_3814_, 0);
                v_isSharedCheck_3840_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_3814_)) as u8;
                if v_isSharedCheck_3840_ == 0 {
                    v___x_3829_ = v_traceState_3814_;
                    v_isShared_3830_ = v_isSharedCheck_3840_;
                    state = 12;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_3827_);
                    crate::leanh::lean_dec(v_traceState_3814_);
                    v___x_3829_ = crate::leanh::lean_box(0);
                    v_isShared_3830_ = v_isSharedCheck_3840_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_3831_ =
                    l_Lean_PersistentArray_append___redArg(v_oldTraces_3752_, v_traces_3827_);
                crate::leanh::lean_dec_ref(v_traces_3827_);
                if v_isShared_3830_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3829_, 0, v___x_3831_);
                    v___x_3833_ = v___x_3829_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3839_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3839_, 0, v___x_3831_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_3839_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_3826_,
                    );
                    v___x_3833_ = v_reuseFailAlloc_3839_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_3825_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3824_, 4, v___x_3833_);
                    v___x_3835_ = v___x_3824_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3838_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3838_, 0, v_env_3815_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3838_, 1, v_nextMacroScope_3816_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3838_, 2, v_ngen_3817_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3838_, 3, v_auxDeclNGen_3818_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3838_, 4, v___x_3833_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3838_, 5, v_cache_3819_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3838_, 6, v_messages_3820_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3838_, 7, v_infoState_3821_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3838_, 8, v_snapshotTasks_3822_);
                    v___x_3835_ = v_reuseFailAlloc_3838_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_3836_ = lean_st_ref_set(v___y_3758_, v___x_3835_);
                v___x_3837_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__3___redArg(v_fst_3760_);
                return v___x_3837_;
            }
            15 => {
                v___x_3844_ = crate::leanh::lean_unbox_float(v_snd_3780_);
                v___x_3845_ = crate::leanh::lean_unbox_float(v_fst_3779_);
                v___x_3846_ = lean_float_sub(v___x_3844_, v___x_3845_);
                v___x_3847_ = lean_float_decLt(v___y_3843_, v___x_3846_);
                v___y_3812_ = v___x_3847_;
                state = 10;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2___boxed(
    mut v_cls_3860_: *mut crate::leanh::LeanObject,
    mut v_collapsed_3861_: *mut crate::leanh::LeanObject,
    mut v_tag_3862_: *mut crate::leanh::LeanObject,
    mut v_opts_3863_: *mut crate::leanh::LeanObject,
    mut v_clsEnabled_3864_: *mut crate::leanh::LeanObject,
    mut v_oldTraces_3865_: *mut crate::leanh::LeanObject,
    mut v_msg_3866_: *mut crate::leanh::LeanObject,
    mut v_resStartStop_3867_: *mut crate::leanh::LeanObject,
    mut v___y_3868_: *mut crate::leanh::LeanObject,
    mut v___y_3869_: *mut crate::leanh::LeanObject,
    mut v___y_3870_: *mut crate::leanh::LeanObject,
    mut v___y_3871_: *mut crate::leanh::LeanObject,
    mut v___y_3872_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_collapsed_boxed_3873_: u8 = 0;
    let mut v_clsEnabled_boxed_3874_: u8 = 0;
    let mut v_res_3875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_3873_ = (crate::leanh::lean_unbox(v_collapsed_3861_) as u8);
    v_clsEnabled_boxed_3874_ = (crate::leanh::lean_unbox(v_clsEnabled_3864_) as u8);
    v_res_3875_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_3860_, v_collapsed_boxed_3873_, v_tag_3862_, v_opts_3863_, v_clsEnabled_boxed_3874_, v_oldTraces_3865_, v_msg_3866_, v_resStartStop_3867_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_);
    crate::leanh::lean_dec(v___y_3871_);
    crate::leanh::lean_dec_ref(v___y_3870_);
    crate::leanh::lean_dec(v___y_3869_);
    crate::leanh::lean_dec_ref(v___y_3868_);
    crate::leanh::lean_dec_ref(v_opts_3863_);
    return v_res_3875_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3877_ = crate::leanh::lean_box(0);
    v___x_3878_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_3879_ = lean_mk_array(v___x_3878_, v___x_3877_);
    return v___x_3879_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3880_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__1_once),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__1,
    );
    v___x_3881_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3882_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3882_, 0, v___x_3881_);
    crate::leanh::lean_ctor_set(v___x_3882_, 1, v___x_3880_);
    return v___x_3882_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3883_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__2_once),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__2,
    );
    v___x_3884_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3884_, 0, v___x_3883_);
    crate::leanh::lean_ctor_set(v___x_3884_, 1, v___x_3883_);
    crate::leanh::lean_ctor_set(v___x_3884_, 2, v___x_3883_);
    crate::leanh::lean_ctor_set(v___x_3884_, 3, v___x_3883_);
    return v___x_3884_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(
    mut v_g_3886_: *mut crate::leanh::LeanObject,
    mut v_cfg_3887_: *mut crate::leanh::LeanObject,
    mut v_a_3888_: *mut crate::leanh::LeanObject,
    mut v_a_3889_: *mut crate::leanh::LeanObject,
    mut v_a_3890_: *mut crate::leanh::LeanObject,
    mut v_a_3891_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_3893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3894_: u8 = 0;
    let mut v___x_3895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3915_: u8 = 0;
    let mut v___x_3916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3920_: u8 = 0;
    let mut v_a_3921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3924_: u8 = 0;
    let mut v___x_3926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3928_: u8 = 0;
    let mut v_inheritedTraceOptions_3929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: u8 = 0;
    let mut v___y_3936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3940_: f64 = 0.0;
    let mut v___x_3941_: f64 = 0.0;
    let mut v___x_3942_: f64 = 0.0;
    let mut v___x_3943_: f64 = 0.0;
    let mut v___x_3944_: f64 = 0.0;
    let mut v___x_3945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: f64 = 0.0;
    let mut v___x_3966_: f64 = 0.0;
    let mut v___x_3967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3986_: u8 = 0;
    let mut v___x_3987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4034_: u8 = 0;
    let mut v___x_4035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4055_: u8 = 0;
    let mut v___x_4056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4060_: u8 = 0;
    let mut v_a_4061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4064_: u8 = 0;
    let mut v___x_4066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4068_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_3893_ = crate::leanh::lean_ctor_get(v_a_3890_, 2);
                v_hasTrace_3894_ = crate::leanh::lean_ctor_get_uint8(
                    v_options_3893_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                if v_hasTrace_3894_ == 0 {
                    v___x_3895_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__0;
                    crate::leanh::lean_inc(v_g_3886_);
                    v___x_3896_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg(v_g_3886_, v___x_3895_, v_a_3888_, v_a_3889_, v_a_3890_, v_a_3891_);
                    if crate::leanh::lean_obj_tag(v___x_3896_) == 0 {
                        v_a_3897_ = crate::leanh::lean_ctor_get(v___x_3896_, 0);
                        crate::leanh::lean_inc(v_a_3897_);
                        crate::leanh::lean_dec_ref_known(v___x_3896_, 1);
                        v___x_3898_ = lean_array_get_size(v_a_3897_);
                        crate::leanh::lean_dec(v_a_3897_);
                        v___x_3899_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_3900_ = crate::leanh::lean_unsigned_to_nat(4);
                        v___x_3901_ = lean_nat_mul(v___x_3898_, v___x_3900_);
                        v___x_3902_ = crate::leanh::lean_unsigned_to_nat(3);
                        v___x_3903_ = lean_nat_div(v___x_3901_, v___x_3902_);
                        crate::leanh::lean_dec(v___x_3901_);
                        v___x_3904_ = l_Nat_nextPowerOfTwo(v___x_3903_);
                        crate::leanh::lean_dec(v___x_3903_);
                        v___x_3905_ = crate::leanh::lean_box(0);
                        v___x_3906_ = lean_mk_array(v___x_3904_, v___x_3905_);
                        v___x_3907_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3907_, 0, v___x_3899_);
                        crate::leanh::lean_ctor_set(v___x_3907_, 1, v___x_3906_);
                        v___x_3908_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__3_once
                            ),
                            _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__3,
                        );
                        crate::leanh::lean_inc_ref(v___x_3907_);
                        v___x_3909_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3909_, 0, v___x_3907_);
                        crate::leanh::lean_ctor_set(v___x_3909_, 1, v___x_3907_);
                        crate::leanh::lean_ctor_set(v___x_3909_, 2, v___x_3908_);
                        v___x_3910_ = lean_st_mk_ref(v___x_3909_);
                        v___x_3911_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go(v_g_3886_, v_cfg_3887_, v___x_3910_, v_a_3888_, v_a_3889_, v_a_3890_, v_a_3891_);
                        if crate::leanh::lean_obj_tag(v___x_3911_) == 0 {
                            v_a_3912_ = crate::leanh::lean_ctor_get(v___x_3911_, 0);
                            v_isSharedCheck_3920_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3911_)) as u8;
                            if v_isSharedCheck_3920_ == 0 {
                                v___x_3914_ = v___x_3911_;
                                v_isShared_3915_ = v_isSharedCheck_3920_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3912_);
                                crate::leanh::lean_dec(v___x_3911_);
                                v___x_3914_ = crate::leanh::lean_box(0);
                                v_isShared_3915_ = v_isSharedCheck_3920_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_3910_);
                            return v___x_3911_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_g_3886_);
                        v_a_3921_ = crate::leanh::lean_ctor_get(v___x_3896_, 0);
                        v_isSharedCheck_3928_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3896_)) as u8;
                        if v_isSharedCheck_3928_ == 0 {
                            v___x_3923_ = v___x_3896_;
                            v_isShared_3924_ = v_isSharedCheck_3928_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3921_);
                            crate::leanh::lean_dec(v___x_3896_);
                            v___x_3923_ = crate::leanh::lean_box(0);
                            v_isShared_3924_ = v_isSharedCheck_3928_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_inheritedTraceOptions_3929_ = crate::leanh::lean_ctor_get(v_a_3890_, 13);
                    v___f_3930_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__4;
                    v___x_3931_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__3;
                    v___x_3932_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__1;
                    v___x_3933_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7);
                    v___x_3934_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_3929_,
                        v_options_3893_,
                        v___x_3933_,
                    );
                    if v___x_3934_ == 0 {
                        v___x_4033_ = l_Lean_trace_profiler;
                        v___x_4034_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__1(v_options_3893_, v___x_4033_);
                        if v___x_4034_ == 0 {
                            v___x_4035_ =
                                l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__0;
                            crate::leanh::lean_inc(v_g_3886_);
                            v___x_4036_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg(v_g_3886_, v___x_4035_, v_a_3888_, v_a_3889_, v_a_3890_, v_a_3891_);
                            if crate::leanh::lean_obj_tag(v___x_4036_) == 0 {
                                v_a_4037_ = crate::leanh::lean_ctor_get(v___x_4036_, 0);
                                crate::leanh::lean_inc(v_a_4037_);
                                crate::leanh::lean_dec_ref_known(v___x_4036_, 1);
                                v___x_4038_ = lean_array_get_size(v_a_4037_);
                                crate::leanh::lean_dec(v_a_4037_);
                                v___x_4039_ = crate::leanh::lean_unsigned_to_nat(0);
                                v___x_4040_ = crate::leanh::lean_unsigned_to_nat(4);
                                v___x_4041_ = lean_nat_mul(v___x_4038_, v___x_4040_);
                                v___x_4042_ = crate::leanh::lean_unsigned_to_nat(3);
                                v___x_4043_ = lean_nat_div(v___x_4041_, v___x_4042_);
                                crate::leanh::lean_dec(v___x_4041_);
                                v___x_4044_ = l_Nat_nextPowerOfTwo(v___x_4043_);
                                crate::leanh::lean_dec(v___x_4043_);
                                v___x_4045_ = crate::leanh::lean_box(0);
                                v___x_4046_ = lean_mk_array(v___x_4044_, v___x_4045_);
                                v___x_4047_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_4047_, 0, v___x_4039_);
                                crate::leanh::lean_ctor_set(v___x_4047_, 1, v___x_4046_);
                                v___x_4048_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__3), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__3_once), _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__3);
                                crate::leanh::lean_inc_ref(v___x_4047_);
                                v___x_4049_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_4049_, 0, v___x_4047_);
                                crate::leanh::lean_ctor_set(v___x_4049_, 1, v___x_4047_);
                                crate::leanh::lean_ctor_set(v___x_4049_, 2, v___x_4048_);
                                v___x_4050_ = lean_st_mk_ref(v___x_4049_);
                                v___x_4051_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go(v_g_3886_, v_cfg_3887_, v___x_4050_, v_a_3888_, v_a_3889_, v_a_3890_, v_a_3891_);
                                if crate::leanh::lean_obj_tag(v___x_4051_) == 0 {
                                    v_a_4052_ = crate::leanh::lean_ctor_get(v___x_4051_, 0);
                                    v_isSharedCheck_4060_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_4051_)) as u8;
                                    if v_isSharedCheck_4060_ == 0 {
                                        v___x_4054_ = v___x_4051_;
                                        v_isShared_4055_ = v_isSharedCheck_4060_;
                                        state = 12;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_4052_);
                                        crate::leanh::lean_dec(v___x_4051_);
                                        v___x_4054_ = crate::leanh::lean_box(0);
                                        v_isShared_4055_ = v_isSharedCheck_4060_;
                                        state = 12;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v___x_4050_);
                                    return v___x_4051_;
                                }
                            } else {
                                crate::leanh::lean_dec(v_g_3886_);
                                v_a_4061_ = crate::leanh::lean_ctor_get(v___x_4036_, 0);
                                v_isSharedCheck_4068_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4036_)) as u8;
                                if v_isSharedCheck_4068_ == 0 {
                                    v___x_4063_ = v___x_4036_;
                                    v_isShared_4064_ = v_isSharedCheck_4068_;
                                    state = 14;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4061_);
                                    crate::leanh::lean_dec(v___x_4036_);
                                    v___x_4063_ = crate::leanh::lean_box(0);
                                    v_isShared_4064_ = v_isSharedCheck_4068_;
                                    state = 14;
                                    continue;
                                }
                            }
                        } else {
                            state = 11;
                            continue;
                        }
                    } else {
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3916_ = lean_st_ref_get(v___x_3910_);
                crate::leanh::lean_dec(v___x_3910_);
                crate::leanh::lean_dec(v___x_3916_);
                if v_isShared_3915_ == 0 {
                    v___x_3918_ = v___x_3914_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3919_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3919_, 0, v_a_3912_);
                    v___x_3918_ = v_reuseFailAlloc_3919_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3918_;
            }
            3 => {
                if v_isShared_3924_ == 0 {
                    v___x_3926_ = v___x_3923_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3927_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3927_, 0, v_a_3921_);
                    v___x_3926_ = v_reuseFailAlloc_3927_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3926_;
            }
            5 => {
                v___x_3939_ = lean_io_mono_nanos_now();
                v___x_3940_ = lean_float_of_nat(v___y_3937_);
                v___x_3941_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__4_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__4);
                v___x_3942_ = lean_float_div(v___x_3940_, v___x_3941_);
                v___x_3943_ = lean_float_of_nat(v___x_3939_);
                v___x_3944_ = lean_float_div(v___x_3943_, v___x_3941_);
                v___x_3945_ = crate::leanh::lean_box_float(v___x_3942_);
                v___x_3946_ = crate::leanh::lean_box_float(v___x_3944_);
                v___x_3947_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3947_, 0, v___x_3945_);
                crate::leanh::lean_ctor_set(v___x_3947_, 1, v___x_3946_);
                v___x_3948_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3948_, 0, v_a_3938_);
                crate::leanh::lean_ctor_set(v___x_3948_, 1, v___x_3947_);
                v___x_3949_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v___x_3931_, v_hasTrace_3894_, v___x_3932_, v_options_3893_, v___x_3934_, v___y_3936_, v___f_3930_, v___x_3948_, v_a_3888_, v_a_3889_, v_a_3890_, v_a_3891_);
                return v___x_3949_;
            }
            6 => {
                v___x_3954_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3954_, 0, v_a_3953_);
                v___y_3936_ = v___y_3951_;
                v___y_3937_ = v___y_3952_;
                v_a_3938_ = v___x_3954_;
                state = 5;
                continue;
            }
            7 => {
                v___x_3959_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3959_, 0, v_a_3958_);
                v___y_3936_ = v___y_3956_;
                v___y_3937_ = v___y_3957_;
                v_a_3938_ = v___x_3959_;
                state = 5;
                continue;
            }
            8 => {
                v___x_3964_ = lean_io_get_num_heartbeats();
                v___x_3965_ = lean_float_of_nat(v___y_3961_);
                v___x_3966_ = lean_float_of_nat(v___x_3964_);
                v___x_3967_ = crate::leanh::lean_box_float(v___x_3965_);
                v___x_3968_ = crate::leanh::lean_box_float(v___x_3966_);
                v___x_3969_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3969_, 0, v___x_3967_);
                crate::leanh::lean_ctor_set(v___x_3969_, 1, v___x_3968_);
                v___x_3970_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3970_, 0, v_a_3963_);
                crate::leanh::lean_ctor_set(v___x_3970_, 1, v___x_3969_);
                v___x_3971_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v___x_3931_, v_hasTrace_3894_, v___x_3932_, v_options_3893_, v___x_3934_, v___y_3962_, v___f_3930_, v___x_3970_, v_a_3888_, v_a_3889_, v_a_3890_, v_a_3891_);
                return v___x_3971_;
            }
            9 => {
                v___x_3976_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3976_, 0, v_a_3975_);
                v___y_3961_ = v___y_3973_;
                v___y_3962_ = v___y_3974_;
                v_a_3963_ = v___x_3976_;
                state = 8;
                continue;
            }
            10 => {
                v___x_3981_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3981_, 0, v_a_3980_);
                v___y_3961_ = v___y_3978_;
                v___y_3962_ = v___y_3979_;
                v_a_3963_ = v___x_3981_;
                state = 8;
                continue;
            }
            11 => {
                v___x_3983_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1___redArg(v_a_3891_);
                v_a_3984_ = crate::leanh::lean_ctor_get(v___x_3983_, 0);
                crate::leanh::lean_inc(v_a_3984_);
                crate::leanh::lean_dec_ref(v___x_3983_);
                v___x_3985_ = l_Lean_trace_profiler_useHeartbeats;
                v___x_3986_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__1(v_options_3893_, v___x_3985_);
                if v___x_3986_ == 0 {
                    v___x_3987_ = lean_io_mono_nanos_now();
                    v___x_3988_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__0;
                    crate::leanh::lean_inc(v_g_3886_);
                    v___x_3989_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg(v_g_3886_, v___x_3988_, v_a_3888_, v_a_3889_, v_a_3890_, v_a_3891_);
                    if crate::leanh::lean_obj_tag(v___x_3989_) == 0 {
                        v_a_3990_ = crate::leanh::lean_ctor_get(v___x_3989_, 0);
                        crate::leanh::lean_inc(v_a_3990_);
                        crate::leanh::lean_dec_ref_known(v___x_3989_, 1);
                        v___x_3991_ = lean_array_get_size(v_a_3990_);
                        crate::leanh::lean_dec(v_a_3990_);
                        v___x_3992_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_3993_ = crate::leanh::lean_unsigned_to_nat(4);
                        v___x_3994_ = lean_nat_mul(v___x_3991_, v___x_3993_);
                        v___x_3995_ = crate::leanh::lean_unsigned_to_nat(3);
                        v___x_3996_ = lean_nat_div(v___x_3994_, v___x_3995_);
                        crate::leanh::lean_dec(v___x_3994_);
                        v___x_3997_ = l_Nat_nextPowerOfTwo(v___x_3996_);
                        crate::leanh::lean_dec(v___x_3996_);
                        v___x_3998_ = crate::leanh::lean_box(0);
                        v___x_3999_ = lean_mk_array(v___x_3997_, v___x_3998_);
                        v___x_4000_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4000_, 0, v___x_3992_);
                        crate::leanh::lean_ctor_set(v___x_4000_, 1, v___x_3999_);
                        v___x_4001_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__3_once
                            ),
                            _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__3,
                        );
                        crate::leanh::lean_inc_ref(v___x_4000_);
                        v___x_4002_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4002_, 0, v___x_4000_);
                        crate::leanh::lean_ctor_set(v___x_4002_, 1, v___x_4000_);
                        crate::leanh::lean_ctor_set(v___x_4002_, 2, v___x_4001_);
                        v___x_4003_ = lean_st_mk_ref(v___x_4002_);
                        v___x_4004_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go(v_g_3886_, v_cfg_3887_, v___x_4003_, v_a_3888_, v_a_3889_, v_a_3890_, v_a_3891_);
                        if crate::leanh::lean_obj_tag(v___x_4004_) == 0 {
                            v_a_4005_ = crate::leanh::lean_ctor_get(v___x_4004_, 0);
                            crate::leanh::lean_inc(v_a_4005_);
                            crate::leanh::lean_dec_ref_known(v___x_4004_, 1);
                            v___x_4006_ = lean_st_ref_get(v___x_4003_);
                            crate::leanh::lean_dec(v___x_4003_);
                            crate::leanh::lean_dec(v___x_4006_);
                            v___y_3956_ = v_a_3984_;
                            v___y_3957_ = v___x_3987_;
                            v_a_3958_ = v_a_4005_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_4003_);
                            if crate::leanh::lean_obj_tag(v___x_4004_) == 0 {
                                v_a_4007_ = crate::leanh::lean_ctor_get(v___x_4004_, 0);
                                crate::leanh::lean_inc(v_a_4007_);
                                crate::leanh::lean_dec_ref_known(v___x_4004_, 1);
                                v___y_3956_ = v_a_3984_;
                                v___y_3957_ = v___x_3987_;
                                v_a_3958_ = v_a_4007_;
                                state = 7;
                                continue;
                            } else {
                                v_a_4008_ = crate::leanh::lean_ctor_get(v___x_4004_, 0);
                                crate::leanh::lean_inc(v_a_4008_);
                                crate::leanh::lean_dec_ref_known(v___x_4004_, 1);
                                v___y_3951_ = v_a_3984_;
                                v___y_3952_ = v___x_3987_;
                                v_a_3953_ = v_a_4008_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_g_3886_);
                        v_a_4009_ = crate::leanh::lean_ctor_get(v___x_3989_, 0);
                        crate::leanh::lean_inc(v_a_4009_);
                        crate::leanh::lean_dec_ref_known(v___x_3989_, 1);
                        v___y_3951_ = v_a_3984_;
                        v___y_3952_ = v___x_3987_;
                        v_a_3953_ = v_a_4009_;
                        state = 6;
                        continue;
                    }
                } else {
                    v___x_4010_ = lean_io_get_num_heartbeats();
                    v___x_4011_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__0;
                    crate::leanh::lean_inc(v_g_3886_);
                    v___x_4012_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg(v_g_3886_, v___x_4011_, v_a_3888_, v_a_3889_, v_a_3890_, v_a_3891_);
                    if crate::leanh::lean_obj_tag(v___x_4012_) == 0 {
                        v_a_4013_ = crate::leanh::lean_ctor_get(v___x_4012_, 0);
                        crate::leanh::lean_inc(v_a_4013_);
                        crate::leanh::lean_dec_ref_known(v___x_4012_, 1);
                        v___x_4014_ = lean_array_get_size(v_a_4013_);
                        crate::leanh::lean_dec(v_a_4013_);
                        v___x_4015_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_4016_ = crate::leanh::lean_unsigned_to_nat(4);
                        v___x_4017_ = lean_nat_mul(v___x_4014_, v___x_4016_);
                        v___x_4018_ = crate::leanh::lean_unsigned_to_nat(3);
                        v___x_4019_ = lean_nat_div(v___x_4017_, v___x_4018_);
                        crate::leanh::lean_dec(v___x_4017_);
                        v___x_4020_ = l_Nat_nextPowerOfTwo(v___x_4019_);
                        crate::leanh::lean_dec(v___x_4019_);
                        v___x_4021_ = crate::leanh::lean_box(0);
                        v___x_4022_ = lean_mk_array(v___x_4020_, v___x_4021_);
                        v___x_4023_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4023_, 0, v___x_4015_);
                        crate::leanh::lean_ctor_set(v___x_4023_, 1, v___x_4022_);
                        v___x_4024_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__3_once
                            ),
                            _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__3,
                        );
                        crate::leanh::lean_inc_ref(v___x_4023_);
                        v___x_4025_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4025_, 0, v___x_4023_);
                        crate::leanh::lean_ctor_set(v___x_4025_, 1, v___x_4023_);
                        crate::leanh::lean_ctor_set(v___x_4025_, 2, v___x_4024_);
                        v___x_4026_ = lean_st_mk_ref(v___x_4025_);
                        v___x_4027_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go(v_g_3886_, v_cfg_3887_, v___x_4026_, v_a_3888_, v_a_3889_, v_a_3890_, v_a_3891_);
                        if crate::leanh::lean_obj_tag(v___x_4027_) == 0 {
                            v_a_4028_ = crate::leanh::lean_ctor_get(v___x_4027_, 0);
                            crate::leanh::lean_inc(v_a_4028_);
                            crate::leanh::lean_dec_ref_known(v___x_4027_, 1);
                            v___x_4029_ = lean_st_ref_get(v___x_4026_);
                            crate::leanh::lean_dec(v___x_4026_);
                            crate::leanh::lean_dec(v___x_4029_);
                            v___y_3978_ = v___x_4010_;
                            v___y_3979_ = v_a_3984_;
                            v_a_3980_ = v_a_4028_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_4026_);
                            if crate::leanh::lean_obj_tag(v___x_4027_) == 0 {
                                v_a_4030_ = crate::leanh::lean_ctor_get(v___x_4027_, 0);
                                crate::leanh::lean_inc(v_a_4030_);
                                crate::leanh::lean_dec_ref_known(v___x_4027_, 1);
                                v___y_3978_ = v___x_4010_;
                                v___y_3979_ = v_a_3984_;
                                v_a_3980_ = v_a_4030_;
                                state = 10;
                                continue;
                            } else {
                                v_a_4031_ = crate::leanh::lean_ctor_get(v___x_4027_, 0);
                                crate::leanh::lean_inc(v_a_4031_);
                                crate::leanh::lean_dec_ref_known(v___x_4027_, 1);
                                v___y_3973_ = v___x_4010_;
                                v___y_3974_ = v_a_3984_;
                                v_a_3975_ = v_a_4031_;
                                state = 9;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_g_3886_);
                        v_a_4032_ = crate::leanh::lean_ctor_get(v___x_4012_, 0);
                        crate::leanh::lean_inc(v_a_4032_);
                        crate::leanh::lean_dec_ref_known(v___x_4012_, 1);
                        v___y_3973_ = v___x_4010_;
                        v___y_3974_ = v_a_3984_;
                        v_a_3975_ = v_a_4032_;
                        state = 9;
                        continue;
                    }
                }
            }
            12 => {
                v___x_4056_ = lean_st_ref_get(v___x_4050_);
                crate::leanh::lean_dec(v___x_4050_);
                crate::leanh::lean_dec(v___x_4056_);
                if v_isShared_4055_ == 0 {
                    v___x_4058_ = v___x_4054_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4059_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4059_, 0, v_a_4052_);
                    v___x_4058_ = v_reuseFailAlloc_4059_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_4058_;
            }
            14 => {
                if v_isShared_4064_ == 0 {
                    v___x_4066_ = v___x_4063_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4067_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4067_, 0, v_a_4061_);
                    v___x_4066_ = v_reuseFailAlloc_4067_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_4066_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___boxed(
    mut v_g_4069_: *mut crate::leanh::LeanObject,
    mut v_cfg_4070_: *mut crate::leanh::LeanObject,
    mut v_a_4071_: *mut crate::leanh::LeanObject,
    mut v_a_4072_: *mut crate::leanh::LeanObject,
    mut v_a_4073_: *mut crate::leanh::LeanObject,
    mut v_a_4074_: *mut crate::leanh::LeanObject,
    mut v_a_4075_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4076_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(
        v_g_4069_,
        v_cfg_4070_,
        v_a_4071_,
        v_a_4072_,
        v_a_4073_,
        v_a_4074_,
    );
    crate::leanh::lean_dec(v_a_4074_);
    crate::leanh::lean_dec_ref(v_a_4073_);
    crate::leanh::lean_dec(v_a_4072_);
    crate::leanh::lean_dec_ref(v_a_4071_);
    crate::leanh::lean_dec_ref(v_cfg_4070_);
    return v_res_4076_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__3(
    mut v_00_u03b1_4077_: *mut crate::leanh::LeanObject,
    mut v_x_4078_: *mut crate::leanh::LeanObject,
    mut v___y_4079_: *mut crate::leanh::LeanObject,
    mut v___y_4080_: *mut crate::leanh::LeanObject,
    mut v___y_4081_: *mut crate::leanh::LeanObject,
    mut v___y_4082_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4084_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__3___redArg(v_x_4078_);
    return v___x_4084_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__3___boxed(
    mut v_00_u03b1_4085_: *mut crate::leanh::LeanObject,
    mut v_x_4086_: *mut crate::leanh::LeanObject,
    mut v___y_4087_: *mut crate::leanh::LeanObject,
    mut v___y_4088_: *mut crate::leanh::LeanObject,
    mut v___y_4089_: *mut crate::leanh::LeanObject,
    mut v___y_4090_: *mut crate::leanh::LeanObject,
    mut v___y_4091_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4092_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__3(v_00_u03b1_4085_, v_x_4086_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_);
    crate::leanh::lean_dec(v___y_4090_);
    crate::leanh::lean_dec_ref(v___y_4089_);
    crate::leanh::lean_dec(v___y_4088_);
    crate::leanh::lean_dec_ref(v___y_4087_);
    return v_res_4092_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_FalseOrByContra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_ApplyControlFlow(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Simproc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_AC(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Structures(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Enums(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_TypeAnalysis(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_BVDecide_Normalize(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_FalseOrByContra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_ApplyControlFlow(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_Simproc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_AC(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_Structures(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_Enums(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_TypeAnalysis(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_BVDecide_Normalize(builtin);
}
