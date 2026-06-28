// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Normalize
// Imports: Lean.Elab.Tactic.FalseOrByContra Lean.Meta.Tactic.BVDecide.Normalize.Basic Lean.Meta.Tactic.BVDecide.Normalize.ApplyControlFlow Lean.Meta.Tactic.BVDecide.Normalize.Simproc Lean.Meta.Tactic.BVDecide.Normalize.Rewrite Lean.Meta.Tactic.BVDecide.Normalize.AndFlatten Lean.Meta.Tactic.BVDecide.Normalize.EmbeddedConstraint Lean.Meta.Tactic.BVDecide.Normalize.AC Lean.Meta.Tactic.BVDecide.Normalize.Structures Lean.Meta.Tactic.BVDecide.Normalize.IntToBitVec Lean.Meta.Tactic.BVDecide.Normalize.Enums Lean.Meta.Tactic.BVDecide.Normalize.TypeAnalysis Lean.Meta.Tactic.BVDecide.Normalize.ShortCircuit
use crate::r#gen::Init::Data::List::Basic::l_List_appendTR___redArg;
use crate::r#gen::Init::Data::Nat::Power2::Basic::l_Nat_nextPowerOfTwo;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_mkStr3, l_Lean_replaceRef,
};
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
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Float::{lean_float_decLt, lean_float_div, lean_float_sub};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_dec_lt};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_mk_empty_array_with_capacity, lean_nat_div, lean_nat_mul,
};
use crate::lean_imports_rs::Init::System::IO::{
    lean_io_get_num_heartbeats, lean_io_mono_nanos_now,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_6,
    lean_apply_8, lean_box, lean_box_float, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_get_uint64, lean_ctor_set, lean_ctor_set_float, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_ctor_set_uint64, lean_ctor_set_usize, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_float_once, lean_inc, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unbox_float, lean_unbox_usize, lean_unsigned_to_nat,
};
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__0_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [82, 117, 110, 110, 105, 110, 103, 32, 112, 97, 115, 115, 58, 32, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__2_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [32, 111, 110, 10, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__2_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__1_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__1_value) as *mut LeanObject;
pub static l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__2_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__0_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__2_value: LeanStringObject<54> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [60, 101, 120, 99, 101, 112, 116, 105, 111, 110, 32, 116, 104, 114, 111, 119, 110, 32, 119, 104, 105, 108, 101, 32, 112, 114, 111, 100, 117, 99, 105, 110, 103, 32, 116, 114, 97, 99, 101, 32, 110, 111, 100, 101, 32, 109, 101, 115, 115, 97, 103, 101, 62, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__2_value) as *mut LeanObject;
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__4: f64 = 0.0;
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__2_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [98, 118, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__2_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__0_value) as *mut LeanObject,142734480563613395 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__1_value) as *mut LeanObject,15847151208953044930 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__2_value) as *mut LeanObject,10551690841954068875 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__3_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__4: f64 = 0.0;
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__5_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__5_value) as *mut LeanObject,14231257465488249300 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__6_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__8_value: LeanStringObject<31> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 31, m_capacity: 31, m_length: 30, m_data: [82, 117, 110, 110, 105, 110, 103, 32, 102, 105, 120, 112, 111, 105, 110, 116, 32, 112, 105, 112, 101, 108, 105, 110, 101, 32, 111, 110, 58, 10, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__8_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__10_value: LeanStringObject<36> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 36, m_capacity: 36, m_length: 35, m_data: [82, 117, 110, 110, 105, 110, 103, 32, 112, 114, 101, 112, 114, 111, 99, 101, 115, 115, 105, 110, 103, 32, 112, 105, 112, 101, 108, 105, 110, 101, 32, 111, 110, 58, 10, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__10_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___closed__0_value:
    LeanStringObject<19> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___closed__0_value
)
    as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___closed__1_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___closed__0_value
    ) as *mut LeanObject],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___closed__1_value
)
    as *mut LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___closed__2_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__0_value: LeanClosureObject<
    0,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_getPropHyps___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__4_value: LeanClosureObject<
    0,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__4_value)
        as *mut LeanObject;
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_2047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut LeanObject = core::ptr::null_mut();
    v___x_2047_ = lean_box(0);
    v___x_2048_ = l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass;
    v___x_2049_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_2049_, 0, v___x_2048_);
    lean_ctor_set(v___x_2049_, 1, v___x_2047_);
    return v___x_2049_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_2050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut LeanObject = core::ptr::null_mut();
    v___x_2050_ = lean_box(0);
    v___x_2051_ = l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass;
    v___x_2052_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_2052_, 0, v___x_2051_);
    lean_ctor_set(v___x_2052_, 1, v___x_2050_);
    return v___x_2052_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_2053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_passPipeline_2055_: *mut LeanObject = core::ptr::null_mut();
    v___x_2053_ = lean_box(0);
    v___x_2054_ = l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass;
    v_passPipeline_2055_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v_passPipeline_2055_, 0, v___x_2054_);
    lean_ctor_set(v_passPipeline_2055_, 1, v___x_2053_);
    return v_passPipeline_2055_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_2056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut LeanObject = core::ptr::null_mut();
    v___x_2056_ = lean_box(0);
    v___x_2057_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass;
    v___x_2058_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_2058_, 0, v___x_2057_);
    lean_ctor_set(v___x_2058_, 1, v___x_2056_);
    return v___x_2058_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_2059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_passPipeline_2060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut LeanObject = core::ptr::null_mut();
    v___x_2059_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__3_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__3);
    v_passPipeline_2060_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__2_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__2);
    v___x_2061_ = l_List_appendTR___redArg(v_passPipeline_2060_, v___x_2059_);
    return v___x_2061_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg(
    mut v_a_2062_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_acNf_2064_: u8 = 0;
    let mut v_andFlattening_2065_: u8 = 0;
    let mut v_embeddedConstraintSubst_2066_: u8 = 0;
    let mut v_passPipeline_2068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_passPipeline_2074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_passPipeline_2077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_acNf_2064_ = lean_ctor_get_uint8(
                    v_a_2062_,
                    (core::mem::size_of::<*mut LeanObject>() * 2 + 2) as u32,
                );
                v_andFlattening_2065_ = lean_ctor_get_uint8(
                    v_a_2062_,
                    (core::mem::size_of::<*mut LeanObject>() * 2 + 3) as u32,
                );
                v_embeddedConstraintSubst_2066_ = lean_ctor_get_uint8(
                    v_a_2062_,
                    (core::mem::size_of::<*mut LeanObject>() * 2 + 4) as u32,
                );
                v_passPipeline_2077_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__2_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__2);
                if v_acNf_2064_ == 0 {
                    v_passPipeline_2074_ = v_passPipeline_2077_;
                    state = 2;
                    continue;
                } else {
                    v___x_2078_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__4_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__4);
                    v_passPipeline_2074_ = v___x_2078_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                if v_embeddedConstraintSubst_2066_ == 0 {
                    v___x_2069_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2069_, 0, v_passPipeline_2068_);
                    return v___x_2069_;
                } else {
                    v___x_2070_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__0_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__0);
                    v___x_2071_ = l_List_appendTR___redArg(v_passPipeline_2068_, v___x_2070_);
                    v___x_2072_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2072_, 0, v___x_2071_);
                    return v___x_2072_;
                }
            }
            2 => {
                if v_embeddedConstraintSubst_2066_ == 0 {
                    lean_inc(v_passPipeline_2074_);
                    v_passPipeline_2068_ = v_passPipeline_2074_;
                    state = 1;
                    continue;
                } else {
                    if v_andFlattening_2065_ == 0 {
                        lean_inc(v_passPipeline_2074_);
                        v_passPipeline_2068_ = v_passPipeline_2074_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2075_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__1_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__1);
                        lean_inc(v_passPipeline_2074_);
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
    mut v_a_2079_: *mut LeanObject,
    mut v_a_2080_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2081_: *mut LeanObject = core::ptr::null_mut();
    v_res_2081_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg(v_a_2079_);
    lean_dec_ref(v_a_2079_);
    return v_res_2081_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline(
    mut v_a_2082_: *mut LeanObject,
    mut v_a_2083_: *mut LeanObject,
    mut v_a_2084_: *mut LeanObject,
    mut v_a_2085_: *mut LeanObject,
    mut v_a_2086_: *mut LeanObject,
    mut v_a_2087_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2089_: *mut LeanObject = core::ptr::null_mut();
    v___x_2089_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg(v_a_2082_);
    return v___x_2089_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___boxed(
    mut v_a_2090_: *mut LeanObject,
    mut v_a_2091_: *mut LeanObject,
    mut v_a_2092_: *mut LeanObject,
    mut v_a_2093_: *mut LeanObject,
    mut v_a_2094_: *mut LeanObject,
    mut v_a_2095_: *mut LeanObject,
    mut v_a_2096_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2097_: *mut LeanObject = core::ptr::null_mut();
    v_res_2097_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline(v_a_2090_, v_a_2091_, v_a_2092_, v_a_2093_, v_a_2094_, v_a_2095_);
    lean_dec(v_a_2095_);
    lean_dec_ref(v_a_2094_);
    lean_dec(v_a_2093_);
    lean_dec_ref(v_a_2092_);
    lean_dec(v_a_2091_);
    lean_dec_ref(v_a_2090_);
    return v_res_2097_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_2098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut LeanObject = core::ptr::null_mut();
    v___x_2098_ = lean_unsigned_to_nat(32);
    v___x_2099_ = lean_mk_empty_array_with_capacity(v___x_2098_);
    v___x_2100_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2100_, 0, v___x_2099_);
    return v___x_2100_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_2101_: usize = 0;
    let mut v___x_2102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut LeanObject = core::ptr::null_mut();
    v___x_2101_ = 5usize;
    v___x_2102_ = lean_unsigned_to_nat(0);
    v___x_2103_ = lean_unsigned_to_nat(32);
    v___x_2104_ = lean_mk_empty_array_with_capacity(v___x_2103_);
    v___x_2105_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___redArg___closed__0_once), _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___redArg___closed__0);
    v___x_2106_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_2106_, 0, v___x_2105_);
    lean_ctor_set(v___x_2106_, 1, v___x_2104_);
    lean_ctor_set(v___x_2106_, 2, v___x_2102_);
    lean_ctor_set(v___x_2106_, 3, v___x_2102_);
    lean_ctor_set_usize(v___x_2106_, 4, v___x_2101_);
    return v___x_2106_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___redArg(
    mut v___y_2107_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_2110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traces_2111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_2113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_2116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_2118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_2119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_2120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2124_: u8 = 0;
    let mut v_tid_2125_: u64 = 0;
    let mut v___x_2127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2128_: u8 = 0;
    let mut v___x_2129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2138_: u8 = 0;
    let mut v_unused_2139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2140_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2109_ = lean_st_ref_get(v___y_2107_);
                v_traceState_2110_ = lean_ctor_get(v___x_2109_, 4);
                lean_inc_ref(v_traceState_2110_);
                lean_dec(v___x_2109_);
                v_traces_2111_ = lean_ctor_get(v_traceState_2110_, 0);
                lean_inc_ref(v_traces_2111_);
                lean_dec_ref(v_traceState_2110_);
                v___x_2112_ = lean_st_ref_take(v___y_2107_);
                v_traceState_2113_ = lean_ctor_get(v___x_2112_, 4);
                v_env_2114_ = lean_ctor_get(v___x_2112_, 0);
                v_nextMacroScope_2115_ = lean_ctor_get(v___x_2112_, 1);
                v_ngen_2116_ = lean_ctor_get(v___x_2112_, 2);
                v_auxDeclNGen_2117_ = lean_ctor_get(v___x_2112_, 3);
                v_cache_2118_ = lean_ctor_get(v___x_2112_, 5);
                v_messages_2119_ = lean_ctor_get(v___x_2112_, 6);
                v_infoState_2120_ = lean_ctor_get(v___x_2112_, 7);
                v_snapshotTasks_2121_ = lean_ctor_get(v___x_2112_, 8);
                v_isSharedCheck_2140_ = (!lean_is_exclusive(v___x_2112_)) as u8;
                if v_isSharedCheck_2140_ == 0 {
                    v___x_2123_ = v___x_2112_;
                    v_isShared_2124_ = v_isSharedCheck_2140_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_2121_);
                    lean_inc(v_infoState_2120_);
                    lean_inc(v_messages_2119_);
                    lean_inc(v_cache_2118_);
                    lean_inc(v_traceState_2113_);
                    lean_inc(v_auxDeclNGen_2117_);
                    lean_inc(v_ngen_2116_);
                    lean_inc(v_nextMacroScope_2115_);
                    lean_inc(v_env_2114_);
                    lean_dec(v___x_2112_);
                    v___x_2123_ = lean_box(0);
                    v_isShared_2124_ = v_isSharedCheck_2140_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_tid_2125_ = lean_ctor_get_uint64(
                    v_traceState_2113_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_2138_ = (!lean_is_exclusive(v_traceState_2113_)) as u8;
                if v_isSharedCheck_2138_ == 0 {
                    v_unused_2139_ = lean_ctor_get(v_traceState_2113_, 0);
                    lean_dec(v_unused_2139_);
                    v___x_2127_ = v_traceState_2113_;
                    v_isShared_2128_ = v_isSharedCheck_2138_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_traceState_2113_);
                    v___x_2127_ = lean_box(0);
                    v_isShared_2128_ = v_isSharedCheck_2138_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2129_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___redArg___closed__1_once), _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___redArg___closed__1);
                if v_isShared_2128_ == 0 {
                    lean_ctor_set(v___x_2127_, 0, v___x_2129_);
                    v___x_2131_ = v___x_2127_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2137_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2137_, 0, v___x_2129_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_2137_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_2125_,
                    );
                    v___x_2131_ = v_reuseFailAlloc_2137_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2124_ == 0 {
                    lean_ctor_set(v___x_2123_, 4, v___x_2131_);
                    v___x_2133_ = v___x_2123_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2136_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_env_2114_);
                    lean_ctor_set(v_reuseFailAlloc_2136_, 1, v_nextMacroScope_2115_);
                    lean_ctor_set(v_reuseFailAlloc_2136_, 2, v_ngen_2116_);
                    lean_ctor_set(v_reuseFailAlloc_2136_, 3, v_auxDeclNGen_2117_);
                    lean_ctor_set(v_reuseFailAlloc_2136_, 4, v___x_2131_);
                    lean_ctor_set(v_reuseFailAlloc_2136_, 5, v_cache_2118_);
                    lean_ctor_set(v_reuseFailAlloc_2136_, 6, v_messages_2119_);
                    lean_ctor_set(v_reuseFailAlloc_2136_, 7, v_infoState_2120_);
                    lean_ctor_set(v_reuseFailAlloc_2136_, 8, v_snapshotTasks_2121_);
                    v___x_2133_ = v_reuseFailAlloc_2136_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2134_ = lean_st_ref_set(v___y_2107_, v___x_2133_);
                v___x_2135_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2135_, 0, v_traces_2111_);
                return v___x_2135_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___redArg___boxed(
    mut v___y_2141_: *mut LeanObject,
    mut v___y_2142_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2143_: *mut LeanObject = core::ptr::null_mut();
    v_res_2143_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___redArg(v___y_2141_);
    lean_dec(v___y_2141_);
    return v_res_2143_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0(
    mut v___y_2144_: *mut LeanObject,
    mut v___y_2145_: *mut LeanObject,
    mut v___y_2146_: *mut LeanObject,
    mut v___y_2147_: *mut LeanObject,
    mut v___y_2148_: *mut LeanObject,
    mut v___y_2149_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2151_: *mut LeanObject = core::ptr::null_mut();
    v___x_2151_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___redArg(v___y_2149_);
    return v___x_2151_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___boxed(
    mut v___y_2152_: *mut LeanObject,
    mut v___y_2153_: *mut LeanObject,
    mut v___y_2154_: *mut LeanObject,
    mut v___y_2155_: *mut LeanObject,
    mut v___y_2156_: *mut LeanObject,
    mut v___y_2157_: *mut LeanObject,
    mut v___y_2158_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2159_: *mut LeanObject = core::ptr::null_mut();
    v_res_2159_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0(v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_);
    lean_dec(v___y_2157_);
    lean_dec_ref(v___y_2156_);
    lean_dec(v___y_2155_);
    lean_dec_ref(v___y_2154_);
    lean_dec(v___y_2153_);
    lean_dec_ref(v___y_2152_);
    return v_res_2159_;
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__1(
    mut v_opts_2160_: *mut LeanObject,
    mut v_opt_2161_: *mut LeanObject,
) -> u8 {
    let mut v_name_2162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_2163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_2164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut LeanObject = core::ptr::null_mut();
    v_name_2162_ = lean_ctor_get(v_opt_2161_, 0);
    v_defValue_2163_ = lean_ctor_get(v_opt_2161_, 1);
    v_map_2164_ = lean_ctor_get(v_opts_2160_, 0);
    v___x_2165_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2164_,
            v_name_2162_,
        );
    if lean_obj_tag(v___x_2165_) == 0 {
        let mut v___x_2166_: u8 = 0;
        v___x_2166_ = (lean_unbox(v_defValue_2163_) as u8);
        return v___x_2166_;
    } else {
        let mut v_val_2167_: *mut LeanObject = core::ptr::null_mut();
        v_val_2167_ = lean_ctor_get(v___x_2165_, 0);
        lean_inc(v_val_2167_);
        lean_dec_ref_known(v___x_2165_, 1);
        if lean_obj_tag(v_val_2167_) == 1 {
            let mut v_v_2168_: u8 = 0;
            v_v_2168_ = lean_ctor_get_uint8(v_val_2167_, 0 as u32);
            lean_dec_ref_known(v_val_2167_, 0);
            return v_v_2168_;
        } else {
            let mut v___x_2169_: u8 = 0;
            lean_dec(v_val_2167_);
            v___x_2169_ = (lean_unbox(v_defValue_2163_) as u8);
            return v___x_2169_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__1___boxed(
    mut v_opts_2170_: *mut LeanObject,
    mut v_opt_2171_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2172_: u8 = 0;
    let mut v_r_2173_: *mut LeanObject = core::ptr::null_mut();
    v_res_2172_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__1(v_opts_2170_, v_opt_2171_);
    lean_dec_ref(v_opt_2171_);
    lean_dec_ref(v_opts_2170_);
    v_r_2173_ = lean_box((v_res_2172_) as usize);
    return v_r_2173_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__1()
-> *mut LeanObject {
    let mut v___x_2175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut LeanObject = core::ptr::null_mut();
    v___x_2175_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__0;
    v___x_2176_ = l_Lean_stringToMessageData(v___x_2175_);
    return v___x_2176_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__3()
-> *mut LeanObject {
    let mut v___x_2178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut LeanObject = core::ptr::null_mut();
    v___x_2178_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__2;
    v___x_2179_ = l_Lean_stringToMessageData(v___x_2178_);
    return v___x_2179_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0(
    mut v___x_2180_: *mut LeanObject,
    mut v_val_2181_: *mut LeanObject,
    mut v_x_2182_: *mut LeanObject,
    mut v___y_2183_: *mut LeanObject,
    mut v___y_2184_: *mut LeanObject,
    mut v___y_2185_: *mut LeanObject,
    mut v___y_2186_: *mut LeanObject,
    mut v___y_2187_: *mut LeanObject,
    mut v___y_2188_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_2190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2193_: u8 = 0;
    let mut v___x_2194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2204_: u8 = 0;
    let mut v_unused_2205_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_2190_ = lean_ctor_get(v___x_2180_, 0);
                v_isSharedCheck_2204_ = (!lean_is_exclusive(v___x_2180_)) as u8;
                if v_isSharedCheck_2204_ == 0 {
                    v_unused_2205_ = lean_ctor_get(v___x_2180_, 1);
                    lean_dec(v_unused_2205_);
                    v___x_2192_ = v___x_2180_;
                    v_isShared_2193_ = v_isSharedCheck_2204_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_name_2190_);
                    lean_dec(v___x_2180_);
                    v___x_2192_ = lean_box(0);
                    v_isShared_2193_ = v_isSharedCheck_2204_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2194_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__1_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__1);
                v___x_2195_ = l_Lean_MessageData_ofName(v_name_2190_);
                if v_isShared_2193_ == 0 {
                    lean_ctor_set_tag(v___x_2192_, 7);
                    lean_ctor_set(v___x_2192_, 1, v___x_2195_);
                    lean_ctor_set(v___x_2192_, 0, v___x_2194_);
                    v___x_2197_ = v___x_2192_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2203_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2203_, 0, v___x_2194_);
                    lean_ctor_set(v_reuseFailAlloc_2203_, 1, v___x_2195_);
                    v___x_2197_ = v_reuseFailAlloc_2203_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2198_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__3_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__3);
                v___x_2199_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2199_, 0, v___x_2197_);
                lean_ctor_set(v___x_2199_, 1, v___x_2198_);
                v___x_2200_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2200_, 0, v_val_2181_);
                v___x_2201_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2201_, 0, v___x_2199_);
                lean_ctor_set(v___x_2201_, 1, v___x_2200_);
                v___x_2202_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2202_, 0, v___x_2201_);
                return v___x_2202_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___boxed(
    mut v___x_2206_: *mut LeanObject,
    mut v_val_2207_: *mut LeanObject,
    mut v_x_2208_: *mut LeanObject,
    mut v___y_2209_: *mut LeanObject,
    mut v___y_2210_: *mut LeanObject,
    mut v___y_2211_: *mut LeanObject,
    mut v___y_2212_: *mut LeanObject,
    mut v___y_2213_: *mut LeanObject,
    mut v___y_2214_: *mut LeanObject,
    mut v___y_2215_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2216_: *mut LeanObject = core::ptr::null_mut();
    v_res_2216_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0(v___x_2206_, v_val_2207_, v_x_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_);
    lean_dec(v___y_2214_);
    lean_dec_ref(v___y_2213_);
    lean_dec(v___y_2212_);
    lean_dec_ref(v___y_2211_);
    lean_dec(v___y_2210_);
    lean_dec_ref(v___y_2209_);
    lean_dec_ref(v_x_2208_);
    return v_res_2216_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__1(
    mut v___x_2217_: *mut LeanObject,
    mut v_g_2218_: *mut LeanObject,
    mut v_x_2219_: *mut LeanObject,
    mut v___y_2220_: *mut LeanObject,
    mut v___y_2221_: *mut LeanObject,
    mut v___y_2222_: *mut LeanObject,
    mut v___y_2223_: *mut LeanObject,
    mut v___y_2224_: *mut LeanObject,
    mut v___y_2225_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_2227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2230_: u8 = 0;
    let mut v___x_2231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2241_: u8 = 0;
    let mut v_unused_2242_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_2227_ = lean_ctor_get(v___x_2217_, 0);
                v_isSharedCheck_2241_ = (!lean_is_exclusive(v___x_2217_)) as u8;
                if v_isSharedCheck_2241_ == 0 {
                    v_unused_2242_ = lean_ctor_get(v___x_2217_, 1);
                    lean_dec(v_unused_2242_);
                    v___x_2229_ = v___x_2217_;
                    v_isShared_2230_ = v_isSharedCheck_2241_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_name_2227_);
                    lean_dec(v___x_2217_);
                    v___x_2229_ = lean_box(0);
                    v_isShared_2230_ = v_isSharedCheck_2241_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2231_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__1_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__1);
                v___x_2232_ = l_Lean_MessageData_ofName(v_name_2227_);
                if v_isShared_2230_ == 0 {
                    lean_ctor_set_tag(v___x_2229_, 7);
                    lean_ctor_set(v___x_2229_, 1, v___x_2232_);
                    lean_ctor_set(v___x_2229_, 0, v___x_2231_);
                    v___x_2234_ = v___x_2229_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2240_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2240_, 0, v___x_2231_);
                    lean_ctor_set(v_reuseFailAlloc_2240_, 1, v___x_2232_);
                    v___x_2234_ = v_reuseFailAlloc_2240_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2235_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__3_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__3);
                v___x_2236_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2236_, 0, v___x_2234_);
                lean_ctor_set(v___x_2236_, 1, v___x_2235_);
                v___x_2237_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2237_, 0, v_g_2218_);
                v___x_2238_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2238_, 0, v___x_2236_);
                lean_ctor_set(v___x_2238_, 1, v___x_2237_);
                v___x_2239_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2239_, 0, v___x_2238_);
                return v___x_2239_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__1___boxed(
    mut v___x_2243_: *mut LeanObject,
    mut v_g_2244_: *mut LeanObject,
    mut v_x_2245_: *mut LeanObject,
    mut v___y_2246_: *mut LeanObject,
    mut v___y_2247_: *mut LeanObject,
    mut v___y_2248_: *mut LeanObject,
    mut v___y_2249_: *mut LeanObject,
    mut v___y_2250_: *mut LeanObject,
    mut v___y_2251_: *mut LeanObject,
    mut v___y_2252_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2253_: *mut LeanObject = core::ptr::null_mut();
    v_res_2253_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__1(v___x_2243_, v_g_2244_, v_x_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_);
    lean_dec(v___y_2251_);
    lean_dec_ref(v___y_2250_);
    lean_dec(v___y_2249_);
    lean_dec_ref(v___y_2248_);
    lean_dec(v___y_2247_);
    lean_dec_ref(v___y_2246_);
    lean_dec_ref(v_x_2245_);
    return v_res_2253_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3_spec__7(
    mut v_msgData_2254_: *mut LeanObject,
    mut v___y_2255_: *mut LeanObject,
    mut v___y_2256_: *mut LeanObject,
    mut v___y_2257_: *mut LeanObject,
    mut v___y_2258_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_2263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_2264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut LeanObject = core::ptr::null_mut();
    v___x_2260_ = lean_st_ref_get(v___y_2258_);
    v_env_2261_ = lean_ctor_get(v___x_2260_, 0);
    lean_inc_ref(v_env_2261_);
    lean_dec(v___x_2260_);
    v___x_2262_ = lean_st_ref_get(v___y_2256_);
    v_mctx_2263_ = lean_ctor_get(v___x_2262_, 0);
    lean_inc_ref(v_mctx_2263_);
    lean_dec(v___x_2262_);
    v_lctx_2264_ = lean_ctor_get(v___y_2255_, 2);
    v_options_2265_ = lean_ctor_get(v___y_2257_, 2);
    lean_inc_ref(v_options_2265_);
    lean_inc_ref(v_lctx_2264_);
    v___x_2266_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_2266_, 0, v_env_2261_);
    lean_ctor_set(v___x_2266_, 1, v_mctx_2263_);
    lean_ctor_set(v___x_2266_, 2, v_lctx_2264_);
    lean_ctor_set(v___x_2266_, 3, v_options_2265_);
    v___x_2267_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_2267_, 0, v___x_2266_);
    lean_ctor_set(v___x_2267_, 1, v_msgData_2254_);
    v___x_2268_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2268_, 0, v___x_2267_);
    return v___x_2268_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3_spec__7___boxed(
    mut v_msgData_2269_: *mut LeanObject,
    mut v___y_2270_: *mut LeanObject,
    mut v___y_2271_: *mut LeanObject,
    mut v___y_2272_: *mut LeanObject,
    mut v___y_2273_: *mut LeanObject,
    mut v___y_2274_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2275_: *mut LeanObject = core::ptr::null_mut();
    v_res_2275_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3_spec__7(v_msgData_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_);
    lean_dec(v___y_2273_);
    lean_dec_ref(v___y_2272_);
    lean_dec(v___y_2271_);
    lean_dec_ref(v___y_2270_);
    return v_res_2275_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__0()
-> f64 {
    let mut v___x_2276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: f64 = 0.0;
    v___x_2276_ = lean_unsigned_to_nat(0);
    v___x_2277_ = lean_float_of_nat(v___x_2276_);
    return v___x_2277_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg(
    mut v_cls_2281_: *mut LeanObject,
    mut v_msg_2282_: *mut LeanObject,
    mut v___y_2283_: *mut LeanObject,
    mut v___y_2284_: *mut LeanObject,
    mut v___y_2285_: *mut LeanObject,
    mut v___y_2286_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_2288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2293_: u8 = 0;
    let mut v___x_2294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_2295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_2298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_2300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_2301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_2302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2306_: u8 = 0;
    let mut v_tid_2307_: u64 = 0;
    let mut v_traces_2308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2311_: u8 = 0;
    let mut v___x_2312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: f64 = 0.0;
    let mut v___x_2314_: u8 = 0;
    let mut v___x_2315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2332_: u8 = 0;
    let mut v_isSharedCheck_2333_: u8 = 0;
    let mut v_isSharedCheck_2334_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2288_ = lean_ctor_get(v___y_2285_, 5);
                v___x_2289_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3_spec__7(v_msg_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_);
                v_a_2290_ = lean_ctor_get(v___x_2289_, 0);
                v_isSharedCheck_2334_ = (!lean_is_exclusive(v___x_2289_)) as u8;
                if v_isSharedCheck_2334_ == 0 {
                    v___x_2292_ = v___x_2289_;
                    v_isShared_2293_ = v_isSharedCheck_2334_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_2290_);
                    lean_dec(v___x_2289_);
                    v___x_2292_ = lean_box(0);
                    v_isShared_2293_ = v_isSharedCheck_2334_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2294_ = lean_st_ref_take(v___y_2286_);
                v_traceState_2295_ = lean_ctor_get(v___x_2294_, 4);
                v_env_2296_ = lean_ctor_get(v___x_2294_, 0);
                v_nextMacroScope_2297_ = lean_ctor_get(v___x_2294_, 1);
                v_ngen_2298_ = lean_ctor_get(v___x_2294_, 2);
                v_auxDeclNGen_2299_ = lean_ctor_get(v___x_2294_, 3);
                v_cache_2300_ = lean_ctor_get(v___x_2294_, 5);
                v_messages_2301_ = lean_ctor_get(v___x_2294_, 6);
                v_infoState_2302_ = lean_ctor_get(v___x_2294_, 7);
                v_snapshotTasks_2303_ = lean_ctor_get(v___x_2294_, 8);
                v_isSharedCheck_2333_ = (!lean_is_exclusive(v___x_2294_)) as u8;
                if v_isSharedCheck_2333_ == 0 {
                    v___x_2305_ = v___x_2294_;
                    v_isShared_2306_ = v_isSharedCheck_2333_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_2303_);
                    lean_inc(v_infoState_2302_);
                    lean_inc(v_messages_2301_);
                    lean_inc(v_cache_2300_);
                    lean_inc(v_traceState_2295_);
                    lean_inc(v_auxDeclNGen_2299_);
                    lean_inc(v_ngen_2298_);
                    lean_inc(v_nextMacroScope_2297_);
                    lean_inc(v_env_2296_);
                    lean_dec(v___x_2294_);
                    v___x_2305_ = lean_box(0);
                    v_isShared_2306_ = v_isSharedCheck_2333_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_2307_ = lean_ctor_get_uint64(
                    v_traceState_2295_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_traces_2308_ = lean_ctor_get(v_traceState_2295_, 0);
                v_isSharedCheck_2332_ = (!lean_is_exclusive(v_traceState_2295_)) as u8;
                if v_isSharedCheck_2332_ == 0 {
                    v___x_2310_ = v_traceState_2295_;
                    v_isShared_2311_ = v_isSharedCheck_2332_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_traces_2308_);
                    lean_dec(v_traceState_2295_);
                    v___x_2310_ = lean_box(0);
                    v_isShared_2311_ = v_isSharedCheck_2332_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2312_ = lean_box(0);
                v___x_2313_ = lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__0_once), _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__0);
                v___x_2314_ = 0;
                v___x_2315_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__1;
                v___x_2316_ = lean_alloc_ctor(0, 3, (17) as u32);
                lean_ctor_set(v___x_2316_, 0, v_cls_2281_);
                lean_ctor_set(v___x_2316_, 1, v___x_2312_);
                lean_ctor_set(v___x_2316_, 2, v___x_2315_);
                lean_ctor_set_float(
                    v___x_2316_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_2313_,
                );
                lean_ctor_set_float(
                    v___x_2316_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    v___x_2313_,
                );
                lean_ctor_set_uint8(
                    v___x_2316_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                    v___x_2314_,
                );
                v___x_2317_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__2;
                v___x_2318_ = lean_alloc_ctor(9, 3, (0) as u32);
                lean_ctor_set(v___x_2318_, 0, v___x_2316_);
                lean_ctor_set(v___x_2318_, 1, v_a_2290_);
                lean_ctor_set(v___x_2318_, 2, v___x_2317_);
                lean_inc(v_ref_2288_);
                v___x_2319_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2319_, 0, v_ref_2288_);
                lean_ctor_set(v___x_2319_, 1, v___x_2318_);
                v___x_2320_ = l_Lean_PersistentArray_push___redArg(v_traces_2308_, v___x_2319_);
                if v_isShared_2311_ == 0 {
                    lean_ctor_set(v___x_2310_, 0, v___x_2320_);
                    v___x_2322_ = v___x_2310_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2331_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2331_, 0, v___x_2320_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_2331_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_2307_,
                    );
                    v___x_2322_ = v_reuseFailAlloc_2331_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2306_ == 0 {
                    lean_ctor_set(v___x_2305_, 4, v___x_2322_);
                    v___x_2324_ = v___x_2305_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2330_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2330_, 0, v_env_2296_);
                    lean_ctor_set(v_reuseFailAlloc_2330_, 1, v_nextMacroScope_2297_);
                    lean_ctor_set(v_reuseFailAlloc_2330_, 2, v_ngen_2298_);
                    lean_ctor_set(v_reuseFailAlloc_2330_, 3, v_auxDeclNGen_2299_);
                    lean_ctor_set(v_reuseFailAlloc_2330_, 4, v___x_2322_);
                    lean_ctor_set(v_reuseFailAlloc_2330_, 5, v_cache_2300_);
                    lean_ctor_set(v_reuseFailAlloc_2330_, 6, v_messages_2301_);
                    lean_ctor_set(v_reuseFailAlloc_2330_, 7, v_infoState_2302_);
                    lean_ctor_set(v_reuseFailAlloc_2330_, 8, v_snapshotTasks_2303_);
                    v___x_2324_ = v_reuseFailAlloc_2330_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2325_ = lean_st_ref_set(v___y_2286_, v___x_2324_);
                v___x_2326_ = lean_box(0);
                if v_isShared_2293_ == 0 {
                    lean_ctor_set(v___x_2292_, 0, v___x_2326_);
                    v___x_2328_ = v___x_2292_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2329_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2329_, 0, v___x_2326_);
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
    mut v_cls_2335_: *mut LeanObject,
    mut v_msg_2336_: *mut LeanObject,
    mut v___y_2337_: *mut LeanObject,
    mut v___y_2338_: *mut LeanObject,
    mut v___y_2339_: *mut LeanObject,
    mut v___y_2340_: *mut LeanObject,
    mut v___y_2341_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2342_: *mut LeanObject = core::ptr::null_mut();
    v_res_2342_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg(v_cls_2335_, v_msg_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_);
    lean_dec(v___y_2340_);
    lean_dec_ref(v___y_2339_);
    lean_dec(v___y_2338_);
    lean_dec_ref(v___y_2337_);
    return v_res_2342_;
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__5(
    mut v_opts_2343_: *mut LeanObject,
    mut v_opt_2344_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_2345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_2346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_2347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut LeanObject = core::ptr::null_mut();
    v_name_2345_ = lean_ctor_get(v_opt_2344_, 0);
    v_defValue_2346_ = lean_ctor_get(v_opt_2344_, 1);
    v_map_2347_ = lean_ctor_get(v_opts_2343_, 0);
    v___x_2348_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2347_,
            v_name_2345_,
        );
    if lean_obj_tag(v___x_2348_) == 0 {
        lean_inc(v_defValue_2346_);
        return v_defValue_2346_;
    } else {
        let mut v_val_2349_: *mut LeanObject = core::ptr::null_mut();
        v_val_2349_ = lean_ctor_get(v___x_2348_, 0);
        lean_inc(v_val_2349_);
        lean_dec_ref_known(v___x_2348_, 1);
        if lean_obj_tag(v_val_2349_) == 3 {
            let mut v_v_2350_: *mut LeanObject = core::ptr::null_mut();
            v_v_2350_ = lean_ctor_get(v_val_2349_, 0);
            lean_inc(v_v_2350_);
            lean_dec_ref_known(v_val_2349_, 1);
            return v_v_2350_;
        } else {
            lean_dec(v_val_2349_);
            lean_inc(v_defValue_2346_);
            return v_defValue_2346_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__5___boxed(
    mut v_opts_2351_: *mut LeanObject,
    mut v_opt_2352_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2353_: *mut LeanObject = core::ptr::null_mut();
    v_res_2353_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__5(v_opts_2351_, v_opt_2352_);
    lean_dec_ref(v_opt_2352_);
    lean_dec_ref(v_opts_2351_);
    return v_res_2353_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__4___redArg(
    mut v_x_2354_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2359_: u8 = 0;
    let mut v___x_2361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2363_: u8 = 0;
    let mut v_a_2364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2367_: u8 = 0;
    let mut v___x_2369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2371_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2354_) == 0 {
                    v_a_2356_ = lean_ctor_get(v_x_2354_, 0);
                    v_isSharedCheck_2363_ = (!lean_is_exclusive(v_x_2354_)) as u8;
                    if v_isSharedCheck_2363_ == 0 {
                        v___x_2358_ = v_x_2354_;
                        v_isShared_2359_ = v_isSharedCheck_2363_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2356_);
                        lean_dec(v_x_2354_);
                        v___x_2358_ = lean_box(0);
                        v_isShared_2359_ = v_isSharedCheck_2363_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2364_ = lean_ctor_get(v_x_2354_, 0);
                    v_isSharedCheck_2371_ = (!lean_is_exclusive(v_x_2354_)) as u8;
                    if v_isSharedCheck_2371_ == 0 {
                        v___x_2366_ = v_x_2354_;
                        v_isShared_2367_ = v_isSharedCheck_2371_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2364_);
                        lean_dec(v_x_2354_);
                        v___x_2366_ = lean_box(0);
                        v_isShared_2367_ = v_isSharedCheck_2371_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2359_ == 0 {
                    lean_ctor_set_tag(v___x_2358_, 1);
                    v___x_2361_ = v___x_2358_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2362_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2362_, 0, v_a_2356_);
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
                    lean_ctor_set_tag(v___x_2366_, 0);
                    v___x_2369_ = v___x_2366_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2370_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2370_, 0, v_a_2364_);
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
    mut v_x_2372_: *mut LeanObject,
    mut v___y_2373_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2374_: *mut LeanObject = core::ptr::null_mut();
    v_res_2374_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__4___redArg(v_x_2372_);
    return v_res_2374_;
}
pub unsafe fn l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__2(
    mut v_e_2375_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_e_2375_) == 0 {
        let mut v___x_2376_: u8 = 0;
        v___x_2376_ = 2;
        return v___x_2376_;
    } else {
        let mut v_a_2377_: *mut LeanObject = core::ptr::null_mut();
        v_a_2377_ = lean_ctor_get(v_e_2375_, 0);
        if lean_obj_tag(v_a_2377_) == 0 {
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
    mut v_e_2380_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2381_: u8 = 0;
    let mut v_r_2382_: *mut LeanObject = core::ptr::null_mut();
    v_res_2381_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__2(v_e_2380_);
    lean_dec_ref(v_e_2380_);
    v_r_2382_ = lean_box((v_res_2381_) as usize);
    return v_r_2382_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__3_spec__4(
    mut v_sz_2383_: usize,
    mut v_i_2384_: usize,
    mut v_bs_2385_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2386_: u8 = 0;
    let mut v_v_2387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msg_2388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: usize = 0;
    let mut v___x_2392_: usize = 0;
    let mut v___x_2393_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2386_ = lean_usize_dec_lt(v_i_2384_, v_sz_2383_);
                if v___x_2386_ == 0 {
                    return v_bs_2385_;
                } else {
                    v_v_2387_ = lean_array_uget_borrowed(v_bs_2385_, v_i_2384_);
                    v_msg_2388_ = lean_ctor_get(v_v_2387_, 1);
                    lean_inc_ref(v_msg_2388_);
                    v___x_2389_ = lean_unsigned_to_nat(0);
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
    mut v_sz_2395_: *mut LeanObject,
    mut v_i_2396_: *mut LeanObject,
    mut v_bs_2397_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2398_: usize = 0;
    let mut v_i_boxed_2399_: usize = 0;
    let mut v_res_2400_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2398_ = lean_unbox_usize(v_sz_2395_);
    lean_dec(v_sz_2395_);
    v_i_boxed_2399_ = lean_unbox_usize(v_i_2396_);
    lean_dec(v_i_2396_);
    v_res_2400_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__3_spec__4(v_sz_boxed_2398_, v_i_boxed_2399_, v_bs_2397_);
    return v_res_2400_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__3___redArg(
    mut v_oldTraces_2401_: *mut LeanObject,
    mut v_data_2402_: *mut LeanObject,
    mut v_ref_2403_: *mut LeanObject,
    mut v_msg_2404_: *mut LeanObject,
    mut v___y_2405_: *mut LeanObject,
    mut v___y_2406_: *mut LeanObject,
    mut v___y_2407_: *mut LeanObject,
    mut v___y_2408_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_2410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_2418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_2419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_2422_: u8 = 0;
    let mut v_cancelTk_x3f_2423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2424_: u8 = 0;
    let mut v_inheritedTraceOptions_2425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_2427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traces_2428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2432_: usize = 0;
    let mut v___x_2433_: usize = 0;
    let mut v___x_2434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msg_2435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2440_: u8 = 0;
    let mut v___x_2441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_2442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_2445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_2447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_2448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_2449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2453_: u8 = 0;
    let mut v_tid_2454_: u64 = 0;
    let mut v___x_2456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2457_: u8 = 0;
    let mut v___x_2458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2471_: u8 = 0;
    let mut v_unused_2472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2473_: u8 = 0;
    let mut v_isSharedCheck_2474_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_2410_ = lean_ctor_get(v___y_2407_, 0);
                v_fileMap_2411_ = lean_ctor_get(v___y_2407_, 1);
                v_options_2412_ = lean_ctor_get(v___y_2407_, 2);
                v_currRecDepth_2413_ = lean_ctor_get(v___y_2407_, 3);
                v_maxRecDepth_2414_ = lean_ctor_get(v___y_2407_, 4);
                v_ref_2415_ = lean_ctor_get(v___y_2407_, 5);
                v_currNamespace_2416_ = lean_ctor_get(v___y_2407_, 6);
                v_openDecls_2417_ = lean_ctor_get(v___y_2407_, 7);
                v_initHeartbeats_2418_ = lean_ctor_get(v___y_2407_, 8);
                v_maxHeartbeats_2419_ = lean_ctor_get(v___y_2407_, 9);
                v_quotContext_2420_ = lean_ctor_get(v___y_2407_, 10);
                v_currMacroScope_2421_ = lean_ctor_get(v___y_2407_, 11);
                v_diag_2422_ = lean_ctor_get_uint8(
                    v___y_2407_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_2423_ = lean_ctor_get(v___y_2407_, 12);
                v_suppressElabErrors_2424_ = lean_ctor_get_uint8(
                    v___y_2407_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_2425_ = lean_ctor_get(v___y_2407_, 13);
                v___x_2426_ = lean_st_ref_get(v___y_2408_);
                v_traceState_2427_ = lean_ctor_get(v___x_2426_, 4);
                lean_inc_ref(v_traceState_2427_);
                lean_dec(v___x_2426_);
                v_traces_2428_ = lean_ctor_get(v_traceState_2427_, 0);
                lean_inc_ref(v_traces_2428_);
                lean_dec_ref(v_traceState_2427_);
                v_ref_2429_ = l_Lean_replaceRef(v_ref_2403_, v_ref_2415_);
                lean_inc_ref(v_inheritedTraceOptions_2425_);
                lean_inc(v_cancelTk_x3f_2423_);
                lean_inc(v_currMacroScope_2421_);
                lean_inc(v_quotContext_2420_);
                lean_inc(v_maxHeartbeats_2419_);
                lean_inc(v_initHeartbeats_2418_);
                lean_inc(v_openDecls_2417_);
                lean_inc(v_currNamespace_2416_);
                lean_inc(v_maxRecDepth_2414_);
                lean_inc(v_currRecDepth_2413_);
                lean_inc_ref(v_options_2412_);
                lean_inc_ref(v_fileMap_2411_);
                lean_inc_ref(v_fileName_2410_);
                v___x_2430_ = lean_alloc_ctor(0, 14, (2) as u32);
                lean_ctor_set(v___x_2430_, 0, v_fileName_2410_);
                lean_ctor_set(v___x_2430_, 1, v_fileMap_2411_);
                lean_ctor_set(v___x_2430_, 2, v_options_2412_);
                lean_ctor_set(v___x_2430_, 3, v_currRecDepth_2413_);
                lean_ctor_set(v___x_2430_, 4, v_maxRecDepth_2414_);
                lean_ctor_set(v___x_2430_, 5, v_ref_2429_);
                lean_ctor_set(v___x_2430_, 6, v_currNamespace_2416_);
                lean_ctor_set(v___x_2430_, 7, v_openDecls_2417_);
                lean_ctor_set(v___x_2430_, 8, v_initHeartbeats_2418_);
                lean_ctor_set(v___x_2430_, 9, v_maxHeartbeats_2419_);
                lean_ctor_set(v___x_2430_, 10, v_quotContext_2420_);
                lean_ctor_set(v___x_2430_, 11, v_currMacroScope_2421_);
                lean_ctor_set(v___x_2430_, 12, v_cancelTk_x3f_2423_);
                lean_ctor_set(v___x_2430_, 13, v_inheritedTraceOptions_2425_);
                lean_ctor_set_uint8(
                    v___x_2430_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    v_diag_2422_,
                );
                lean_ctor_set_uint8(
                    v___x_2430_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_2424_,
                );
                v___x_2431_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2428_);
                lean_dec_ref(v_traces_2428_);
                v_sz_2432_ = lean_array_size(v___x_2431_);
                v___x_2433_ = 0usize;
                v___x_2434_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__3_spec__4(v_sz_2432_, v___x_2433_, v___x_2431_);
                v_msg_2435_ = lean_alloc_ctor(9, 3, (0) as u32);
                lean_ctor_set(v_msg_2435_, 0, v_data_2402_);
                lean_ctor_set(v_msg_2435_, 1, v_msg_2404_);
                lean_ctor_set(v_msg_2435_, 2, v___x_2434_);
                v___x_2436_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3_spec__7(v_msg_2435_, v___y_2405_, v___y_2406_, v___x_2430_, v___y_2408_);
                lean_dec_ref_known(v___x_2430_, 14);
                v_a_2437_ = lean_ctor_get(v___x_2436_, 0);
                v_isSharedCheck_2474_ = (!lean_is_exclusive(v___x_2436_)) as u8;
                if v_isSharedCheck_2474_ == 0 {
                    v___x_2439_ = v___x_2436_;
                    v_isShared_2440_ = v_isSharedCheck_2474_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_2437_);
                    lean_dec(v___x_2436_);
                    v___x_2439_ = lean_box(0);
                    v_isShared_2440_ = v_isSharedCheck_2474_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2441_ = lean_st_ref_take(v___y_2408_);
                v_traceState_2442_ = lean_ctor_get(v___x_2441_, 4);
                v_env_2443_ = lean_ctor_get(v___x_2441_, 0);
                v_nextMacroScope_2444_ = lean_ctor_get(v___x_2441_, 1);
                v_ngen_2445_ = lean_ctor_get(v___x_2441_, 2);
                v_auxDeclNGen_2446_ = lean_ctor_get(v___x_2441_, 3);
                v_cache_2447_ = lean_ctor_get(v___x_2441_, 5);
                v_messages_2448_ = lean_ctor_get(v___x_2441_, 6);
                v_infoState_2449_ = lean_ctor_get(v___x_2441_, 7);
                v_snapshotTasks_2450_ = lean_ctor_get(v___x_2441_, 8);
                v_isSharedCheck_2473_ = (!lean_is_exclusive(v___x_2441_)) as u8;
                if v_isSharedCheck_2473_ == 0 {
                    v___x_2452_ = v___x_2441_;
                    v_isShared_2453_ = v_isSharedCheck_2473_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_2450_);
                    lean_inc(v_infoState_2449_);
                    lean_inc(v_messages_2448_);
                    lean_inc(v_cache_2447_);
                    lean_inc(v_traceState_2442_);
                    lean_inc(v_auxDeclNGen_2446_);
                    lean_inc(v_ngen_2445_);
                    lean_inc(v_nextMacroScope_2444_);
                    lean_inc(v_env_2443_);
                    lean_dec(v___x_2441_);
                    v___x_2452_ = lean_box(0);
                    v_isShared_2453_ = v_isSharedCheck_2473_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_2454_ = lean_ctor_get_uint64(
                    v_traceState_2442_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_2471_ = (!lean_is_exclusive(v_traceState_2442_)) as u8;
                if v_isSharedCheck_2471_ == 0 {
                    v_unused_2472_ = lean_ctor_get(v_traceState_2442_, 0);
                    lean_dec(v_unused_2472_);
                    v___x_2456_ = v_traceState_2442_;
                    v_isShared_2457_ = v_isSharedCheck_2471_;
                    state = 3;
                    continue;
                } else {
                    lean_dec(v_traceState_2442_);
                    v___x_2456_ = lean_box(0);
                    v_isShared_2457_ = v_isSharedCheck_2471_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2458_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2458_, 0, v_ref_2403_);
                lean_ctor_set(v___x_2458_, 1, v_a_2437_);
                v___x_2459_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2401_, v___x_2458_);
                if v_isShared_2457_ == 0 {
                    lean_ctor_set(v___x_2456_, 0, v___x_2459_);
                    v___x_2461_ = v___x_2456_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2470_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2470_, 0, v___x_2459_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_2470_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_2454_,
                    );
                    v___x_2461_ = v_reuseFailAlloc_2470_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2453_ == 0 {
                    lean_ctor_set(v___x_2452_, 4, v___x_2461_);
                    v___x_2463_ = v___x_2452_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2469_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2469_, 0, v_env_2443_);
                    lean_ctor_set(v_reuseFailAlloc_2469_, 1, v_nextMacroScope_2444_);
                    lean_ctor_set(v_reuseFailAlloc_2469_, 2, v_ngen_2445_);
                    lean_ctor_set(v_reuseFailAlloc_2469_, 3, v_auxDeclNGen_2446_);
                    lean_ctor_set(v_reuseFailAlloc_2469_, 4, v___x_2461_);
                    lean_ctor_set(v_reuseFailAlloc_2469_, 5, v_cache_2447_);
                    lean_ctor_set(v_reuseFailAlloc_2469_, 6, v_messages_2448_);
                    lean_ctor_set(v_reuseFailAlloc_2469_, 7, v_infoState_2449_);
                    lean_ctor_set(v_reuseFailAlloc_2469_, 8, v_snapshotTasks_2450_);
                    v___x_2463_ = v_reuseFailAlloc_2469_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2464_ = lean_st_ref_set(v___y_2408_, v___x_2463_);
                v___x_2465_ = lean_box(0);
                if v_isShared_2440_ == 0 {
                    lean_ctor_set(v___x_2439_, 0, v___x_2465_);
                    v___x_2467_ = v___x_2439_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2468_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2468_, 0, v___x_2465_);
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
    mut v_oldTraces_2475_: *mut LeanObject,
    mut v_data_2476_: *mut LeanObject,
    mut v_ref_2477_: *mut LeanObject,
    mut v_msg_2478_: *mut LeanObject,
    mut v___y_2479_: *mut LeanObject,
    mut v___y_2480_: *mut LeanObject,
    mut v___y_2481_: *mut LeanObject,
    mut v___y_2482_: *mut LeanObject,
    mut v___y_2483_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2484_: *mut LeanObject = core::ptr::null_mut();
    v_res_2484_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__3___redArg(v_oldTraces_2475_, v_data_2476_, v_ref_2477_, v_msg_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_);
    lean_dec(v___y_2482_);
    lean_dec_ref(v___y_2481_);
    lean_dec(v___y_2480_);
    lean_dec_ref(v___y_2479_);
    return v_res_2484_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__1()
-> *mut LeanObject {
    let mut v___x_2486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut LeanObject = core::ptr::null_mut();
    v___x_2486_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__0;
    v___x_2487_ = l_Lean_stringToMessageData(v___x_2486_);
    return v___x_2487_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__3()
-> *mut LeanObject {
    let mut v___x_2489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: *mut LeanObject = core::ptr::null_mut();
    v___x_2489_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__2;
    v___x_2490_ = l_Lean_stringToMessageData(v___x_2489_);
    return v___x_2490_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__4()
-> f64 {
    let mut v___x_2491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: f64 = 0.0;
    v___x_2491_ = lean_unsigned_to_nat(1000);
    v___x_2492_ = lean_float_of_nat(v___x_2491_);
    return v___x_2492_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2(
    mut v_cls_2493_: *mut LeanObject,
    mut v_collapsed_2494_: u8,
    mut v_tag_2495_: *mut LeanObject,
    mut v_opts_2496_: *mut LeanObject,
    mut v_clsEnabled_2497_: u8,
    mut v_oldTraces_2498_: *mut LeanObject,
    mut v_msg_2499_: *mut LeanObject,
    mut v_resStartStop_2500_: *mut LeanObject,
    mut v___y_2501_: *mut LeanObject,
    mut v___y_2502_: *mut LeanObject,
    mut v___y_2503_: *mut LeanObject,
    mut v___y_2504_: *mut LeanObject,
    mut v___y_2505_: *mut LeanObject,
    mut v___y_2506_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_2508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2512_: u8 = 0;
    let mut v___y_2514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_2516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2522_: u8 = 0;
    let mut v___x_2524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2526_: u8 = 0;
    let mut v_fst_2527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2531_: u8 = 0;
    let mut v___x_2532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: u8 = 0;
    let mut v___y_2535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_result_2537_: u8 = 0;
    let mut v___x_2538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_m_2544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: f64 = 0.0;
    let mut v_data_2548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_2549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: f64 = 0.0;
    let mut v___x_2551_: f64 = 0.0;
    let mut v_reuseFailAlloc_2552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2560_: u8 = 0;
    let mut v___x_2561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_2562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_2565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_2567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_2568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_2569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2573_: u8 = 0;
    let mut v_tid_2574_: u64 = 0;
    let mut v_traces_2575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2578_: u8 = 0;
    let mut v___x_2579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2588_: u8 = 0;
    let mut v_isSharedCheck_2589_: u8 = 0;
    let mut v___y_2591_: f64 = 0.0;
    let mut v___x_2592_: f64 = 0.0;
    let mut v___x_2593_: f64 = 0.0;
    let mut v___x_2594_: f64 = 0.0;
    let mut v___x_2595_: u8 = 0;
    let mut v___x_2596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: u8 = 0;
    let mut v___x_2598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2600_: f64 = 0.0;
    let mut v___x_2601_: f64 = 0.0;
    let mut v___x_2602_: f64 = 0.0;
    let mut v___x_2603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: f64 = 0.0;
    let mut v_isSharedCheck_2606_: u8 = 0;
    let mut v_isSharedCheck_2607_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2508_ = lean_ctor_get(v_resStartStop_2500_, 0);
                v_snd_2509_ = lean_ctor_get(v_resStartStop_2500_, 1);
                v_isSharedCheck_2607_ = (!lean_is_exclusive(v_resStartStop_2500_)) as u8;
                if v_isSharedCheck_2607_ == 0 {
                    v___x_2511_ = v_resStartStop_2500_;
                    v_isShared_2512_ = v_isSharedCheck_2607_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_2509_);
                    lean_inc(v_fst_2508_);
                    lean_dec(v_resStartStop_2500_);
                    v___x_2511_ = lean_box(0);
                    v_isShared_2512_ = v_isSharedCheck_2607_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_2527_ = lean_ctor_get(v_snd_2509_, 0);
                v_snd_2528_ = lean_ctor_get(v_snd_2509_, 1);
                v_isSharedCheck_2606_ = (!lean_is_exclusive(v_snd_2509_)) as u8;
                if v_isSharedCheck_2606_ == 0 {
                    v___x_2530_ = v_snd_2509_;
                    v_isShared_2531_ = v_isSharedCheck_2606_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_snd_2528_);
                    lean_inc(v_fst_2527_);
                    lean_dec(v_snd_2509_);
                    v___x_2530_ = lean_box(0);
                    v_isShared_2531_ = v_isSharedCheck_2606_;
                    state = 5;
                    continue;
                }
            }
            2 => {
                lean_inc(v___y_2515_);
                v___x_2517_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__3___redArg(v_oldTraces_2498_, v_data_2516_, v___y_2515_, v___y_2514_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_);
                if lean_obj_tag(v___x_2517_) == 0 {
                    lean_dec_ref_known(v___x_2517_, 1);
                    v___x_2518_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__4___redArg(v_fst_2508_);
                    return v___x_2518_;
                } else {
                    lean_dec(v_fst_2508_);
                    v_a_2519_ = lean_ctor_get(v___x_2517_, 0);
                    v_isSharedCheck_2526_ = (!lean_is_exclusive(v___x_2517_)) as u8;
                    if v_isSharedCheck_2526_ == 0 {
                        v___x_2521_ = v___x_2517_;
                        v_isShared_2522_ = v_isSharedCheck_2526_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2519_);
                        lean_dec(v___x_2517_);
                        v___x_2521_ = lean_box(0);
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
                    v_reuseFailAlloc_2525_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2525_, 0, v_a_2519_);
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
                        v___x_2601_ = lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__4_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__4);
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
                v___x_2540_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__1_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__1);
                if v_isShared_2531_ == 0 {
                    lean_ctor_set_tag(v___x_2530_, 7);
                    lean_ctor_set(v___x_2530_, 1, v___x_2540_);
                    lean_ctor_set(v___x_2530_, 0, v___x_2539_);
                    v___x_2542_ = v___x_2530_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2553_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2553_, 0, v___x_2539_);
                    lean_ctor_set(v_reuseFailAlloc_2553_, 1, v___x_2540_);
                    v___x_2542_ = v_reuseFailAlloc_2553_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2512_ == 0 {
                    lean_ctor_set_tag(v___x_2511_, 7);
                    lean_ctor_set(v___x_2511_, 1, v_a_2536_);
                    lean_ctor_set(v___x_2511_, 0, v___x_2542_);
                    v_m_2544_ = v___x_2511_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2552_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2552_, 0, v___x_2542_);
                    lean_ctor_set(v_reuseFailAlloc_2552_, 1, v_a_2536_);
                    v_m_2544_ = v_reuseFailAlloc_2552_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2545_ = lean_box((v_result_2537_) as usize);
                v___x_2546_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2546_, 0, v___x_2545_);
                v___x_2547_ = lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__0_once), _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__0);
                lean_inc_ref(v_tag_2495_);
                lean_inc_ref(v___x_2546_);
                lean_inc(v_cls_2493_);
                v_data_2548_ = lean_alloc_ctor(0, 3, (17) as u32);
                lean_ctor_set(v_data_2548_, 0, v_cls_2493_);
                lean_ctor_set(v_data_2548_, 1, v___x_2546_);
                lean_ctor_set(v_data_2548_, 2, v_tag_2495_);
                lean_ctor_set_float(
                    v_data_2548_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_2547_,
                );
                lean_ctor_set_float(
                    v_data_2548_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    v___x_2547_,
                );
                lean_ctor_set_uint8(
                    v_data_2548_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                    v_collapsed_2494_,
                );
                if v___x_2533_ == 0 {
                    lean_dec_ref_known(v___x_2546_, 1);
                    lean_dec(v_snd_2528_);
                    lean_dec(v_fst_2527_);
                    lean_dec_ref(v_tag_2495_);
                    lean_dec(v_cls_2493_);
                    v___y_2514_ = v_m_2544_;
                    v___y_2515_ = v___y_2535_;
                    v_data_2516_ = v_data_2548_;
                    state = 2;
                    continue;
                } else {
                    lean_dec_ref_known(v_data_2548_, 3);
                    v_data_2549_ = lean_alloc_ctor(0, 3, (17) as u32);
                    lean_ctor_set(v_data_2549_, 0, v_cls_2493_);
                    lean_ctor_set(v_data_2549_, 1, v___x_2546_);
                    lean_ctor_set(v_data_2549_, 2, v_tag_2495_);
                    v___x_2550_ = lean_unbox_float(v_fst_2527_);
                    lean_dec(v_fst_2527_);
                    lean_ctor_set_float(
                        v_data_2549_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v___x_2550_,
                    );
                    v___x_2551_ = lean_unbox_float(v_snd_2528_);
                    lean_dec(v_snd_2528_);
                    lean_ctor_set_float(
                        v_data_2549_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                        v___x_2551_,
                    );
                    lean_ctor_set_uint8(
                        v_data_2549_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
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
                v_ref_2555_ = lean_ctor_get(v___y_2505_, 5);
                lean_inc(v___y_2506_);
                lean_inc_ref(v___y_2505_);
                lean_inc(v___y_2504_);
                lean_inc_ref(v___y_2503_);
                lean_inc(v___y_2502_);
                lean_inc_ref(v___y_2501_);
                lean_inc(v_fst_2508_);
                v___x_2556_ = lean_apply_8(
                    v_msg_2499_,
                    v_fst_2508_,
                    v___y_2501_,
                    v___y_2502_,
                    v___y_2503_,
                    v___y_2504_,
                    v___y_2505_,
                    v___y_2506_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_2556_) == 0 {
                    v_a_2557_ = lean_ctor_get(v___x_2556_, 0);
                    lean_inc(v_a_2557_);
                    lean_dec_ref_known(v___x_2556_, 1);
                    v___y_2535_ = v_ref_2555_;
                    v_a_2536_ = v_a_2557_;
                    state = 6;
                    continue;
                } else {
                    lean_dec_ref_known(v___x_2556_, 1);
                    v___x_2558_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__3_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__3);
                    v___y_2535_ = v_ref_2555_;
                    v_a_2536_ = v___x_2558_;
                    state = 6;
                    continue;
                }
            }
            10 => {
                if v_clsEnabled_2497_ == 0 {
                    if v___y_2560_ == 0 {
                        lean_del_object(v___x_2530_);
                        lean_dec(v_snd_2528_);
                        lean_dec(v_fst_2527_);
                        lean_del_object(v___x_2511_);
                        lean_dec_ref(v_msg_2499_);
                        lean_dec_ref(v_tag_2495_);
                        lean_dec(v_cls_2493_);
                        v___x_2561_ = lean_st_ref_take(v___y_2506_);
                        v_traceState_2562_ = lean_ctor_get(v___x_2561_, 4);
                        v_env_2563_ = lean_ctor_get(v___x_2561_, 0);
                        v_nextMacroScope_2564_ = lean_ctor_get(v___x_2561_, 1);
                        v_ngen_2565_ = lean_ctor_get(v___x_2561_, 2);
                        v_auxDeclNGen_2566_ = lean_ctor_get(v___x_2561_, 3);
                        v_cache_2567_ = lean_ctor_get(v___x_2561_, 5);
                        v_messages_2568_ = lean_ctor_get(v___x_2561_, 6);
                        v_infoState_2569_ = lean_ctor_get(v___x_2561_, 7);
                        v_snapshotTasks_2570_ = lean_ctor_get(v___x_2561_, 8);
                        v_isSharedCheck_2589_ = (!lean_is_exclusive(v___x_2561_)) as u8;
                        if v_isSharedCheck_2589_ == 0 {
                            v___x_2572_ = v___x_2561_;
                            v_isShared_2573_ = v_isSharedCheck_2589_;
                            state = 11;
                            continue;
                        } else {
                            lean_inc(v_snapshotTasks_2570_);
                            lean_inc(v_infoState_2569_);
                            lean_inc(v_messages_2568_);
                            lean_inc(v_cache_2567_);
                            lean_inc(v_traceState_2562_);
                            lean_inc(v_auxDeclNGen_2566_);
                            lean_inc(v_ngen_2565_);
                            lean_inc(v_nextMacroScope_2564_);
                            lean_inc(v_env_2563_);
                            lean_dec(v___x_2561_);
                            v___x_2572_ = lean_box(0);
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
                v_tid_2574_ = lean_ctor_get_uint64(
                    v_traceState_2562_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_traces_2575_ = lean_ctor_get(v_traceState_2562_, 0);
                v_isSharedCheck_2588_ = (!lean_is_exclusive(v_traceState_2562_)) as u8;
                if v_isSharedCheck_2588_ == 0 {
                    v___x_2577_ = v_traceState_2562_;
                    v_isShared_2578_ = v_isSharedCheck_2588_;
                    state = 12;
                    continue;
                } else {
                    lean_inc(v_traces_2575_);
                    lean_dec(v_traceState_2562_);
                    v___x_2577_ = lean_box(0);
                    v_isShared_2578_ = v_isSharedCheck_2588_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_2579_ =
                    l_Lean_PersistentArray_append___redArg(v_oldTraces_2498_, v_traces_2575_);
                lean_dec_ref(v_traces_2575_);
                if v_isShared_2578_ == 0 {
                    lean_ctor_set(v___x_2577_, 0, v___x_2579_);
                    v___x_2581_ = v___x_2577_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2587_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2587_, 0, v___x_2579_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_2587_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_2574_,
                    );
                    v___x_2581_ = v_reuseFailAlloc_2587_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_2573_ == 0 {
                    lean_ctor_set(v___x_2572_, 4, v___x_2581_);
                    v___x_2583_ = v___x_2572_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2586_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2586_, 0, v_env_2563_);
                    lean_ctor_set(v_reuseFailAlloc_2586_, 1, v_nextMacroScope_2564_);
                    lean_ctor_set(v_reuseFailAlloc_2586_, 2, v_ngen_2565_);
                    lean_ctor_set(v_reuseFailAlloc_2586_, 3, v_auxDeclNGen_2566_);
                    lean_ctor_set(v_reuseFailAlloc_2586_, 4, v___x_2581_);
                    lean_ctor_set(v_reuseFailAlloc_2586_, 5, v_cache_2567_);
                    lean_ctor_set(v_reuseFailAlloc_2586_, 6, v_messages_2568_);
                    lean_ctor_set(v_reuseFailAlloc_2586_, 7, v_infoState_2569_);
                    lean_ctor_set(v_reuseFailAlloc_2586_, 8, v_snapshotTasks_2570_);
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
                v___x_2592_ = lean_unbox_float(v_snd_2528_);
                v___x_2593_ = lean_unbox_float(v_fst_2527_);
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
    mut v_cls_2608_: *mut LeanObject,
    mut v_collapsed_2609_: *mut LeanObject,
    mut v_tag_2610_: *mut LeanObject,
    mut v_opts_2611_: *mut LeanObject,
    mut v_clsEnabled_2612_: *mut LeanObject,
    mut v_oldTraces_2613_: *mut LeanObject,
    mut v_msg_2614_: *mut LeanObject,
    mut v_resStartStop_2615_: *mut LeanObject,
    mut v___y_2616_: *mut LeanObject,
    mut v___y_2617_: *mut LeanObject,
    mut v___y_2618_: *mut LeanObject,
    mut v___y_2619_: *mut LeanObject,
    mut v___y_2620_: *mut LeanObject,
    mut v___y_2621_: *mut LeanObject,
    mut v___y_2622_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_collapsed_boxed_2623_: u8 = 0;
    let mut v_clsEnabled_boxed_2624_: u8 = 0;
    let mut v_res_2625_: *mut LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_2623_ = (lean_unbox(v_collapsed_2609_) as u8);
    v_clsEnabled_boxed_2624_ = (lean_unbox(v_clsEnabled_2612_) as u8);
    v_res_2625_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2(v_cls_2608_, v_collapsed_boxed_2623_, v_tag_2610_, v_opts_2611_, v_clsEnabled_boxed_2624_, v_oldTraces_2613_, v_msg_2614_, v_resStartStop_2615_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_);
    lean_dec(v___y_2621_);
    lean_dec_ref(v___y_2620_);
    lean_dec(v___y_2619_);
    lean_dec_ref(v___y_2618_);
    lean_dec(v___y_2617_);
    lean_dec_ref(v___y_2616_);
    lean_dec_ref(v_opts_2611_);
    return v_res_2625_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__4()
-> f64 {
    let mut v___x_2633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: f64 = 0.0;
    v___x_2633_ = lean_unsigned_to_nat(1000000000);
    v___x_2634_ = lean_float_of_nat(v___x_2633_);
    return v___x_2634_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7()
-> *mut LeanObject {
    let mut v___x_2638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut LeanObject = core::ptr::null_mut();
    v___x_2638_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__3;
    v___x_2639_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__6;
    v___x_2640_ = l_Lean_Name_append(v___x_2639_, v___x_2638_);
    return v___x_2640_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__9()
-> *mut LeanObject {
    let mut v___x_2642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut LeanObject = core::ptr::null_mut();
    v___x_2642_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__8;
    v___x_2643_ = l_Lean_stringToMessageData(v___x_2642_);
    return v___x_2643_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__11()
-> *mut LeanObject {
    let mut v___x_2645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut LeanObject = core::ptr::null_mut();
    v___x_2645_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__10;
    v___x_2646_ = l_Lean_stringToMessageData(v___x_2645_);
    return v___x_2646_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go(
    mut v_g_2647_: *mut LeanObject,
    mut v_a_2648_: *mut LeanObject,
    mut v_a_2649_: *mut LeanObject,
    mut v_a_2650_: *mut LeanObject,
    mut v_a_2651_: *mut LeanObject,
    mut v_a_2652_: *mut LeanObject,
    mut v_a_2653_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2660_: u8 = 0;
    let mut v_options_2661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2665_: u8 = 0;
    let mut v_inheritedTraceOptions_2666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_2667_: u8 = 0;
    let mut v___x_2668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2671_: u8 = 0;
    let mut v___y_2672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2682_: u8 = 0;
    let mut v_a_2683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: f64 = 0.0;
    let mut v___x_2686_: f64 = 0.0;
    let mut v___x_2687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2694_: u8 = 0;
    let mut v___y_2695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2705_: u8 = 0;
    let mut v_a_2706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: f64 = 0.0;
    let mut v___x_2709_: f64 = 0.0;
    let mut v___x_2710_: f64 = 0.0;
    let mut v___x_2711_: f64 = 0.0;
    let mut v___x_2712_: f64 = 0.0;
    let mut v___x_2713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2720_: u8 = 0;
    let mut v___y_2721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2731_: u8 = 0;
    let mut v___x_2732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: u8 = 0;
    let mut v___x_2736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2741_: u8 = 0;
    let mut v___x_2743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2745_: u8 = 0;
    let mut v_a_2746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2749_: u8 = 0;
    let mut v___x_2751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2753_: u8 = 0;
    let mut v___x_2754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2759_: u8 = 0;
    let mut v___x_2761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2763_: u8 = 0;
    let mut v_a_2764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2767_: u8 = 0;
    let mut v___x_2769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2771_: u8 = 0;
    let mut v___y_2773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_shortCircuit_2785_: u8 = 0;
    let mut v_val_2786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_2789_: u8 = 0;
    let mut v_run_x27_2790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_run_x27_2792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_2793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: u8 = 0;
    let mut v___x_2798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: u8 = 0;
    let mut v___x_2800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2803_: u8 = 0;
    let mut v___x_2805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2807_: u8 = 0;
    let mut v_unused_2808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_g_2811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_2819_: u8 = 0;
    let mut v_inheritedTraceOptions_2820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2822_: u8 = 0;
    let mut v___x_2823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2831_: u8 = 0;
    let mut v___x_2833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2835_: u8 = 0;
    let mut v_reuseFailAlloc_2836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2849_: u8 = 0;
    let mut v_val_2850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2854_: u8 = 0;
    let mut v___y_2856_: u8 = 0;
    let mut v___y_2857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2860_: u8 = 0;
    let mut v___y_2861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: f64 = 0.0;
    let mut v___x_2873_: f64 = 0.0;
    let mut v___x_2874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2880_: u8 = 0;
    let mut v___y_2881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2885_: u8 = 0;
    let mut v___y_2886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: f64 = 0.0;
    let mut v___x_2897_: f64 = 0.0;
    let mut v___x_2898_: f64 = 0.0;
    let mut v___x_2899_: f64 = 0.0;
    let mut v___x_2900_: f64 = 0.0;
    let mut v___x_2901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2907_: u8 = 0;
    let mut v___y_2908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2913_: u8 = 0;
    let mut v___y_2914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: u8 = 0;
    let mut v___x_2925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2930_: u8 = 0;
    let mut v___x_2932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2934_: u8 = 0;
    let mut v_a_2935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2938_: u8 = 0;
    let mut v___x_2940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2942_: u8 = 0;
    let mut v___x_2943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2948_: u8 = 0;
    let mut v___x_2950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2952_: u8 = 0;
    let mut v_a_2953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2956_: u8 = 0;
    let mut v___x_2958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2960_: u8 = 0;
    let mut v___y_2962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fixedInt_2963_: u8 = 0;
    let mut v_g_2964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_2973_: u8 = 0;
    let mut v_run_x27_2974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_run_x27_2976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_2977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: u8 = 0;
    let mut v___x_2982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: u8 = 0;
    let mut v___x_2984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2997_: u8 = 0;
    let mut v_val_2998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fixedInt_2999_: u8 = 0;
    let mut v___x_3001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3003_: u8 = 0;
    let mut v___y_3005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3006_: u8 = 0;
    let mut v___y_3007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3018_: u8 = 0;
    let mut v_a_3019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: f64 = 0.0;
    let mut v___x_3022_: f64 = 0.0;
    let mut v___x_3023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3030_: u8 = 0;
    let mut v___y_3031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3042_: u8 = 0;
    let mut v_a_3043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: f64 = 0.0;
    let mut v___x_3046_: f64 = 0.0;
    let mut v___x_3047_: f64 = 0.0;
    let mut v___x_3048_: f64 = 0.0;
    let mut v___x_3049_: f64 = 0.0;
    let mut v___x_3050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3058_: u8 = 0;
    let mut v___y_3059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3068_: u8 = 0;
    let mut v___y_3069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: u8 = 0;
    let mut v___x_3074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3079_: u8 = 0;
    let mut v___x_3081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3083_: u8 = 0;
    let mut v_a_3084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3087_: u8 = 0;
    let mut v___x_3089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3091_: u8 = 0;
    let mut v___x_3092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3097_: u8 = 0;
    let mut v___x_3099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3101_: u8 = 0;
    let mut v_a_3102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3105_: u8 = 0;
    let mut v___x_3107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3109_: u8 = 0;
    let mut v___y_3111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fixedInt_3112_: u8 = 0;
    let mut v_enums_3113_: u8 = 0;
    let mut v_g_3114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_3122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3123_: u8 = 0;
    let mut v_run_x27_3124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_run_x27_3126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_3127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: u8 = 0;
    let mut v___x_3132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: u8 = 0;
    let mut v___x_3134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3147_: u8 = 0;
    let mut v_val_3148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fixedInt_3149_: u8 = 0;
    let mut v_enums_3150_: u8 = 0;
    let mut v___x_3152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3154_: u8 = 0;
    let mut v___y_3156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3158_: u8 = 0;
    let mut v___y_3159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3166_: u8 = 0;
    let mut v___y_3167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: f64 = 0.0;
    let mut v___x_3173_: f64 = 0.0;
    let mut v___x_3174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3182_: u8 = 0;
    let mut v___y_3183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3190_: u8 = 0;
    let mut v___y_3191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3196_: f64 = 0.0;
    let mut v___x_3197_: f64 = 0.0;
    let mut v___x_3198_: f64 = 0.0;
    let mut v___x_3199_: f64 = 0.0;
    let mut v___x_3200_: f64 = 0.0;
    let mut v___x_3201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3211_: u8 = 0;
    let mut v___y_3212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3220_: u8 = 0;
    let mut v___x_3221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: u8 = 0;
    let mut v___x_3225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3230_: u8 = 0;
    let mut v___x_3232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3234_: u8 = 0;
    let mut v_a_3235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3238_: u8 = 0;
    let mut v___x_3240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3242_: u8 = 0;
    let mut v___x_3243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3248_: u8 = 0;
    let mut v___x_3250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3252_: u8 = 0;
    let mut v_a_3253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3256_: u8 = 0;
    let mut v___x_3258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3260_: u8 = 0;
    let mut v___y_3262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3272_: u8 = 0;
    let mut v_structures_3273_: u8 = 0;
    let mut v_val_3274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fixedInt_3275_: u8 = 0;
    let mut v_enums_3276_: u8 = 0;
    let mut v_val_3277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_3279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3280_: u8 = 0;
    let mut v_run_x27_3281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_run_x27_3283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_3284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: u8 = 0;
    let mut v___x_3289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: u8 = 0;
    let mut v___x_3291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3295_: u8 = 0;
    let mut v___y_3297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3305_: u8 = 0;
    let mut v___y_3306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3308_: u8 = 0;
    let mut v___y_3309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: f64 = 0.0;
    let mut v___x_3313_: f64 = 0.0;
    let mut v___x_3314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3328_: u8 = 0;
    let mut v___y_3329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3331_: u8 = 0;
    let mut v___y_3332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: f64 = 0.0;
    let mut v___x_3336_: f64 = 0.0;
    let mut v___x_3337_: f64 = 0.0;
    let mut v___x_3338_: f64 = 0.0;
    let mut v___x_3339_: f64 = 0.0;
    let mut v___x_3340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3352_: u8 = 0;
    let mut v___y_3353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3356_: u8 = 0;
    let mut v___y_3357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3361_: u8 = 0;
    let mut v___x_3362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3367_: u8 = 0;
    let mut v___x_3369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3371_: u8 = 0;
    let mut v_a_3372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3375_: u8 = 0;
    let mut v___x_3377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3379_: u8 = 0;
    let mut v___x_3380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3385_: u8 = 0;
    let mut v___x_3387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3389_: u8 = 0;
    let mut v_a_3390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3393_: u8 = 0;
    let mut v___x_3395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3397_: u8 = 0;
    let mut v___y_3399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_3406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3407_: u8 = 0;
    let mut v_run_x27_3408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_run_x27_3410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_3411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3415_: u8 = 0;
    let mut v___x_3416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3417_: u8 = 0;
    let mut v___x_3418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_structures_3426_: u8 = 0;
    let mut v_enums_3427_: u8 = 0;
    let mut v_fixedInt_3428_: u8 = 0;
    let mut v___x_3429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: u8 = 0;
    let mut v___x_3431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3438_: u8 = 0;
    let mut v___x_3440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3442_: u8 = 0;
    let mut v_isSharedCheck_3443_: u8 = 0;
    let mut v___x_3445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3447_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2655_ = lean_box(0);
                v___x_2656_ = l_Lean_MVarId_falseOrByContra(
                    v_g_2647_,
                    v___x_2655_,
                    v_a_2650_,
                    v_a_2651_,
                    v_a_2652_,
                    v_a_2653_,
                );
                if lean_obj_tag(v___x_2656_) == 0 {
                    v_a_2657_ = lean_ctor_get(v___x_2656_, 0);
                    v_isSharedCheck_3447_ = (!lean_is_exclusive(v___x_2656_)) as u8;
                    if v_isSharedCheck_3447_ == 0 {
                        v___x_2659_ = v___x_2656_;
                        v_isShared_2660_ = v_isSharedCheck_3447_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2657_);
                        lean_dec(v___x_2656_);
                        v___x_2659_ = lean_box(0);
                        v_isShared_2660_ = v_isSharedCheck_3447_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_2656_;
                }
            }
            1 => {
                if lean_obj_tag(v_a_2657_) == 1 {
                    lean_del_object(v___x_2659_);
                    v_options_2661_ = lean_ctor_get(v_a_2652_, 2);
                    v_val_2662_ = lean_ctor_get(v_a_2657_, 0);
                    v_isSharedCheck_3443_ = (!lean_is_exclusive(v_a_2657_)) as u8;
                    if v_isSharedCheck_3443_ == 0 {
                        v___x_2664_ = v_a_2657_;
                        v_isShared_2665_ = v_isSharedCheck_3443_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_2662_);
                        lean_dec(v_a_2657_);
                        v___x_2664_ = lean_box(0);
                        v_isShared_2665_ = v_isSharedCheck_3443_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_2657_);
                    if v_isShared_2660_ == 0 {
                        lean_ctor_set(v___x_2659_, 0, v___x_2655_);
                        v___x_3445_ = v___x_2659_;
                        state = 83;
                        continue;
                    } else {
                        v_reuseFailAlloc_3446_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3446_, 0, v___x_2655_);
                        v___x_3445_ = v_reuseFailAlloc_3446_;
                        state = 83;
                        continue;
                    }
                }
            }
            2 => {
                v_inheritedTraceOptions_2666_ = lean_ctor_get(v_a_2652_, 13);
                v_hasTrace_2667_ = lean_ctor_get_uint8(
                    v_options_2661_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
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
                    v___x_3429_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7);
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
                        v___x_3431_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__11_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__11);
                        lean_inc(v_val_2662_);
                        v___x_3432_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_3432_, 0, v_val_2662_);
                        v___x_3433_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_3433_, 0, v___x_3431_);
                        lean_ctor_set(v___x_3433_, 1, v___x_3432_);
                        v___x_3434_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg(v___x_2668_, v___x_3433_, v_a_2650_, v_a_2651_, v_a_2652_, v_a_2653_);
                        if lean_obj_tag(v___x_3434_) == 0 {
                            lean_dec_ref_known(v___x_3434_, 1);
                            v___y_3420_ = v_a_2648_;
                            v___y_3421_ = v_a_2649_;
                            v___y_3422_ = v_a_2650_;
                            v___y_3423_ = v_a_2651_;
                            v___y_3424_ = v_a_2652_;
                            v___y_3425_ = v_a_2653_;
                            state = 80;
                            continue;
                        } else {
                            lean_del_object(v___x_2664_);
                            lean_dec(v_val_2662_);
                            v_a_3435_ = lean_ctor_get(v___x_3434_, 0);
                            v_isSharedCheck_3442_ = (!lean_is_exclusive(v___x_3434_)) as u8;
                            if v_isSharedCheck_3442_ == 0 {
                                v___x_3437_ = v___x_3434_;
                                v_isShared_3438_ = v_isSharedCheck_3442_;
                                state = 81;
                                continue;
                            } else {
                                lean_inc(v_a_3435_);
                                lean_dec(v___x_3434_);
                                v___x_3437_ = lean_box(0);
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
                v___x_2687_ = lean_box_float(v___x_2685_);
                v___x_2688_ = lean_box_float(v___x_2686_);
                v___x_2689_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2689_, 0, v___x_2687_);
                lean_ctor_set(v___x_2689_, 1, v___x_2688_);
                v___x_2690_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2690_, 0, v_a_2683_);
                lean_ctor_set(v___x_2690_, 1, v___x_2689_);
                lean_inc_ref(v___y_2677_);
                v___x_2691_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2(v___x_2668_, v___y_2682_, v___y_2677_, v___y_2678_, v___y_2671_, v___y_2676_, v___y_2679_, v___x_2690_, v___y_2670_, v___y_2675_, v___y_2680_, v___y_2673_, v___y_2674_, v___y_2681_);
                return v___x_2691_;
            }
            4 => {
                v___x_2707_ = lean_io_mono_nanos_now();
                v___x_2708_ = lean_float_of_nat(v___y_2696_);
                v___x_2709_ = lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__4_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__4);
                v___x_2710_ = lean_float_div(v___x_2708_, v___x_2709_);
                v___x_2711_ = lean_float_of_nat(v___x_2707_);
                v___x_2712_ = lean_float_div(v___x_2711_, v___x_2709_);
                v___x_2713_ = lean_box_float(v___x_2710_);
                v___x_2714_ = lean_box_float(v___x_2712_);
                v___x_2715_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2715_, 0, v___x_2713_);
                lean_ctor_set(v___x_2715_, 1, v___x_2714_);
                v___x_2716_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2716_, 0, v_a_2706_);
                lean_ctor_set(v___x_2716_, 1, v___x_2715_);
                lean_inc_ref(v___y_2700_);
                v___x_2717_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2(v___x_2668_, v___y_2705_, v___y_2700_, v___y_2701_, v___y_2694_, v___y_2699_, v___y_2702_, v___x_2716_, v___y_2693_, v___y_2698_, v___y_2703_, v___y_2695_, v___y_2697_, v___y_2704_);
                return v___x_2717_;
            }
            5 => {
                v___x_2732_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___redArg(v___y_2730_);
                v_a_2733_ = lean_ctor_get(v___x_2732_, 0);
                lean_inc(v_a_2733_);
                lean_dec_ref(v___x_2732_);
                v___x_2734_ = l_Lean_trace_profiler_useHeartbeats;
                v___x_2735_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__1(v___y_2727_, v___x_2734_);
                if v___x_2735_ == 0 {
                    v___x_2736_ = lean_io_mono_nanos_now();
                    lean_inc(v___y_2730_);
                    lean_inc_ref(v___y_2724_);
                    lean_inc(v___y_2721_);
                    lean_inc_ref(v___y_2729_);
                    lean_inc(v___y_2725_);
                    lean_inc_ref(v___y_2719_);
                    v___x_2737_ = lean_apply_8(
                        v___y_2722_,
                        v___y_2723_,
                        v___y_2719_,
                        v___y_2725_,
                        v___y_2729_,
                        v___y_2721_,
                        v___y_2724_,
                        v___y_2730_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_2737_) == 0 {
                        v_a_2738_ = lean_ctor_get(v___x_2737_, 0);
                        v_isSharedCheck_2745_ = (!lean_is_exclusive(v___x_2737_)) as u8;
                        if v_isSharedCheck_2745_ == 0 {
                            v___x_2740_ = v___x_2737_;
                            v_isShared_2741_ = v_isSharedCheck_2745_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_2738_);
                            lean_dec(v___x_2737_);
                            v___x_2740_ = lean_box(0);
                            v_isShared_2741_ = v_isSharedCheck_2745_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_2746_ = lean_ctor_get(v___x_2737_, 0);
                        v_isSharedCheck_2753_ = (!lean_is_exclusive(v___x_2737_)) as u8;
                        if v_isSharedCheck_2753_ == 0 {
                            v___x_2748_ = v___x_2737_;
                            v_isShared_2749_ = v_isSharedCheck_2753_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_2746_);
                            lean_dec(v___x_2737_);
                            v___x_2748_ = lean_box(0);
                            v_isShared_2749_ = v_isSharedCheck_2753_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    v___x_2754_ = lean_io_get_num_heartbeats();
                    lean_inc(v___y_2730_);
                    lean_inc_ref(v___y_2724_);
                    lean_inc(v___y_2721_);
                    lean_inc_ref(v___y_2729_);
                    lean_inc(v___y_2725_);
                    lean_inc_ref(v___y_2719_);
                    v___x_2755_ = lean_apply_8(
                        v___y_2722_,
                        v___y_2723_,
                        v___y_2719_,
                        v___y_2725_,
                        v___y_2729_,
                        v___y_2721_,
                        v___y_2724_,
                        v___y_2730_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_2755_) == 0 {
                        v_a_2756_ = lean_ctor_get(v___x_2755_, 0);
                        v_isSharedCheck_2763_ = (!lean_is_exclusive(v___x_2755_)) as u8;
                        if v_isSharedCheck_2763_ == 0 {
                            v___x_2758_ = v___x_2755_;
                            v_isShared_2759_ = v_isSharedCheck_2763_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_a_2756_);
                            lean_dec(v___x_2755_);
                            v___x_2758_ = lean_box(0);
                            v_isShared_2759_ = v_isSharedCheck_2763_;
                            state = 10;
                            continue;
                        }
                    } else {
                        v_a_2764_ = lean_ctor_get(v___x_2755_, 0);
                        v_isSharedCheck_2771_ = (!lean_is_exclusive(v___x_2755_)) as u8;
                        if v_isSharedCheck_2771_ == 0 {
                            v___x_2766_ = v___x_2755_;
                            v_isShared_2767_ = v_isSharedCheck_2771_;
                            state = 12;
                            continue;
                        } else {
                            lean_inc(v_a_2764_);
                            lean_dec(v___x_2755_);
                            v___x_2766_ = lean_box(0);
                            v_isShared_2767_ = v_isSharedCheck_2771_;
                            state = 12;
                            continue;
                        }
                    }
                }
            }
            6 => {
                if v_isShared_2741_ == 0 {
                    lean_ctor_set_tag(v___x_2740_, 1);
                    v___x_2743_ = v___x_2740_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2744_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2744_, 0, v_a_2738_);
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
                    lean_ctor_set_tag(v___x_2748_, 0);
                    v___x_2751_ = v___x_2748_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2752_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2752_, 0, v_a_2746_);
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
                    lean_ctor_set_tag(v___x_2758_, 1);
                    v___x_2761_ = v___x_2758_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2762_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2762_, 0, v_a_2756_);
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
                    lean_ctor_set_tag(v___x_2766_, 0);
                    v___x_2769_ = v___x_2766_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2770_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2770_, 0, v_a_2764_);
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
                v_a_2782_ = lean_ctor_get(v___x_2781_, 0);
                lean_inc(v_a_2782_);
                lean_dec_ref(v___x_2781_);
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
                lean_dec(v_a_2782_);
                if lean_obj_tag(v___x_2783_) == 0 {
                    v_a_2784_ = lean_ctor_get(v___x_2783_, 0);
                    lean_inc(v_a_2784_);
                    if lean_obj_tag(v_a_2784_) == 1 {
                        v_shortCircuit_2785_ = lean_ctor_get_uint8(
                            v___y_2774_,
                            (core::mem::size_of::<*mut LeanObject>() * 2 + 9) as u32,
                        );
                        if v_shortCircuit_2785_ == 0 {
                            lean_dec_ref_known(v_a_2784_, 1);
                            return v___x_2783_;
                        } else {
                            lean_dec_ref_known(v___x_2783_, 1);
                            v_val_2786_ = lean_ctor_get(v_a_2784_, 0);
                            lean_inc(v_val_2786_);
                            lean_dec_ref_known(v_a_2784_, 1);
                            v___x_2787_ = l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass;
                            v_options_2788_ = lean_ctor_get(v___y_2779_, 2);
                            v_hasTrace_2789_ = lean_ctor_get_uint8(
                                v_options_2788_,
                                (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            );
                            if v_hasTrace_2789_ == 0 {
                                v_run_x27_2790_ = lean_ctor_get(v___x_2787_, 1);
                                lean_inc_ref(v_run_x27_2790_);
                                lean_inc(v___y_2780_);
                                lean_inc_ref(v___y_2779_);
                                lean_inc(v___y_2778_);
                                lean_inc_ref(v___y_2777_);
                                lean_inc(v___y_2776_);
                                lean_inc_ref(v___y_2775_);
                                v___x_2791_ = lean_apply_8(
                                    v_run_x27_2790_,
                                    v_val_2786_,
                                    v___y_2775_,
                                    v___y_2776_,
                                    v___y_2777_,
                                    v___y_2778_,
                                    v___y_2779_,
                                    v___y_2780_,
                                    lean_box(0),
                                );
                                return v___x_2791_;
                            } else {
                                v_run_x27_2792_ = lean_ctor_get(v___x_2787_, 1);
                                v_inheritedTraceOptions_2793_ = lean_ctor_get(v___y_2779_, 13);
                                lean_inc(v_val_2786_);
                                v___f_2794_ = lean_alloc_closure(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___boxed as *mut core::ffi::c_void, 10, 2);
                                lean_closure_set(v___f_2794_, 0, v___x_2787_);
                                lean_closure_set(v___f_2794_, 1, v_val_2786_);
                                v___x_2795_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__1;
                                v___x_2796_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7);
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
                                        lean_dec_ref(v___f_2794_);
                                        lean_inc_ref(v_run_x27_2792_);
                                        lean_inc(v___y_2780_);
                                        lean_inc_ref(v___y_2779_);
                                        lean_inc(v___y_2778_);
                                        lean_inc_ref(v___y_2777_);
                                        lean_inc(v___y_2776_);
                                        lean_inc_ref(v___y_2775_);
                                        v___x_2800_ = lean_apply_8(
                                            v_run_x27_2792_,
                                            v_val_2786_,
                                            v___y_2775_,
                                            v___y_2776_,
                                            v___y_2777_,
                                            v___y_2778_,
                                            v___y_2779_,
                                            v___y_2780_,
                                            lean_box(0),
                                        );
                                        return v___x_2800_;
                                    } else {
                                        lean_inc_ref(v_run_x27_2792_);
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
                                    lean_inc_ref(v_run_x27_2792_);
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
                        lean_dec(v_a_2784_);
                        v_isSharedCheck_2807_ = (!lean_is_exclusive(v___x_2783_)) as u8;
                        if v_isSharedCheck_2807_ == 0 {
                            v_unused_2808_ = lean_ctor_get(v___x_2783_, 0);
                            lean_dec(v_unused_2808_);
                            v___x_2802_ = v___x_2783_;
                            v_isShared_2803_ = v_isSharedCheck_2807_;
                            state = 15;
                            continue;
                        } else {
                            lean_dec(v___x_2783_);
                            v___x_2802_ = lean_box(0);
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
                    lean_ctor_set(v___x_2802_, 0, v___x_2655_);
                    v___x_2805_ = v___x_2802_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2806_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2806_, 0, v___x_2655_);
                    v___x_2805_ = v_reuseFailAlloc_2806_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_2805_;
            }
            17 => {
                v_options_2818_ = lean_ctor_get(v___y_2816_, 2);
                v_hasTrace_2819_ = lean_ctor_get_uint8(
                    v_options_2818_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                if v_hasTrace_2819_ == 0 {
                    lean_del_object(v___x_2664_);
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
                    v_inheritedTraceOptions_2820_ = lean_ctor_get(v___y_2816_, 13);
                    v___x_2821_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7);
                    v___x_2822_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_2820_,
                        v_options_2818_,
                        v___x_2821_,
                    );
                    if v___x_2822_ == 0 {
                        lean_del_object(v___x_2664_);
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
                        v___x_2823_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__9_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__9);
                        lean_inc(v_g_2811_);
                        if v_isShared_2665_ == 0 {
                            lean_ctor_set(v___x_2664_, 0, v_g_2811_);
                            v___x_2825_ = v___x_2664_;
                            state = 18;
                            continue;
                        } else {
                            v_reuseFailAlloc_2836_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2836_, 0, v_g_2811_);
                            v___x_2825_ = v_reuseFailAlloc_2836_;
                            state = 18;
                            continue;
                        }
                    }
                }
            }
            18 => {
                v___x_2826_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2826_, 0, v___x_2823_);
                lean_ctor_set(v___x_2826_, 1, v___x_2825_);
                v___x_2827_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg(v___x_2668_, v___x_2826_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_);
                if lean_obj_tag(v___x_2827_) == 0 {
                    lean_dec_ref_known(v___x_2827_, 1);
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
                    lean_dec(v_g_2811_);
                    v_a_2828_ = lean_ctor_get(v___x_2827_, 0);
                    v_isSharedCheck_2835_ = (!lean_is_exclusive(v___x_2827_)) as u8;
                    if v_isSharedCheck_2835_ == 0 {
                        v___x_2830_ = v___x_2827_;
                        v_isShared_2831_ = v_isSharedCheck_2835_;
                        state = 19;
                        continue;
                    } else {
                        lean_inc(v_a_2828_);
                        lean_dec(v___x_2827_);
                        v___x_2830_ = lean_box(0);
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
                    v_reuseFailAlloc_2834_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2834_, 0, v_a_2828_);
                    v___x_2833_ = v_reuseFailAlloc_2834_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_2833_;
            }
            21 => {
                if lean_obj_tag(v___y_2845_) == 0 {
                    v_a_2846_ = lean_ctor_get(v___y_2845_, 0);
                    v_isSharedCheck_2854_ = (!lean_is_exclusive(v___y_2845_)) as u8;
                    if v_isSharedCheck_2854_ == 0 {
                        v___x_2848_ = v___y_2845_;
                        v_isShared_2849_ = v_isSharedCheck_2854_;
                        state = 22;
                        continue;
                    } else {
                        lean_inc(v_a_2846_);
                        lean_dec(v___y_2845_);
                        v___x_2848_ = lean_box(0);
                        v_isShared_2849_ = v_isSharedCheck_2854_;
                        state = 22;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2664_);
                    return v___y_2845_;
                }
            }
            22 => {
                if lean_obj_tag(v_a_2846_) == 1 {
                    lean_del_object(v___x_2848_);
                    v_val_2850_ = lean_ctor_get(v_a_2846_, 0);
                    lean_inc(v_val_2850_);
                    lean_dec_ref_known(v_a_2846_, 1);
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
                    lean_dec(v_a_2846_);
                    lean_del_object(v___x_2664_);
                    if v_isShared_2849_ == 0 {
                        lean_ctor_set(v___x_2848_, 0, v___x_2655_);
                        v___x_2852_ = v___x_2848_;
                        state = 23;
                        continue;
                    } else {
                        v_reuseFailAlloc_2853_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2853_, 0, v___x_2655_);
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
                v___x_2874_ = lean_box_float(v___x_2872_);
                v___x_2875_ = lean_box_float(v___x_2873_);
                v___x_2876_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2876_, 0, v___x_2874_);
                lean_ctor_set(v___x_2876_, 1, v___x_2875_);
                v___x_2877_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2877_, 0, v_a_2870_);
                lean_ctor_set(v___x_2877_, 1, v___x_2876_);
                lean_inc_ref(v___y_2859_);
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
                v___x_2897_ = lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__4_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__4);
                v___x_2898_ = lean_float_div(v___x_2896_, v___x_2897_);
                v___x_2899_ = lean_float_of_nat(v___x_2895_);
                v___x_2900_ = lean_float_div(v___x_2899_, v___x_2897_);
                v___x_2901_ = lean_box_float(v___x_2898_);
                v___x_2902_ = lean_box_float(v___x_2900_);
                v___x_2903_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2903_, 0, v___x_2901_);
                lean_ctor_set(v___x_2903_, 1, v___x_2902_);
                v___x_2904_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2904_, 0, v_a_2894_);
                lean_ctor_set(v___x_2904_, 1, v___x_2903_);
                lean_inc_ref(v___y_2883_);
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
                v_a_2922_ = lean_ctor_get(v___x_2921_, 0);
                lean_inc(v_a_2922_);
                lean_dec_ref(v___x_2921_);
                v___x_2923_ = l_Lean_trace_profiler_useHeartbeats;
                v___x_2924_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__1(v___y_2909_, v___x_2923_);
                if v___x_2924_ == 0 {
                    v___x_2925_ = lean_io_mono_nanos_now();
                    lean_inc(v___y_2915_);
                    lean_inc_ref(v___y_2920_);
                    lean_inc(v___y_2916_);
                    lean_inc_ref(v___y_2908_);
                    lean_inc(v___y_2919_);
                    lean_inc_ref(v___y_2917_);
                    v___x_2926_ = lean_apply_8(
                        v___y_2912_,
                        v___y_2910_,
                        v___y_2917_,
                        v___y_2919_,
                        v___y_2908_,
                        v___y_2916_,
                        v___y_2920_,
                        v___y_2915_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_2926_) == 0 {
                        v_a_2927_ = lean_ctor_get(v___x_2926_, 0);
                        v_isSharedCheck_2934_ = (!lean_is_exclusive(v___x_2926_)) as u8;
                        if v_isSharedCheck_2934_ == 0 {
                            v___x_2929_ = v___x_2926_;
                            v_isShared_2930_ = v_isSharedCheck_2934_;
                            state = 27;
                            continue;
                        } else {
                            lean_inc(v_a_2927_);
                            lean_dec(v___x_2926_);
                            v___x_2929_ = lean_box(0);
                            v_isShared_2930_ = v_isSharedCheck_2934_;
                            state = 27;
                            continue;
                        }
                    } else {
                        v_a_2935_ = lean_ctor_get(v___x_2926_, 0);
                        v_isSharedCheck_2942_ = (!lean_is_exclusive(v___x_2926_)) as u8;
                        if v_isSharedCheck_2942_ == 0 {
                            v___x_2937_ = v___x_2926_;
                            v_isShared_2938_ = v_isSharedCheck_2942_;
                            state = 29;
                            continue;
                        } else {
                            lean_inc(v_a_2935_);
                            lean_dec(v___x_2926_);
                            v___x_2937_ = lean_box(0);
                            v_isShared_2938_ = v_isSharedCheck_2942_;
                            state = 29;
                            continue;
                        }
                    }
                } else {
                    v___x_2943_ = lean_io_get_num_heartbeats();
                    lean_inc(v___y_2915_);
                    lean_inc_ref(v___y_2920_);
                    lean_inc(v___y_2916_);
                    lean_inc_ref(v___y_2908_);
                    lean_inc(v___y_2919_);
                    lean_inc_ref(v___y_2917_);
                    v___x_2944_ = lean_apply_8(
                        v___y_2912_,
                        v___y_2910_,
                        v___y_2917_,
                        v___y_2919_,
                        v___y_2908_,
                        v___y_2916_,
                        v___y_2920_,
                        v___y_2915_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_2944_) == 0 {
                        v_a_2945_ = lean_ctor_get(v___x_2944_, 0);
                        v_isSharedCheck_2952_ = (!lean_is_exclusive(v___x_2944_)) as u8;
                        if v_isSharedCheck_2952_ == 0 {
                            v___x_2947_ = v___x_2944_;
                            v_isShared_2948_ = v_isSharedCheck_2952_;
                            state = 31;
                            continue;
                        } else {
                            lean_inc(v_a_2945_);
                            lean_dec(v___x_2944_);
                            v___x_2947_ = lean_box(0);
                            v_isShared_2948_ = v_isSharedCheck_2952_;
                            state = 31;
                            continue;
                        }
                    } else {
                        v_a_2953_ = lean_ctor_get(v___x_2944_, 0);
                        v_isSharedCheck_2960_ = (!lean_is_exclusive(v___x_2944_)) as u8;
                        if v_isSharedCheck_2960_ == 0 {
                            v___x_2955_ = v___x_2944_;
                            v_isShared_2956_ = v_isSharedCheck_2960_;
                            state = 33;
                            continue;
                        } else {
                            lean_inc(v_a_2953_);
                            lean_dec(v___x_2944_);
                            v___x_2955_ = lean_box(0);
                            v_isShared_2956_ = v_isSharedCheck_2960_;
                            state = 33;
                            continue;
                        }
                    }
                }
            }
            27 => {
                if v_isShared_2930_ == 0 {
                    lean_ctor_set_tag(v___x_2929_, 1);
                    v___x_2932_ = v___x_2929_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_2933_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2933_, 0, v_a_2927_);
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
                    lean_ctor_set_tag(v___x_2937_, 0);
                    v___x_2940_ = v___x_2937_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_2941_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2941_, 0, v_a_2935_);
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
                    lean_ctor_set_tag(v___x_2947_, 1);
                    v___x_2950_ = v___x_2947_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_2951_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2951_, 0, v_a_2945_);
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
                    lean_ctor_set_tag(v___x_2955_, 0);
                    v___x_2958_ = v___x_2955_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_2959_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2959_, 0, v_a_2953_);
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
                    v_options_2972_ = lean_ctor_get(v___y_2969_, 2);
                    v_hasTrace_2973_ = lean_ctor_get_uint8(
                        v_options_2972_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_2973_ == 0 {
                        v_run_x27_2974_ = lean_ctor_get(v___x_2971_, 1);
                        lean_inc_ref(v_run_x27_2974_);
                        lean_inc(v___y_2970_);
                        lean_inc_ref(v___y_2969_);
                        lean_inc(v___y_2968_);
                        lean_inc_ref(v___y_2967_);
                        lean_inc(v___y_2966_);
                        lean_inc_ref(v___y_2965_);
                        v___x_2975_ = lean_apply_8(
                            v_run_x27_2974_,
                            v_g_2964_,
                            v___y_2965_,
                            v___y_2966_,
                            v___y_2967_,
                            v___y_2968_,
                            v___y_2969_,
                            v___y_2970_,
                            lean_box(0),
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
                        v_run_x27_2976_ = lean_ctor_get(v___x_2971_, 1);
                        v_inheritedTraceOptions_2977_ = lean_ctor_get(v___y_2969_, 13);
                        lean_inc(v_g_2964_);
                        v___f_2978_ = lean_alloc_closure(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__1___boxed as *mut core::ffi::c_void, 10, 2);
                        lean_closure_set(v___f_2978_, 0, v___x_2971_);
                        lean_closure_set(v___f_2978_, 1, v_g_2964_);
                        v___x_2979_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__1;
                        v___x_2980_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7);
                        v___x_2981_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_2977_,
                            v_options_2972_,
                            v___x_2980_,
                        );
                        if v___x_2981_ == 0 {
                            v___x_2982_ = l_Lean_trace_profiler;
                            v___x_2983_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__1(v_options_2972_, v___x_2982_);
                            if v___x_2983_ == 0 {
                                lean_dec_ref(v___f_2978_);
                                lean_inc_ref(v_run_x27_2976_);
                                lean_inc(v___y_2970_);
                                lean_inc_ref(v___y_2969_);
                                lean_inc(v___y_2968_);
                                lean_inc_ref(v___y_2967_);
                                lean_inc(v___y_2966_);
                                lean_inc_ref(v___y_2965_);
                                v___x_2984_ = lean_apply_8(
                                    v_run_x27_2976_,
                                    v_g_2964_,
                                    v___y_2965_,
                                    v___y_2966_,
                                    v___y_2967_,
                                    v___y_2968_,
                                    v___y_2969_,
                                    v___y_2970_,
                                    lean_box(0),
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
                                lean_inc_ref(v_run_x27_2976_);
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
                            lean_inc_ref(v_run_x27_2976_);
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
                if lean_obj_tag(v___y_2993_) == 0 {
                    v_a_2994_ = lean_ctor_get(v___y_2993_, 0);
                    v_isSharedCheck_3003_ = (!lean_is_exclusive(v___y_2993_)) as u8;
                    if v_isSharedCheck_3003_ == 0 {
                        v___x_2996_ = v___y_2993_;
                        v_isShared_2997_ = v_isSharedCheck_3003_;
                        state = 37;
                        continue;
                    } else {
                        lean_inc(v_a_2994_);
                        lean_dec(v___y_2993_);
                        v___x_2996_ = lean_box(0);
                        v_isShared_2997_ = v_isSharedCheck_3003_;
                        state = 37;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2664_);
                    return v___y_2993_;
                }
            }
            37 => {
                if lean_obj_tag(v_a_2994_) == 1 {
                    lean_del_object(v___x_2996_);
                    v_val_2998_ = lean_ctor_get(v_a_2994_, 0);
                    lean_inc(v_val_2998_);
                    lean_dec_ref_known(v_a_2994_, 1);
                    v_fixedInt_2999_ = lean_ctor_get_uint8(
                        v___y_2992_,
                        (core::mem::size_of::<*mut LeanObject>() * 2 + 6) as u32,
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
                    lean_dec(v_a_2994_);
                    lean_del_object(v___x_2664_);
                    if v_isShared_2997_ == 0 {
                        lean_ctor_set(v___x_2996_, 0, v___x_2655_);
                        v___x_3001_ = v___x_2996_;
                        state = 38;
                        continue;
                    } else {
                        v_reuseFailAlloc_3002_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3002_, 0, v___x_2655_);
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
                v___x_3023_ = lean_box_float(v___x_3021_);
                v___x_3024_ = lean_box_float(v___x_3022_);
                v___x_3025_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3025_, 0, v___x_3023_);
                lean_ctor_set(v___x_3025_, 1, v___x_3024_);
                v___x_3026_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3026_, 0, v_a_3019_);
                lean_ctor_set(v___x_3026_, 1, v___x_3025_);
                lean_inc_ref(v___y_3013_);
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
                v___x_3046_ = lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__4_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__4);
                v___x_3047_ = lean_float_div(v___x_3045_, v___x_3046_);
                v___x_3048_ = lean_float_of_nat(v___x_3044_);
                v___x_3049_ = lean_float_div(v___x_3048_, v___x_3046_);
                v___x_3050_ = lean_box_float(v___x_3047_);
                v___x_3051_ = lean_box_float(v___x_3049_);
                v___x_3052_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3052_, 0, v___x_3050_);
                lean_ctor_set(v___x_3052_, 1, v___x_3051_);
                v___x_3053_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3053_, 0, v_a_3043_);
                lean_ctor_set(v___x_3053_, 1, v___x_3052_);
                lean_inc_ref(v___y_3038_);
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
                v_a_3071_ = lean_ctor_get(v___x_3070_, 0);
                lean_inc(v_a_3071_);
                lean_dec_ref(v___x_3070_);
                v___x_3072_ = l_Lean_trace_profiler_useHeartbeats;
                v___x_3073_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__1(v___y_3067_, v___x_3072_);
                if v___x_3073_ == 0 {
                    v___x_3074_ = lean_io_mono_nanos_now();
                    lean_inc(v___y_3056_);
                    lean_inc_ref(v___y_3061_);
                    lean_inc(v___y_3063_);
                    lean_inc_ref(v___y_3059_);
                    lean_inc(v___y_3066_);
                    lean_inc_ref(v___y_3057_);
                    v___x_3075_ = lean_apply_8(
                        v___y_3065_,
                        v___y_3069_,
                        v___y_3057_,
                        v___y_3066_,
                        v___y_3059_,
                        v___y_3063_,
                        v___y_3061_,
                        v___y_3056_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_3075_) == 0 {
                        v_a_3076_ = lean_ctor_get(v___x_3075_, 0);
                        v_isSharedCheck_3083_ = (!lean_is_exclusive(v___x_3075_)) as u8;
                        if v_isSharedCheck_3083_ == 0 {
                            v___x_3078_ = v___x_3075_;
                            v_isShared_3079_ = v_isSharedCheck_3083_;
                            state = 42;
                            continue;
                        } else {
                            lean_inc(v_a_3076_);
                            lean_dec(v___x_3075_);
                            v___x_3078_ = lean_box(0);
                            v_isShared_3079_ = v_isSharedCheck_3083_;
                            state = 42;
                            continue;
                        }
                    } else {
                        v_a_3084_ = lean_ctor_get(v___x_3075_, 0);
                        v_isSharedCheck_3091_ = (!lean_is_exclusive(v___x_3075_)) as u8;
                        if v_isSharedCheck_3091_ == 0 {
                            v___x_3086_ = v___x_3075_;
                            v_isShared_3087_ = v_isSharedCheck_3091_;
                            state = 44;
                            continue;
                        } else {
                            lean_inc(v_a_3084_);
                            lean_dec(v___x_3075_);
                            v___x_3086_ = lean_box(0);
                            v_isShared_3087_ = v_isSharedCheck_3091_;
                            state = 44;
                            continue;
                        }
                    }
                } else {
                    v___x_3092_ = lean_io_get_num_heartbeats();
                    lean_inc(v___y_3056_);
                    lean_inc_ref(v___y_3061_);
                    lean_inc(v___y_3063_);
                    lean_inc_ref(v___y_3059_);
                    lean_inc(v___y_3066_);
                    lean_inc_ref(v___y_3057_);
                    v___x_3093_ = lean_apply_8(
                        v___y_3065_,
                        v___y_3069_,
                        v___y_3057_,
                        v___y_3066_,
                        v___y_3059_,
                        v___y_3063_,
                        v___y_3061_,
                        v___y_3056_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_3093_) == 0 {
                        v_a_3094_ = lean_ctor_get(v___x_3093_, 0);
                        v_isSharedCheck_3101_ = (!lean_is_exclusive(v___x_3093_)) as u8;
                        if v_isSharedCheck_3101_ == 0 {
                            v___x_3096_ = v___x_3093_;
                            v_isShared_3097_ = v_isSharedCheck_3101_;
                            state = 46;
                            continue;
                        } else {
                            lean_inc(v_a_3094_);
                            lean_dec(v___x_3093_);
                            v___x_3096_ = lean_box(0);
                            v_isShared_3097_ = v_isSharedCheck_3101_;
                            state = 46;
                            continue;
                        }
                    } else {
                        v_a_3102_ = lean_ctor_get(v___x_3093_, 0);
                        v_isSharedCheck_3109_ = (!lean_is_exclusive(v___x_3093_)) as u8;
                        if v_isSharedCheck_3109_ == 0 {
                            v___x_3104_ = v___x_3093_;
                            v_isShared_3105_ = v_isSharedCheck_3109_;
                            state = 48;
                            continue;
                        } else {
                            lean_inc(v_a_3102_);
                            lean_dec(v___x_3093_);
                            v___x_3104_ = lean_box(0);
                            v_isShared_3105_ = v_isSharedCheck_3109_;
                            state = 48;
                            continue;
                        }
                    }
                }
            }
            42 => {
                if v_isShared_3079_ == 0 {
                    lean_ctor_set_tag(v___x_3078_, 1);
                    v___x_3081_ = v___x_3078_;
                    state = 43;
                    continue;
                } else {
                    v_reuseFailAlloc_3082_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3082_, 0, v_a_3076_);
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
                    lean_ctor_set_tag(v___x_3086_, 0);
                    v___x_3089_ = v___x_3086_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_3090_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3090_, 0, v_a_3084_);
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
                    lean_ctor_set_tag(v___x_3096_, 1);
                    v___x_3099_ = v___x_3096_;
                    state = 47;
                    continue;
                } else {
                    v_reuseFailAlloc_3100_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3100_, 0, v_a_3094_);
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
                    lean_ctor_set_tag(v___x_3104_, 0);
                    v___x_3107_ = v___x_3104_;
                    state = 49;
                    continue;
                } else {
                    v_reuseFailAlloc_3108_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3108_, 0, v_a_3102_);
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
                    v_options_3122_ = lean_ctor_get(v___y_3119_, 2);
                    v_hasTrace_3123_ = lean_ctor_get_uint8(
                        v_options_3122_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_3123_ == 0 {
                        v_run_x27_3124_ = lean_ctor_get(v___x_3121_, 1);
                        lean_inc_ref(v_run_x27_3124_);
                        lean_inc(v___y_3120_);
                        lean_inc_ref(v___y_3119_);
                        lean_inc(v___y_3118_);
                        lean_inc_ref(v___y_3117_);
                        lean_inc(v___y_3116_);
                        lean_inc_ref(v___y_3115_);
                        v___x_3125_ = lean_apply_8(
                            v_run_x27_3124_,
                            v_g_3114_,
                            v___y_3115_,
                            v___y_3116_,
                            v___y_3117_,
                            v___y_3118_,
                            v___y_3119_,
                            v___y_3120_,
                            lean_box(0),
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
                        v_run_x27_3126_ = lean_ctor_get(v___x_3121_, 1);
                        v_inheritedTraceOptions_3127_ = lean_ctor_get(v___y_3119_, 13);
                        lean_inc(v_g_3114_);
                        v___f_3128_ = lean_alloc_closure(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__1___boxed as *mut core::ffi::c_void, 10, 2);
                        lean_closure_set(v___f_3128_, 0, v___x_3121_);
                        lean_closure_set(v___f_3128_, 1, v_g_3114_);
                        v___x_3129_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__1;
                        v___x_3130_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7);
                        v___x_3131_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_3127_,
                            v_options_3122_,
                            v___x_3130_,
                        );
                        if v___x_3131_ == 0 {
                            v___x_3132_ = l_Lean_trace_profiler;
                            v___x_3133_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__1(v_options_3122_, v___x_3132_);
                            if v___x_3133_ == 0 {
                                lean_dec_ref(v___f_3128_);
                                lean_inc_ref(v_run_x27_3126_);
                                lean_inc(v___y_3120_);
                                lean_inc_ref(v___y_3119_);
                                lean_inc(v___y_3118_);
                                lean_inc_ref(v___y_3117_);
                                lean_inc(v___y_3116_);
                                lean_inc_ref(v___y_3115_);
                                v___x_3134_ = lean_apply_8(
                                    v_run_x27_3126_,
                                    v_g_3114_,
                                    v___y_3115_,
                                    v___y_3116_,
                                    v___y_3117_,
                                    v___y_3118_,
                                    v___y_3119_,
                                    v___y_3120_,
                                    lean_box(0),
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
                                lean_inc_ref(v_run_x27_3126_);
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
                            lean_inc_ref(v_run_x27_3126_);
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
                if lean_obj_tag(v___y_3143_) == 0 {
                    v_a_3144_ = lean_ctor_get(v___y_3143_, 0);
                    v_isSharedCheck_3154_ = (!lean_is_exclusive(v___y_3143_)) as u8;
                    if v_isSharedCheck_3154_ == 0 {
                        v___x_3146_ = v___y_3143_;
                        v_isShared_3147_ = v_isSharedCheck_3154_;
                        state = 52;
                        continue;
                    } else {
                        lean_inc(v_a_3144_);
                        lean_dec(v___y_3143_);
                        v___x_3146_ = lean_box(0);
                        v_isShared_3147_ = v_isSharedCheck_3154_;
                        state = 52;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2664_);
                    return v___y_3143_;
                }
            }
            52 => {
                if lean_obj_tag(v_a_3144_) == 1 {
                    lean_del_object(v___x_3146_);
                    v_val_3148_ = lean_ctor_get(v_a_3144_, 0);
                    lean_inc(v_val_3148_);
                    lean_dec_ref_known(v_a_3144_, 1);
                    v_fixedInt_3149_ = lean_ctor_get_uint8(
                        v___y_3141_,
                        (core::mem::size_of::<*mut LeanObject>() * 2 + 6) as u32,
                    );
                    v_enums_3150_ = lean_ctor_get_uint8(
                        v___y_3141_,
                        (core::mem::size_of::<*mut LeanObject>() * 2 + 7) as u32,
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
                    lean_dec(v_a_3144_);
                    lean_del_object(v___x_2664_);
                    if v_isShared_3147_ == 0 {
                        lean_ctor_set(v___x_3146_, 0, v___x_2655_);
                        v___x_3152_ = v___x_3146_;
                        state = 53;
                        continue;
                    } else {
                        v_reuseFailAlloc_3153_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3153_, 0, v___x_2655_);
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
                v___x_3174_ = lean_box_float(v___x_3172_);
                v___x_3175_ = lean_box_float(v___x_3173_);
                v___x_3176_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3176_, 0, v___x_3174_);
                lean_ctor_set(v___x_3176_, 1, v___x_3175_);
                v___x_3177_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3177_, 0, v_a_3170_);
                lean_ctor_set(v___x_3177_, 1, v___x_3176_);
                lean_inc_ref(v___y_3156_);
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
                v___x_3197_ = lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__4_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__4);
                v___x_3198_ = lean_float_div(v___x_3196_, v___x_3197_);
                v___x_3199_ = lean_float_of_nat(v___x_3195_);
                v___x_3200_ = lean_float_div(v___x_3199_, v___x_3197_);
                v___x_3201_ = lean_box_float(v___x_3198_);
                v___x_3202_ = lean_box_float(v___x_3200_);
                v___x_3203_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3203_, 0, v___x_3201_);
                lean_ctor_set(v___x_3203_, 1, v___x_3202_);
                v___x_3204_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3204_, 0, v_a_3194_);
                lean_ctor_set(v___x_3204_, 1, v___x_3203_);
                lean_inc_ref(v___y_3180_);
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
                v_a_3222_ = lean_ctor_get(v___x_3221_, 0);
                lean_inc(v_a_3222_);
                lean_dec_ref(v___x_3221_);
                v___x_3223_ = l_Lean_trace_profiler_useHeartbeats;
                v___x_3224_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__1(v___y_3213_, v___x_3223_);
                if v___x_3224_ == 0 {
                    v___x_3225_ = lean_io_mono_nanos_now();
                    lean_inc(v___y_3219_);
                    lean_inc_ref(v___y_3218_);
                    lean_inc(v___y_3216_);
                    lean_inc_ref(v___y_3215_);
                    lean_inc(v___y_3214_);
                    lean_inc_ref(v___y_3210_);
                    v___x_3226_ = lean_apply_8(
                        v___y_3209_,
                        v___y_3212_,
                        v___y_3210_,
                        v___y_3214_,
                        v___y_3215_,
                        v___y_3216_,
                        v___y_3218_,
                        v___y_3219_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_3226_) == 0 {
                        v_a_3227_ = lean_ctor_get(v___x_3226_, 0);
                        v_isSharedCheck_3234_ = (!lean_is_exclusive(v___x_3226_)) as u8;
                        if v_isSharedCheck_3234_ == 0 {
                            v___x_3229_ = v___x_3226_;
                            v_isShared_3230_ = v_isSharedCheck_3234_;
                            state = 57;
                            continue;
                        } else {
                            lean_inc(v_a_3227_);
                            lean_dec(v___x_3226_);
                            v___x_3229_ = lean_box(0);
                            v_isShared_3230_ = v_isSharedCheck_3234_;
                            state = 57;
                            continue;
                        }
                    } else {
                        v_a_3235_ = lean_ctor_get(v___x_3226_, 0);
                        v_isSharedCheck_3242_ = (!lean_is_exclusive(v___x_3226_)) as u8;
                        if v_isSharedCheck_3242_ == 0 {
                            v___x_3237_ = v___x_3226_;
                            v_isShared_3238_ = v_isSharedCheck_3242_;
                            state = 59;
                            continue;
                        } else {
                            lean_inc(v_a_3235_);
                            lean_dec(v___x_3226_);
                            v___x_3237_ = lean_box(0);
                            v_isShared_3238_ = v_isSharedCheck_3242_;
                            state = 59;
                            continue;
                        }
                    }
                } else {
                    v___x_3243_ = lean_io_get_num_heartbeats();
                    lean_inc(v___y_3219_);
                    lean_inc_ref(v___y_3218_);
                    lean_inc(v___y_3216_);
                    lean_inc_ref(v___y_3215_);
                    lean_inc(v___y_3214_);
                    lean_inc_ref(v___y_3210_);
                    v___x_3244_ = lean_apply_8(
                        v___y_3209_,
                        v___y_3212_,
                        v___y_3210_,
                        v___y_3214_,
                        v___y_3215_,
                        v___y_3216_,
                        v___y_3218_,
                        v___y_3219_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_3244_) == 0 {
                        v_a_3245_ = lean_ctor_get(v___x_3244_, 0);
                        v_isSharedCheck_3252_ = (!lean_is_exclusive(v___x_3244_)) as u8;
                        if v_isSharedCheck_3252_ == 0 {
                            v___x_3247_ = v___x_3244_;
                            v_isShared_3248_ = v_isSharedCheck_3252_;
                            state = 61;
                            continue;
                        } else {
                            lean_inc(v_a_3245_);
                            lean_dec(v___x_3244_);
                            v___x_3247_ = lean_box(0);
                            v_isShared_3248_ = v_isSharedCheck_3252_;
                            state = 61;
                            continue;
                        }
                    } else {
                        v_a_3253_ = lean_ctor_get(v___x_3244_, 0);
                        v_isSharedCheck_3260_ = (!lean_is_exclusive(v___x_3244_)) as u8;
                        if v_isSharedCheck_3260_ == 0 {
                            v___x_3255_ = v___x_3244_;
                            v_isShared_3256_ = v_isSharedCheck_3260_;
                            state = 63;
                            continue;
                        } else {
                            lean_inc(v_a_3253_);
                            lean_dec(v___x_3244_);
                            v___x_3255_ = lean_box(0);
                            v_isShared_3256_ = v_isSharedCheck_3260_;
                            state = 63;
                            continue;
                        }
                    }
                }
            }
            57 => {
                if v_isShared_3230_ == 0 {
                    lean_ctor_set_tag(v___x_3229_, 1);
                    v___x_3232_ = v___x_3229_;
                    state = 58;
                    continue;
                } else {
                    v_reuseFailAlloc_3233_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3233_, 0, v_a_3227_);
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
                    lean_ctor_set_tag(v___x_3237_, 0);
                    v___x_3240_ = v___x_3237_;
                    state = 60;
                    continue;
                } else {
                    v_reuseFailAlloc_3241_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3241_, 0, v_a_3235_);
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
                    lean_ctor_set_tag(v___x_3247_, 1);
                    v___x_3250_ = v___x_3247_;
                    state = 62;
                    continue;
                } else {
                    v_reuseFailAlloc_3251_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3251_, 0, v_a_3245_);
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
                    lean_ctor_set_tag(v___x_3255_, 0);
                    v___x_3258_ = v___x_3255_;
                    state = 64;
                    continue;
                } else {
                    v_reuseFailAlloc_3259_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3259_, 0, v_a_3253_);
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
                if lean_obj_tag(v___y_3268_) == 0 {
                    v_a_3269_ = lean_ctor_get(v___y_3268_, 0);
                    v_isSharedCheck_3295_ = (!lean_is_exclusive(v___y_3268_)) as u8;
                    if v_isSharedCheck_3295_ == 0 {
                        v___x_3271_ = v___y_3268_;
                        v_isShared_3272_ = v_isSharedCheck_3295_;
                        state = 66;
                        continue;
                    } else {
                        lean_inc(v_a_3269_);
                        lean_dec(v___y_3268_);
                        v___x_3271_ = lean_box(0);
                        v_isShared_3272_ = v_isSharedCheck_3295_;
                        state = 66;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2664_);
                    return v___y_3268_;
                }
            }
            66 => {
                if lean_obj_tag(v_a_3269_) == 1 {
                    lean_del_object(v___x_3271_);
                    v_structures_3273_ = lean_ctor_get_uint8(
                        v___y_3267_,
                        (core::mem::size_of::<*mut LeanObject>() * 2 + 5) as u32,
                    );
                    if v_structures_3273_ == 0 {
                        v_val_3274_ = lean_ctor_get(v_a_3269_, 0);
                        lean_inc(v_val_3274_);
                        lean_dec_ref_known(v_a_3269_, 1);
                        v_fixedInt_3275_ = lean_ctor_get_uint8(
                            v___y_3267_,
                            (core::mem::size_of::<*mut LeanObject>() * 2 + 6) as u32,
                        );
                        v_enums_3276_ = lean_ctor_get_uint8(
                            v___y_3267_,
                            (core::mem::size_of::<*mut LeanObject>() * 2 + 7) as u32,
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
                        v_val_3277_ = lean_ctor_get(v_a_3269_, 0);
                        lean_inc(v_val_3277_);
                        lean_dec_ref_known(v_a_3269_, 1);
                        v___x_3278_ = l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass;
                        v_options_3279_ = lean_ctor_get(v___y_3264_, 2);
                        v_hasTrace_3280_ = lean_ctor_get_uint8(
                            v_options_3279_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        );
                        if v_hasTrace_3280_ == 0 {
                            v_run_x27_3281_ = lean_ctor_get(v___x_3278_, 1);
                            lean_inc_ref(v_run_x27_3281_);
                            lean_inc(v___y_3263_);
                            lean_inc_ref(v___y_3264_);
                            lean_inc(v___y_3262_);
                            lean_inc_ref(v___y_3265_);
                            lean_inc(v___y_3266_);
                            lean_inc_ref(v___y_3267_);
                            v___x_3282_ = lean_apply_8(
                                v_run_x27_3281_,
                                v_val_3277_,
                                v___y_3267_,
                                v___y_3266_,
                                v___y_3265_,
                                v___y_3262_,
                                v___y_3264_,
                                v___y_3263_,
                                lean_box(0),
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
                            v_run_x27_3283_ = lean_ctor_get(v___x_3278_, 1);
                            v_inheritedTraceOptions_3284_ = lean_ctor_get(v___y_3264_, 13);
                            lean_inc(v_val_3277_);
                            v___f_3285_ = lean_alloc_closure(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___boxed as *mut core::ffi::c_void, 10, 2);
                            lean_closure_set(v___f_3285_, 0, v___x_3278_);
                            lean_closure_set(v___f_3285_, 1, v_val_3277_);
                            v___x_3286_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__1;
                            v___x_3287_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7);
                            v___x_3288_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                v_inheritedTraceOptions_3284_,
                                v_options_3279_,
                                v___x_3287_,
                            );
                            if v___x_3288_ == 0 {
                                v___x_3289_ = l_Lean_trace_profiler;
                                v___x_3290_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__1(v_options_3279_, v___x_3289_);
                                if v___x_3290_ == 0 {
                                    lean_dec_ref(v___f_3285_);
                                    lean_inc_ref(v_run_x27_3283_);
                                    lean_inc(v___y_3263_);
                                    lean_inc_ref(v___y_3264_);
                                    lean_inc(v___y_3262_);
                                    lean_inc_ref(v___y_3265_);
                                    lean_inc(v___y_3266_);
                                    lean_inc_ref(v___y_3267_);
                                    v___x_3291_ = lean_apply_8(
                                        v_run_x27_3283_,
                                        v_val_3277_,
                                        v___y_3267_,
                                        v___y_3266_,
                                        v___y_3265_,
                                        v___y_3262_,
                                        v___y_3264_,
                                        v___y_3263_,
                                        lean_box(0),
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
                                    lean_inc_ref(v_run_x27_3283_);
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
                                lean_inc_ref(v_run_x27_3283_);
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
                    lean_dec(v_a_3269_);
                    lean_del_object(v___x_2664_);
                    if v_isShared_3272_ == 0 {
                        lean_ctor_set(v___x_3271_, 0, v___x_2655_);
                        v___x_3293_ = v___x_3271_;
                        state = 67;
                        continue;
                    } else {
                        v_reuseFailAlloc_3294_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3294_, 0, v___x_2655_);
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
                v___x_3314_ = lean_box_float(v___x_3312_);
                v___x_3315_ = lean_box_float(v___x_3313_);
                v___x_3316_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3316_, 0, v___x_3314_);
                lean_ctor_set(v___x_3316_, 1, v___x_3315_);
                v___x_3317_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3317_, 0, v_a_3310_);
                lean_ctor_set(v___x_3317_, 1, v___x_3316_);
                lean_inc_ref(v___y_3301_);
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
                v___x_3336_ = lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__4_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__4);
                v___x_3337_ = lean_float_div(v___x_3335_, v___x_3336_);
                v___x_3338_ = lean_float_of_nat(v___x_3334_);
                v___x_3339_ = lean_float_div(v___x_3338_, v___x_3336_);
                v___x_3340_ = lean_box_float(v___x_3337_);
                v___x_3341_ = lean_box_float(v___x_3339_);
                v___x_3342_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3342_, 0, v___x_3340_);
                lean_ctor_set(v___x_3342_, 1, v___x_3341_);
                v___x_3343_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3343_, 0, v_a_3333_);
                lean_ctor_set(v___x_3343_, 1, v___x_3342_);
                lean_inc_ref(v___y_3324_);
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
                v_a_3359_ = lean_ctor_get(v___x_3358_, 0);
                lean_inc(v_a_3359_);
                lean_dec_ref(v___x_3358_);
                v___x_3360_ = l_Lean_trace_profiler_useHeartbeats;
                v___x_3361_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__1(v___y_3347_, v___x_3360_);
                if v___x_3361_ == 0 {
                    v___x_3362_ = lean_io_mono_nanos_now();
                    lean_inc(v___y_3348_);
                    lean_inc_ref(v___y_3349_);
                    lean_inc(v___y_3346_);
                    lean_inc_ref(v___y_3354_);
                    lean_inc(v___y_3355_);
                    lean_inc_ref(v___y_3351_);
                    v___x_3363_ = lean_apply_8(
                        v___y_3353_,
                        v_val_2662_,
                        v___y_3351_,
                        v___y_3355_,
                        v___y_3354_,
                        v___y_3346_,
                        v___y_3349_,
                        v___y_3348_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_3363_) == 0 {
                        v_a_3364_ = lean_ctor_get(v___x_3363_, 0);
                        v_isSharedCheck_3371_ = (!lean_is_exclusive(v___x_3363_)) as u8;
                        if v_isSharedCheck_3371_ == 0 {
                            v___x_3366_ = v___x_3363_;
                            v_isShared_3367_ = v_isSharedCheck_3371_;
                            state = 71;
                            continue;
                        } else {
                            lean_inc(v_a_3364_);
                            lean_dec(v___x_3363_);
                            v___x_3366_ = lean_box(0);
                            v_isShared_3367_ = v_isSharedCheck_3371_;
                            state = 71;
                            continue;
                        }
                    } else {
                        v_a_3372_ = lean_ctor_get(v___x_3363_, 0);
                        v_isSharedCheck_3379_ = (!lean_is_exclusive(v___x_3363_)) as u8;
                        if v_isSharedCheck_3379_ == 0 {
                            v___x_3374_ = v___x_3363_;
                            v_isShared_3375_ = v_isSharedCheck_3379_;
                            state = 73;
                            continue;
                        } else {
                            lean_inc(v_a_3372_);
                            lean_dec(v___x_3363_);
                            v___x_3374_ = lean_box(0);
                            v_isShared_3375_ = v_isSharedCheck_3379_;
                            state = 73;
                            continue;
                        }
                    }
                } else {
                    v___x_3380_ = lean_io_get_num_heartbeats();
                    lean_inc(v___y_3348_);
                    lean_inc_ref(v___y_3349_);
                    lean_inc(v___y_3346_);
                    lean_inc_ref(v___y_3354_);
                    lean_inc(v___y_3355_);
                    lean_inc_ref(v___y_3351_);
                    v___x_3381_ = lean_apply_8(
                        v___y_3353_,
                        v_val_2662_,
                        v___y_3351_,
                        v___y_3355_,
                        v___y_3354_,
                        v___y_3346_,
                        v___y_3349_,
                        v___y_3348_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_3381_) == 0 {
                        v_a_3382_ = lean_ctor_get(v___x_3381_, 0);
                        v_isSharedCheck_3389_ = (!lean_is_exclusive(v___x_3381_)) as u8;
                        if v_isSharedCheck_3389_ == 0 {
                            v___x_3384_ = v___x_3381_;
                            v_isShared_3385_ = v_isSharedCheck_3389_;
                            state = 75;
                            continue;
                        } else {
                            lean_inc(v_a_3382_);
                            lean_dec(v___x_3381_);
                            v___x_3384_ = lean_box(0);
                            v_isShared_3385_ = v_isSharedCheck_3389_;
                            state = 75;
                            continue;
                        }
                    } else {
                        v_a_3390_ = lean_ctor_get(v___x_3381_, 0);
                        v_isSharedCheck_3397_ = (!lean_is_exclusive(v___x_3381_)) as u8;
                        if v_isSharedCheck_3397_ == 0 {
                            v___x_3392_ = v___x_3381_;
                            v_isShared_3393_ = v_isSharedCheck_3397_;
                            state = 77;
                            continue;
                        } else {
                            lean_inc(v_a_3390_);
                            lean_dec(v___x_3381_);
                            v___x_3392_ = lean_box(0);
                            v_isShared_3393_ = v_isSharedCheck_3397_;
                            state = 77;
                            continue;
                        }
                    }
                }
            }
            71 => {
                if v_isShared_3367_ == 0 {
                    lean_ctor_set_tag(v___x_3366_, 1);
                    v___x_3369_ = v___x_3366_;
                    state = 72;
                    continue;
                } else {
                    v_reuseFailAlloc_3370_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3370_, 0, v_a_3364_);
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
                    lean_ctor_set_tag(v___x_3374_, 0);
                    v___x_3377_ = v___x_3374_;
                    state = 74;
                    continue;
                } else {
                    v_reuseFailAlloc_3378_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3378_, 0, v_a_3372_);
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
                    lean_ctor_set_tag(v___x_3384_, 1);
                    v___x_3387_ = v___x_3384_;
                    state = 76;
                    continue;
                } else {
                    v_reuseFailAlloc_3388_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3388_, 0, v_a_3382_);
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
                    lean_ctor_set_tag(v___x_3392_, 0);
                    v___x_3395_ = v___x_3392_;
                    state = 78;
                    continue;
                } else {
                    v_reuseFailAlloc_3396_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3396_, 0, v_a_3390_);
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
                v_options_3406_ = lean_ctor_get(v___y_3401_, 2);
                v_hasTrace_3407_ = lean_ctor_get_uint8(
                    v_options_3406_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                if v_hasTrace_3407_ == 0 {
                    v_run_x27_3408_ = lean_ctor_get(v___x_3405_, 1);
                    lean_inc_ref(v_run_x27_3408_);
                    lean_inc(v___y_3400_);
                    lean_inc_ref(v___y_3401_);
                    lean_inc(v___y_3399_);
                    lean_inc_ref(v___y_3402_);
                    lean_inc(v___y_3403_);
                    lean_inc_ref(v___y_3404_);
                    v___x_3409_ = lean_apply_8(
                        v_run_x27_3408_,
                        v_val_2662_,
                        v___y_3404_,
                        v___y_3403_,
                        v___y_3402_,
                        v___y_3399_,
                        v___y_3401_,
                        v___y_3400_,
                        lean_box(0),
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
                    v_run_x27_3410_ = lean_ctor_get(v___x_3405_, 1);
                    v_inheritedTraceOptions_3411_ = lean_ctor_get(v___y_3401_, 13);
                    lean_inc(v_val_2662_);
                    v___f_3412_ = lean_alloc_closure(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___boxed as *mut core::ffi::c_void, 10, 2);
                    lean_closure_set(v___f_3412_, 0, v___x_3405_);
                    lean_closure_set(v___f_3412_, 1, v_val_2662_);
                    v___x_3413_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__1;
                    v___x_3414_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7);
                    v___x_3415_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_3411_,
                        v_options_3406_,
                        v___x_3414_,
                    );
                    if v___x_3415_ == 0 {
                        v___x_3416_ = l_Lean_trace_profiler;
                        v___x_3417_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__1(v_options_3406_, v___x_3416_);
                        if v___x_3417_ == 0 {
                            lean_dec_ref(v___f_3412_);
                            lean_inc_ref(v_run_x27_3410_);
                            lean_inc(v___y_3400_);
                            lean_inc_ref(v___y_3401_);
                            lean_inc(v___y_3399_);
                            lean_inc_ref(v___y_3402_);
                            lean_inc(v___y_3403_);
                            lean_inc_ref(v___y_3404_);
                            v___x_3418_ = lean_apply_8(
                                v_run_x27_3410_,
                                v_val_2662_,
                                v___y_3404_,
                                v___y_3403_,
                                v___y_3402_,
                                v___y_3399_,
                                v___y_3401_,
                                v___y_3400_,
                                lean_box(0),
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
                            lean_inc_ref(v_run_x27_3410_);
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
                        lean_inc_ref(v_run_x27_3410_);
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
                v_structures_3426_ = lean_ctor_get_uint8(
                    v___y_3420_,
                    (core::mem::size_of::<*mut LeanObject>() * 2 + 5) as u32,
                );
                if v_structures_3426_ == 0 {
                    v_enums_3427_ = lean_ctor_get_uint8(
                        v___y_3420_,
                        (core::mem::size_of::<*mut LeanObject>() * 2 + 7) as u32,
                    );
                    if v_enums_3427_ == 0 {
                        v_fixedInt_3428_ = lean_ctor_get_uint8(
                            v___y_3420_,
                            (core::mem::size_of::<*mut LeanObject>() * 2 + 6) as u32,
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
                    v_reuseFailAlloc_3441_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3441_, 0, v_a_3435_);
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
    mut v_g_3448_: *mut LeanObject,
    mut v_a_3449_: *mut LeanObject,
    mut v_a_3450_: *mut LeanObject,
    mut v_a_3451_: *mut LeanObject,
    mut v_a_3452_: *mut LeanObject,
    mut v_a_3453_: *mut LeanObject,
    mut v_a_3454_: *mut LeanObject,
    mut v_a_3455_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3456_: *mut LeanObject = core::ptr::null_mut();
    v_res_3456_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go(v_g_3448_, v_a_3449_, v_a_3450_, v_a_3451_, v_a_3452_, v_a_3453_, v_a_3454_);
    lean_dec(v_a_3454_);
    lean_dec_ref(v_a_3453_);
    lean_dec(v_a_3452_);
    lean_dec_ref(v_a_3451_);
    lean_dec(v_a_3450_);
    lean_dec_ref(v_a_3449_);
    return v_res_3456_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__4(
    mut v_00_u03b1_3457_: *mut LeanObject,
    mut v_x_3458_: *mut LeanObject,
    mut v___y_3459_: *mut LeanObject,
    mut v___y_3460_: *mut LeanObject,
    mut v___y_3461_: *mut LeanObject,
    mut v___y_3462_: *mut LeanObject,
    mut v___y_3463_: *mut LeanObject,
    mut v___y_3464_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3466_: *mut LeanObject = core::ptr::null_mut();
    v___x_3466_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__4___redArg(v_x_3458_);
    return v___x_3466_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__4___boxed(
    mut v_00_u03b1_3467_: *mut LeanObject,
    mut v_x_3468_: *mut LeanObject,
    mut v___y_3469_: *mut LeanObject,
    mut v___y_3470_: *mut LeanObject,
    mut v___y_3471_: *mut LeanObject,
    mut v___y_3472_: *mut LeanObject,
    mut v___y_3473_: *mut LeanObject,
    mut v___y_3474_: *mut LeanObject,
    mut v___y_3475_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3476_: *mut LeanObject = core::ptr::null_mut();
    v_res_3476_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__4(v_00_u03b1_3467_, v_x_3468_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_);
    lean_dec(v___y_3474_);
    lean_dec_ref(v___y_3473_);
    lean_dec(v___y_3472_);
    lean_dec_ref(v___y_3471_);
    lean_dec(v___y_3470_);
    lean_dec_ref(v___y_3469_);
    return v_res_3476_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3(
    mut v_cls_3477_: *mut LeanObject,
    mut v_msg_3478_: *mut LeanObject,
    mut v___y_3479_: *mut LeanObject,
    mut v___y_3480_: *mut LeanObject,
    mut v___y_3481_: *mut LeanObject,
    mut v___y_3482_: *mut LeanObject,
    mut v___y_3483_: *mut LeanObject,
    mut v___y_3484_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3486_: *mut LeanObject = core::ptr::null_mut();
    v___x_3486_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg(v_cls_3477_, v_msg_3478_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_);
    return v___x_3486_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___boxed(
    mut v_cls_3487_: *mut LeanObject,
    mut v_msg_3488_: *mut LeanObject,
    mut v___y_3489_: *mut LeanObject,
    mut v___y_3490_: *mut LeanObject,
    mut v___y_3491_: *mut LeanObject,
    mut v___y_3492_: *mut LeanObject,
    mut v___y_3493_: *mut LeanObject,
    mut v___y_3494_: *mut LeanObject,
    mut v___y_3495_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3496_: *mut LeanObject = core::ptr::null_mut();
    v_res_3496_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3(v_cls_3487_, v_msg_3488_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_);
    lean_dec(v___y_3494_);
    lean_dec_ref(v___y_3493_);
    lean_dec(v___y_3492_);
    lean_dec_ref(v___y_3491_);
    lean_dec(v___y_3490_);
    lean_dec_ref(v___y_3489_);
    return v_res_3496_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__3(
    mut v_oldTraces_3497_: *mut LeanObject,
    mut v_data_3498_: *mut LeanObject,
    mut v_ref_3499_: *mut LeanObject,
    mut v_msg_3500_: *mut LeanObject,
    mut v___y_3501_: *mut LeanObject,
    mut v___y_3502_: *mut LeanObject,
    mut v___y_3503_: *mut LeanObject,
    mut v___y_3504_: *mut LeanObject,
    mut v___y_3505_: *mut LeanObject,
    mut v___y_3506_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3508_: *mut LeanObject = core::ptr::null_mut();
    v___x_3508_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__3___redArg(v_oldTraces_3497_, v_data_3498_, v_ref_3499_, v_msg_3500_, v___y_3503_, v___y_3504_, v___y_3505_, v___y_3506_);
    return v___x_3508_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__3___boxed(
    mut v_oldTraces_3509_: *mut LeanObject,
    mut v_data_3510_: *mut LeanObject,
    mut v_ref_3511_: *mut LeanObject,
    mut v_msg_3512_: *mut LeanObject,
    mut v___y_3513_: *mut LeanObject,
    mut v___y_3514_: *mut LeanObject,
    mut v___y_3515_: *mut LeanObject,
    mut v___y_3516_: *mut LeanObject,
    mut v___y_3517_: *mut LeanObject,
    mut v___y_3518_: *mut LeanObject,
    mut v___y_3519_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3520_: *mut LeanObject = core::ptr::null_mut();
    v_res_3520_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__3(v_oldTraces_3509_, v_data_3510_, v_ref_3511_, v_msg_3512_, v___y_3513_, v___y_3514_, v___y_3515_, v___y_3516_, v___y_3517_, v___y_3518_);
    lean_dec(v___y_3518_);
    lean_dec_ref(v___y_3517_);
    lean_dec(v___y_3516_);
    lean_dec_ref(v___y_3515_);
    lean_dec(v___y_3514_);
    lean_dec_ref(v___y_3513_);
    return v_res_3520_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg(
    mut v_mvarId_3521_: *mut LeanObject,
    mut v_x_3522_: *mut LeanObject,
    mut v___y_3523_: *mut LeanObject,
    mut v___y_3524_: *mut LeanObject,
    mut v___y_3525_: *mut LeanObject,
    mut v___y_3526_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3532_: u8 = 0;
    let mut v___x_3534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3536_: u8 = 0;
    let mut v_a_3537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3540_: u8 = 0;
    let mut v___x_3542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3544_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3528_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    lean_box(0),
                    v_mvarId_3521_,
                    v_x_3522_,
                    v___y_3523_,
                    v___y_3524_,
                    v___y_3525_,
                    v___y_3526_,
                );
                if lean_obj_tag(v___x_3528_) == 0 {
                    v_a_3529_ = lean_ctor_get(v___x_3528_, 0);
                    v_isSharedCheck_3536_ = (!lean_is_exclusive(v___x_3528_)) as u8;
                    if v_isSharedCheck_3536_ == 0 {
                        v___x_3531_ = v___x_3528_;
                        v_isShared_3532_ = v_isSharedCheck_3536_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3529_);
                        lean_dec(v___x_3528_);
                        v___x_3531_ = lean_box(0);
                        v_isShared_3532_ = v_isSharedCheck_3536_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3537_ = lean_ctor_get(v___x_3528_, 0);
                    v_isSharedCheck_3544_ = (!lean_is_exclusive(v___x_3528_)) as u8;
                    if v_isSharedCheck_3544_ == 0 {
                        v___x_3539_ = v___x_3528_;
                        v_isShared_3540_ = v_isSharedCheck_3544_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3537_);
                        lean_dec(v___x_3528_);
                        v___x_3539_ = lean_box(0);
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
                    v_reuseFailAlloc_3535_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3535_, 0, v_a_3529_);
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
                    v_reuseFailAlloc_3543_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3543_, 0, v_a_3537_);
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
    mut v_mvarId_3545_: *mut LeanObject,
    mut v_x_3546_: *mut LeanObject,
    mut v___y_3547_: *mut LeanObject,
    mut v___y_3548_: *mut LeanObject,
    mut v___y_3549_: *mut LeanObject,
    mut v___y_3550_: *mut LeanObject,
    mut v___y_3551_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3552_: *mut LeanObject = core::ptr::null_mut();
    v_res_3552_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg(v_mvarId_3545_, v_x_3546_, v___y_3547_, v___y_3548_, v___y_3549_, v___y_3550_);
    lean_dec(v___y_3550_);
    lean_dec_ref(v___y_3549_);
    lean_dec(v___y_3548_);
    lean_dec_ref(v___y_3547_);
    return v_res_3552_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0(
    mut v_00_u03b1_3553_: *mut LeanObject,
    mut v_mvarId_3554_: *mut LeanObject,
    mut v_x_3555_: *mut LeanObject,
    mut v___y_3556_: *mut LeanObject,
    mut v___y_3557_: *mut LeanObject,
    mut v___y_3558_: *mut LeanObject,
    mut v___y_3559_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3561_: *mut LeanObject = core::ptr::null_mut();
    v___x_3561_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg(v_mvarId_3554_, v_x_3555_, v___y_3556_, v___y_3557_, v___y_3558_, v___y_3559_);
    return v___x_3561_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___boxed(
    mut v_00_u03b1_3562_: *mut LeanObject,
    mut v_mvarId_3563_: *mut LeanObject,
    mut v_x_3564_: *mut LeanObject,
    mut v___y_3565_: *mut LeanObject,
    mut v___y_3566_: *mut LeanObject,
    mut v___y_3567_: *mut LeanObject,
    mut v___y_3568_: *mut LeanObject,
    mut v___y_3569_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3570_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_3568_);
    lean_dec_ref(v___y_3567_);
    lean_dec(v___y_3566_);
    lean_dec_ref(v___y_3565_);
    return v_res_3570_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1___redArg(
    mut v___y_3571_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_3574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traces_3575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_3577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_3580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_3582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_3583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_3584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3588_: u8 = 0;
    let mut v_tid_3589_: u64 = 0;
    let mut v___x_3591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3592_: u8 = 0;
    let mut v___x_3593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3604_: u8 = 0;
    let mut v_unused_3605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3606_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3573_ = lean_st_ref_get(v___y_3571_);
                v_traceState_3574_ = lean_ctor_get(v___x_3573_, 4);
                lean_inc_ref(v_traceState_3574_);
                lean_dec(v___x_3573_);
                v_traces_3575_ = lean_ctor_get(v_traceState_3574_, 0);
                lean_inc_ref(v_traces_3575_);
                lean_dec_ref(v_traceState_3574_);
                v___x_3576_ = lean_st_ref_take(v___y_3571_);
                v_traceState_3577_ = lean_ctor_get(v___x_3576_, 4);
                v_env_3578_ = lean_ctor_get(v___x_3576_, 0);
                v_nextMacroScope_3579_ = lean_ctor_get(v___x_3576_, 1);
                v_ngen_3580_ = lean_ctor_get(v___x_3576_, 2);
                v_auxDeclNGen_3581_ = lean_ctor_get(v___x_3576_, 3);
                v_cache_3582_ = lean_ctor_get(v___x_3576_, 5);
                v_messages_3583_ = lean_ctor_get(v___x_3576_, 6);
                v_infoState_3584_ = lean_ctor_get(v___x_3576_, 7);
                v_snapshotTasks_3585_ = lean_ctor_get(v___x_3576_, 8);
                v_isSharedCheck_3606_ = (!lean_is_exclusive(v___x_3576_)) as u8;
                if v_isSharedCheck_3606_ == 0 {
                    v___x_3587_ = v___x_3576_;
                    v_isShared_3588_ = v_isSharedCheck_3606_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_3585_);
                    lean_inc(v_infoState_3584_);
                    lean_inc(v_messages_3583_);
                    lean_inc(v_cache_3582_);
                    lean_inc(v_traceState_3577_);
                    lean_inc(v_auxDeclNGen_3581_);
                    lean_inc(v_ngen_3580_);
                    lean_inc(v_nextMacroScope_3579_);
                    lean_inc(v_env_3578_);
                    lean_dec(v___x_3576_);
                    v___x_3587_ = lean_box(0);
                    v_isShared_3588_ = v_isSharedCheck_3606_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_tid_3589_ = lean_ctor_get_uint64(
                    v_traceState_3577_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_3604_ = (!lean_is_exclusive(v_traceState_3577_)) as u8;
                if v_isSharedCheck_3604_ == 0 {
                    v_unused_3605_ = lean_ctor_get(v_traceState_3577_, 0);
                    lean_dec(v_unused_3605_);
                    v___x_3591_ = v_traceState_3577_;
                    v_isShared_3592_ = v_isSharedCheck_3604_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_traceState_3577_);
                    v___x_3591_ = lean_box(0);
                    v_isShared_3592_ = v_isSharedCheck_3604_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3593_ = lean_unsigned_to_nat(32);
                v___x_3594_ = lean_mk_empty_array_with_capacity(v___x_3593_);
                lean_dec_ref(v___x_3594_);
                v___x_3595_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___redArg___closed__1_once), _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___redArg___closed__1);
                if v_isShared_3592_ == 0 {
                    lean_ctor_set(v___x_3591_, 0, v___x_3595_);
                    v___x_3597_ = v___x_3591_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3603_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3603_, 0, v___x_3595_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_3603_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_3589_,
                    );
                    v___x_3597_ = v_reuseFailAlloc_3603_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3588_ == 0 {
                    lean_ctor_set(v___x_3587_, 4, v___x_3597_);
                    v___x_3599_ = v___x_3587_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3602_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3602_, 0, v_env_3578_);
                    lean_ctor_set(v_reuseFailAlloc_3602_, 1, v_nextMacroScope_3579_);
                    lean_ctor_set(v_reuseFailAlloc_3602_, 2, v_ngen_3580_);
                    lean_ctor_set(v_reuseFailAlloc_3602_, 3, v_auxDeclNGen_3581_);
                    lean_ctor_set(v_reuseFailAlloc_3602_, 4, v___x_3597_);
                    lean_ctor_set(v_reuseFailAlloc_3602_, 5, v_cache_3582_);
                    lean_ctor_set(v_reuseFailAlloc_3602_, 6, v_messages_3583_);
                    lean_ctor_set(v_reuseFailAlloc_3602_, 7, v_infoState_3584_);
                    lean_ctor_set(v_reuseFailAlloc_3602_, 8, v_snapshotTasks_3585_);
                    v___x_3599_ = v_reuseFailAlloc_3602_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3600_ = lean_st_ref_set(v___y_3571_, v___x_3599_);
                v___x_3601_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3601_, 0, v_traces_3575_);
                return v___x_3601_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1___redArg___boxed(
    mut v___y_3607_: *mut LeanObject,
    mut v___y_3608_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3609_: *mut LeanObject = core::ptr::null_mut();
    v_res_3609_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1___redArg(v___y_3607_);
    lean_dec(v___y_3607_);
    return v_res_3609_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(
    mut v___y_3610_: *mut LeanObject,
    mut v___y_3611_: *mut LeanObject,
    mut v___y_3612_: *mut LeanObject,
    mut v___y_3613_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3615_: *mut LeanObject = core::ptr::null_mut();
    v___x_3615_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1___redArg(v___y_3613_);
    return v___x_3615_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1___boxed(
    mut v___y_3616_: *mut LeanObject,
    mut v___y_3617_: *mut LeanObject,
    mut v___y_3618_: *mut LeanObject,
    mut v___y_3619_: *mut LeanObject,
    mut v___y_3620_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3621_: *mut LeanObject = core::ptr::null_mut();
    v_res_3621_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v___y_3616_, v___y_3617_, v___y_3618_, v___y_3619_);
    lean_dec(v___y_3619_);
    lean_dec_ref(v___y_3618_);
    lean_dec(v___y_3617_);
    lean_dec_ref(v___y_3616_);
    return v_res_3621_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___closed__2()
-> *mut LeanObject {
    let mut v___x_3625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut LeanObject = core::ptr::null_mut();
    v___x_3625_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___closed__1;
    v___x_3626_ = l_Lean_MessageData_ofFormat(v___x_3625_);
    return v___x_3626_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0(
    mut v_x_3627_: *mut LeanObject,
    mut v___y_3628_: *mut LeanObject,
    mut v___y_3629_: *mut LeanObject,
    mut v___y_3630_: *mut LeanObject,
    mut v___y_3631_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut LeanObject = core::ptr::null_mut();
    v___x_3633_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___closed__2_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___closed__2,
    );
    v___x_3634_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3634_, 0, v___x_3633_);
    return v___x_3634_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___boxed(
    mut v_x_3635_: *mut LeanObject,
    mut v___y_3636_: *mut LeanObject,
    mut v___y_3637_: *mut LeanObject,
    mut v___y_3638_: *mut LeanObject,
    mut v___y_3639_: *mut LeanObject,
    mut v___y_3640_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3641_: *mut LeanObject = core::ptr::null_mut();
    v_res_3641_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0(
        v_x_3635_,
        v___y_3636_,
        v___y_3637_,
        v___y_3638_,
        v___y_3639_,
    );
    lean_dec(v___y_3639_);
    lean_dec_ref(v___y_3638_);
    lean_dec(v___y_3637_);
    lean_dec_ref(v___y_3636_);
    lean_dec_ref(v_x_3635_);
    return v_res_3641_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__2(
    mut v_oldTraces_3642_: *mut LeanObject,
    mut v_data_3643_: *mut LeanObject,
    mut v_ref_3644_: *mut LeanObject,
    mut v_msg_3645_: *mut LeanObject,
    mut v___y_3646_: *mut LeanObject,
    mut v___y_3647_: *mut LeanObject,
    mut v___y_3648_: *mut LeanObject,
    mut v___y_3649_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_3651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_3653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_3655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_3659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_3660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_3663_: u8 = 0;
    let mut v_cancelTk_x3f_3664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3665_: u8 = 0;
    let mut v_inheritedTraceOptions_3666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_3668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traces_3669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3673_: usize = 0;
    let mut v___x_3674_: usize = 0;
    let mut v___x_3675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msg_3676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3681_: u8 = 0;
    let mut v___x_3682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_3683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_3686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_3688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_3689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_3690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3694_: u8 = 0;
    let mut v_tid_3695_: u64 = 0;
    let mut v___x_3697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3698_: u8 = 0;
    let mut v___x_3699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3712_: u8 = 0;
    let mut v_unused_3713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3714_: u8 = 0;
    let mut v_isSharedCheck_3715_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_3651_ = lean_ctor_get(v___y_3648_, 0);
                v_fileMap_3652_ = lean_ctor_get(v___y_3648_, 1);
                v_options_3653_ = lean_ctor_get(v___y_3648_, 2);
                v_currRecDepth_3654_ = lean_ctor_get(v___y_3648_, 3);
                v_maxRecDepth_3655_ = lean_ctor_get(v___y_3648_, 4);
                v_ref_3656_ = lean_ctor_get(v___y_3648_, 5);
                v_currNamespace_3657_ = lean_ctor_get(v___y_3648_, 6);
                v_openDecls_3658_ = lean_ctor_get(v___y_3648_, 7);
                v_initHeartbeats_3659_ = lean_ctor_get(v___y_3648_, 8);
                v_maxHeartbeats_3660_ = lean_ctor_get(v___y_3648_, 9);
                v_quotContext_3661_ = lean_ctor_get(v___y_3648_, 10);
                v_currMacroScope_3662_ = lean_ctor_get(v___y_3648_, 11);
                v_diag_3663_ = lean_ctor_get_uint8(
                    v___y_3648_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_3664_ = lean_ctor_get(v___y_3648_, 12);
                v_suppressElabErrors_3665_ = lean_ctor_get_uint8(
                    v___y_3648_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_3666_ = lean_ctor_get(v___y_3648_, 13);
                v___x_3667_ = lean_st_ref_get(v___y_3649_);
                v_traceState_3668_ = lean_ctor_get(v___x_3667_, 4);
                lean_inc_ref(v_traceState_3668_);
                lean_dec(v___x_3667_);
                v_traces_3669_ = lean_ctor_get(v_traceState_3668_, 0);
                lean_inc_ref(v_traces_3669_);
                lean_dec_ref(v_traceState_3668_);
                v_ref_3670_ = l_Lean_replaceRef(v_ref_3644_, v_ref_3656_);
                lean_inc_ref(v_inheritedTraceOptions_3666_);
                lean_inc(v_cancelTk_x3f_3664_);
                lean_inc(v_currMacroScope_3662_);
                lean_inc(v_quotContext_3661_);
                lean_inc(v_maxHeartbeats_3660_);
                lean_inc(v_initHeartbeats_3659_);
                lean_inc(v_openDecls_3658_);
                lean_inc(v_currNamespace_3657_);
                lean_inc(v_maxRecDepth_3655_);
                lean_inc(v_currRecDepth_3654_);
                lean_inc_ref(v_options_3653_);
                lean_inc_ref(v_fileMap_3652_);
                lean_inc_ref(v_fileName_3651_);
                v___x_3671_ = lean_alloc_ctor(0, 14, (2) as u32);
                lean_ctor_set(v___x_3671_, 0, v_fileName_3651_);
                lean_ctor_set(v___x_3671_, 1, v_fileMap_3652_);
                lean_ctor_set(v___x_3671_, 2, v_options_3653_);
                lean_ctor_set(v___x_3671_, 3, v_currRecDepth_3654_);
                lean_ctor_set(v___x_3671_, 4, v_maxRecDepth_3655_);
                lean_ctor_set(v___x_3671_, 5, v_ref_3670_);
                lean_ctor_set(v___x_3671_, 6, v_currNamespace_3657_);
                lean_ctor_set(v___x_3671_, 7, v_openDecls_3658_);
                lean_ctor_set(v___x_3671_, 8, v_initHeartbeats_3659_);
                lean_ctor_set(v___x_3671_, 9, v_maxHeartbeats_3660_);
                lean_ctor_set(v___x_3671_, 10, v_quotContext_3661_);
                lean_ctor_set(v___x_3671_, 11, v_currMacroScope_3662_);
                lean_ctor_set(v___x_3671_, 12, v_cancelTk_x3f_3664_);
                lean_ctor_set(v___x_3671_, 13, v_inheritedTraceOptions_3666_);
                lean_ctor_set_uint8(
                    v___x_3671_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    v_diag_3663_,
                );
                lean_ctor_set_uint8(
                    v___x_3671_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_3665_,
                );
                v___x_3672_ = l_Lean_PersistentArray_toArray___redArg(v_traces_3669_);
                lean_dec_ref(v_traces_3669_);
                v_sz_3673_ = lean_array_size(v___x_3672_);
                v___x_3674_ = 0usize;
                v___x_3675_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__3_spec__4(v_sz_3673_, v___x_3674_, v___x_3672_);
                v_msg_3676_ = lean_alloc_ctor(9, 3, (0) as u32);
                lean_ctor_set(v_msg_3676_, 0, v_data_3643_);
                lean_ctor_set(v_msg_3676_, 1, v_msg_3645_);
                lean_ctor_set(v_msg_3676_, 2, v___x_3675_);
                v___x_3677_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3_spec__7(v_msg_3676_, v___y_3646_, v___y_3647_, v___x_3671_, v___y_3649_);
                lean_dec_ref_known(v___x_3671_, 14);
                v_a_3678_ = lean_ctor_get(v___x_3677_, 0);
                v_isSharedCheck_3715_ = (!lean_is_exclusive(v___x_3677_)) as u8;
                if v_isSharedCheck_3715_ == 0 {
                    v___x_3680_ = v___x_3677_;
                    v_isShared_3681_ = v_isSharedCheck_3715_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_3678_);
                    lean_dec(v___x_3677_);
                    v___x_3680_ = lean_box(0);
                    v_isShared_3681_ = v_isSharedCheck_3715_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3682_ = lean_st_ref_take(v___y_3649_);
                v_traceState_3683_ = lean_ctor_get(v___x_3682_, 4);
                v_env_3684_ = lean_ctor_get(v___x_3682_, 0);
                v_nextMacroScope_3685_ = lean_ctor_get(v___x_3682_, 1);
                v_ngen_3686_ = lean_ctor_get(v___x_3682_, 2);
                v_auxDeclNGen_3687_ = lean_ctor_get(v___x_3682_, 3);
                v_cache_3688_ = lean_ctor_get(v___x_3682_, 5);
                v_messages_3689_ = lean_ctor_get(v___x_3682_, 6);
                v_infoState_3690_ = lean_ctor_get(v___x_3682_, 7);
                v_snapshotTasks_3691_ = lean_ctor_get(v___x_3682_, 8);
                v_isSharedCheck_3714_ = (!lean_is_exclusive(v___x_3682_)) as u8;
                if v_isSharedCheck_3714_ == 0 {
                    v___x_3693_ = v___x_3682_;
                    v_isShared_3694_ = v_isSharedCheck_3714_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_3691_);
                    lean_inc(v_infoState_3690_);
                    lean_inc(v_messages_3689_);
                    lean_inc(v_cache_3688_);
                    lean_inc(v_traceState_3683_);
                    lean_inc(v_auxDeclNGen_3687_);
                    lean_inc(v_ngen_3686_);
                    lean_inc(v_nextMacroScope_3685_);
                    lean_inc(v_env_3684_);
                    lean_dec(v___x_3682_);
                    v___x_3693_ = lean_box(0);
                    v_isShared_3694_ = v_isSharedCheck_3714_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_3695_ = lean_ctor_get_uint64(
                    v_traceState_3683_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_3712_ = (!lean_is_exclusive(v_traceState_3683_)) as u8;
                if v_isSharedCheck_3712_ == 0 {
                    v_unused_3713_ = lean_ctor_get(v_traceState_3683_, 0);
                    lean_dec(v_unused_3713_);
                    v___x_3697_ = v_traceState_3683_;
                    v_isShared_3698_ = v_isSharedCheck_3712_;
                    state = 3;
                    continue;
                } else {
                    lean_dec(v_traceState_3683_);
                    v___x_3697_ = lean_box(0);
                    v_isShared_3698_ = v_isSharedCheck_3712_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3699_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3699_, 0, v_ref_3644_);
                lean_ctor_set(v___x_3699_, 1, v_a_3678_);
                v___x_3700_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_3642_, v___x_3699_);
                if v_isShared_3698_ == 0 {
                    lean_ctor_set(v___x_3697_, 0, v___x_3700_);
                    v___x_3702_ = v___x_3697_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3711_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3711_, 0, v___x_3700_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_3711_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_3695_,
                    );
                    v___x_3702_ = v_reuseFailAlloc_3711_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3694_ == 0 {
                    lean_ctor_set(v___x_3693_, 4, v___x_3702_);
                    v___x_3704_ = v___x_3693_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3710_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3710_, 0, v_env_3684_);
                    lean_ctor_set(v_reuseFailAlloc_3710_, 1, v_nextMacroScope_3685_);
                    lean_ctor_set(v_reuseFailAlloc_3710_, 2, v_ngen_3686_);
                    lean_ctor_set(v_reuseFailAlloc_3710_, 3, v_auxDeclNGen_3687_);
                    lean_ctor_set(v_reuseFailAlloc_3710_, 4, v___x_3702_);
                    lean_ctor_set(v_reuseFailAlloc_3710_, 5, v_cache_3688_);
                    lean_ctor_set(v_reuseFailAlloc_3710_, 6, v_messages_3689_);
                    lean_ctor_set(v_reuseFailAlloc_3710_, 7, v_infoState_3690_);
                    lean_ctor_set(v_reuseFailAlloc_3710_, 8, v_snapshotTasks_3691_);
                    v___x_3704_ = v_reuseFailAlloc_3710_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3705_ = lean_st_ref_set(v___y_3649_, v___x_3704_);
                v___x_3706_ = lean_box(0);
                if v_isShared_3681_ == 0 {
                    lean_ctor_set(v___x_3680_, 0, v___x_3706_);
                    v___x_3708_ = v___x_3680_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3709_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3709_, 0, v___x_3706_);
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
    mut v_oldTraces_3716_: *mut LeanObject,
    mut v_data_3717_: *mut LeanObject,
    mut v_ref_3718_: *mut LeanObject,
    mut v_msg_3719_: *mut LeanObject,
    mut v___y_3720_: *mut LeanObject,
    mut v___y_3721_: *mut LeanObject,
    mut v___y_3722_: *mut LeanObject,
    mut v___y_3723_: *mut LeanObject,
    mut v___y_3724_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3725_: *mut LeanObject = core::ptr::null_mut();
    v_res_3725_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__2(v_oldTraces_3716_, v_data_3717_, v_ref_3718_, v_msg_3719_, v___y_3720_, v___y_3721_, v___y_3722_, v___y_3723_);
    lean_dec(v___y_3723_);
    lean_dec_ref(v___y_3722_);
    lean_dec(v___y_3721_);
    lean_dec_ref(v___y_3720_);
    return v_res_3725_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__3___redArg(
    mut v_x_3726_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3731_: u8 = 0;
    let mut v___x_3733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3735_: u8 = 0;
    let mut v_a_3736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3739_: u8 = 0;
    let mut v___x_3741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3743_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3726_) == 0 {
                    v_a_3728_ = lean_ctor_get(v_x_3726_, 0);
                    v_isSharedCheck_3735_ = (!lean_is_exclusive(v_x_3726_)) as u8;
                    if v_isSharedCheck_3735_ == 0 {
                        v___x_3730_ = v_x_3726_;
                        v_isShared_3731_ = v_isSharedCheck_3735_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3728_);
                        lean_dec(v_x_3726_);
                        v___x_3730_ = lean_box(0);
                        v_isShared_3731_ = v_isSharedCheck_3735_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3736_ = lean_ctor_get(v_x_3726_, 0);
                    v_isSharedCheck_3743_ = (!lean_is_exclusive(v_x_3726_)) as u8;
                    if v_isSharedCheck_3743_ == 0 {
                        v___x_3738_ = v_x_3726_;
                        v_isShared_3739_ = v_isSharedCheck_3743_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3736_);
                        lean_dec(v_x_3726_);
                        v___x_3738_ = lean_box(0);
                        v_isShared_3739_ = v_isSharedCheck_3743_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3731_ == 0 {
                    lean_ctor_set_tag(v___x_3730_, 1);
                    v___x_3733_ = v___x_3730_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3734_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3734_, 0, v_a_3728_);
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
                    lean_ctor_set_tag(v___x_3738_, 0);
                    v___x_3741_ = v___x_3738_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3742_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3742_, 0, v_a_3736_);
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
    mut v_x_3744_: *mut LeanObject,
    mut v___y_3745_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3746_: *mut LeanObject = core::ptr::null_mut();
    v_res_3746_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__3___redArg(v_x_3744_);
    return v_res_3746_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(
    mut v_cls_3747_: *mut LeanObject,
    mut v_collapsed_3748_: u8,
    mut v_tag_3749_: *mut LeanObject,
    mut v_opts_3750_: *mut LeanObject,
    mut v_clsEnabled_3751_: u8,
    mut v_oldTraces_3752_: *mut LeanObject,
    mut v_msg_3753_: *mut LeanObject,
    mut v_resStartStop_3754_: *mut LeanObject,
    mut v___y_3755_: *mut LeanObject,
    mut v___y_3756_: *mut LeanObject,
    mut v___y_3757_: *mut LeanObject,
    mut v___y_3758_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_3760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3764_: u8 = 0;
    let mut v___y_3766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_3768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3774_: u8 = 0;
    let mut v___x_3776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3778_: u8 = 0;
    let mut v_fst_3779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3783_: u8 = 0;
    let mut v___x_3784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3785_: u8 = 0;
    let mut v___y_3787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_result_3789_: u8 = 0;
    let mut v___x_3790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_m_3796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3799_: f64 = 0.0;
    let mut v_data_3800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_3801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3802_: f64 = 0.0;
    let mut v___x_3803_: f64 = 0.0;
    let mut v_reuseFailAlloc_3804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3812_: u8 = 0;
    let mut v___x_3813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_3814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_3817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_3819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_3820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_3821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3825_: u8 = 0;
    let mut v_tid_3826_: u64 = 0;
    let mut v_traces_3827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3830_: u8 = 0;
    let mut v___x_3831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3840_: u8 = 0;
    let mut v_isSharedCheck_3841_: u8 = 0;
    let mut v___y_3843_: f64 = 0.0;
    let mut v___x_3844_: f64 = 0.0;
    let mut v___x_3845_: f64 = 0.0;
    let mut v___x_3846_: f64 = 0.0;
    let mut v___x_3847_: u8 = 0;
    let mut v___x_3848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3849_: u8 = 0;
    let mut v___x_3850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3852_: f64 = 0.0;
    let mut v___x_3853_: f64 = 0.0;
    let mut v___x_3854_: f64 = 0.0;
    let mut v___x_3855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3857_: f64 = 0.0;
    let mut v_isSharedCheck_3858_: u8 = 0;
    let mut v_isSharedCheck_3859_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_3760_ = lean_ctor_get(v_resStartStop_3754_, 0);
                v_snd_3761_ = lean_ctor_get(v_resStartStop_3754_, 1);
                v_isSharedCheck_3859_ = (!lean_is_exclusive(v_resStartStop_3754_)) as u8;
                if v_isSharedCheck_3859_ == 0 {
                    v___x_3763_ = v_resStartStop_3754_;
                    v_isShared_3764_ = v_isSharedCheck_3859_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_3761_);
                    lean_inc(v_fst_3760_);
                    lean_dec(v_resStartStop_3754_);
                    v___x_3763_ = lean_box(0);
                    v_isShared_3764_ = v_isSharedCheck_3859_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_3779_ = lean_ctor_get(v_snd_3761_, 0);
                v_snd_3780_ = lean_ctor_get(v_snd_3761_, 1);
                v_isSharedCheck_3858_ = (!lean_is_exclusive(v_snd_3761_)) as u8;
                if v_isSharedCheck_3858_ == 0 {
                    v___x_3782_ = v_snd_3761_;
                    v_isShared_3783_ = v_isSharedCheck_3858_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_snd_3780_);
                    lean_inc(v_fst_3779_);
                    lean_dec(v_snd_3761_);
                    v___x_3782_ = lean_box(0);
                    v_isShared_3783_ = v_isSharedCheck_3858_;
                    state = 5;
                    continue;
                }
            }
            2 => {
                lean_inc(v___y_3766_);
                v___x_3769_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__2(v_oldTraces_3752_, v_data_3768_, v___y_3766_, v___y_3767_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_);
                if lean_obj_tag(v___x_3769_) == 0 {
                    lean_dec_ref_known(v___x_3769_, 1);
                    v___x_3770_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__3___redArg(v_fst_3760_);
                    return v___x_3770_;
                } else {
                    lean_dec(v_fst_3760_);
                    v_a_3771_ = lean_ctor_get(v___x_3769_, 0);
                    v_isSharedCheck_3778_ = (!lean_is_exclusive(v___x_3769_)) as u8;
                    if v_isSharedCheck_3778_ == 0 {
                        v___x_3773_ = v___x_3769_;
                        v_isShared_3774_ = v_isSharedCheck_3778_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3771_);
                        lean_dec(v___x_3769_);
                        v___x_3773_ = lean_box(0);
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
                    v_reuseFailAlloc_3777_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3777_, 0, v_a_3771_);
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
                        v___x_3853_ = lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__4_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__4);
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
                v___x_3792_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__1_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__1);
                if v_isShared_3783_ == 0 {
                    lean_ctor_set_tag(v___x_3782_, 7);
                    lean_ctor_set(v___x_3782_, 1, v___x_3792_);
                    lean_ctor_set(v___x_3782_, 0, v___x_3791_);
                    v___x_3794_ = v___x_3782_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3805_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3805_, 0, v___x_3791_);
                    lean_ctor_set(v_reuseFailAlloc_3805_, 1, v___x_3792_);
                    v___x_3794_ = v_reuseFailAlloc_3805_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_3764_ == 0 {
                    lean_ctor_set_tag(v___x_3763_, 7);
                    lean_ctor_set(v___x_3763_, 1, v_a_3788_);
                    lean_ctor_set(v___x_3763_, 0, v___x_3794_);
                    v_m_3796_ = v___x_3763_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3804_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3804_, 0, v___x_3794_);
                    lean_ctor_set(v_reuseFailAlloc_3804_, 1, v_a_3788_);
                    v_m_3796_ = v_reuseFailAlloc_3804_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_3797_ = lean_box((v_result_3789_) as usize);
                v___x_3798_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3798_, 0, v___x_3797_);
                v___x_3799_ = lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__0_once), _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__0);
                lean_inc_ref(v_tag_3749_);
                lean_inc_ref(v___x_3798_);
                lean_inc(v_cls_3747_);
                v_data_3800_ = lean_alloc_ctor(0, 3, (17) as u32);
                lean_ctor_set(v_data_3800_, 0, v_cls_3747_);
                lean_ctor_set(v_data_3800_, 1, v___x_3798_);
                lean_ctor_set(v_data_3800_, 2, v_tag_3749_);
                lean_ctor_set_float(
                    v_data_3800_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_3799_,
                );
                lean_ctor_set_float(
                    v_data_3800_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    v___x_3799_,
                );
                lean_ctor_set_uint8(
                    v_data_3800_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                    v_collapsed_3748_,
                );
                if v___x_3785_ == 0 {
                    lean_dec_ref_known(v___x_3798_, 1);
                    lean_dec(v_snd_3780_);
                    lean_dec(v_fst_3779_);
                    lean_dec_ref(v_tag_3749_);
                    lean_dec(v_cls_3747_);
                    v___y_3766_ = v___y_3787_;
                    v___y_3767_ = v_m_3796_;
                    v_data_3768_ = v_data_3800_;
                    state = 2;
                    continue;
                } else {
                    lean_dec_ref_known(v_data_3800_, 3);
                    v_data_3801_ = lean_alloc_ctor(0, 3, (17) as u32);
                    lean_ctor_set(v_data_3801_, 0, v_cls_3747_);
                    lean_ctor_set(v_data_3801_, 1, v___x_3798_);
                    lean_ctor_set(v_data_3801_, 2, v_tag_3749_);
                    v___x_3802_ = lean_unbox_float(v_fst_3779_);
                    lean_dec(v_fst_3779_);
                    lean_ctor_set_float(
                        v_data_3801_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v___x_3802_,
                    );
                    v___x_3803_ = lean_unbox_float(v_snd_3780_);
                    lean_dec(v_snd_3780_);
                    lean_ctor_set_float(
                        v_data_3801_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                        v___x_3803_,
                    );
                    lean_ctor_set_uint8(
                        v_data_3801_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
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
                v_ref_3807_ = lean_ctor_get(v___y_3757_, 5);
                lean_inc(v___y_3758_);
                lean_inc_ref(v___y_3757_);
                lean_inc(v___y_3756_);
                lean_inc_ref(v___y_3755_);
                lean_inc(v_fst_3760_);
                v___x_3808_ = lean_apply_6(
                    v_msg_3753_,
                    v_fst_3760_,
                    v___y_3755_,
                    v___y_3756_,
                    v___y_3757_,
                    v___y_3758_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_3808_) == 0 {
                    v_a_3809_ = lean_ctor_get(v___x_3808_, 0);
                    lean_inc(v_a_3809_);
                    lean_dec_ref_known(v___x_3808_, 1);
                    v___y_3787_ = v_ref_3807_;
                    v_a_3788_ = v_a_3809_;
                    state = 6;
                    continue;
                } else {
                    lean_dec_ref_known(v___x_3808_, 1);
                    v___x_3810_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__3_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__3);
                    v___y_3787_ = v_ref_3807_;
                    v_a_3788_ = v___x_3810_;
                    state = 6;
                    continue;
                }
            }
            10 => {
                if v_clsEnabled_3751_ == 0 {
                    if v___y_3812_ == 0 {
                        lean_del_object(v___x_3782_);
                        lean_dec(v_snd_3780_);
                        lean_dec(v_fst_3779_);
                        lean_del_object(v___x_3763_);
                        lean_dec_ref(v_msg_3753_);
                        lean_dec_ref(v_tag_3749_);
                        lean_dec(v_cls_3747_);
                        v___x_3813_ = lean_st_ref_take(v___y_3758_);
                        v_traceState_3814_ = lean_ctor_get(v___x_3813_, 4);
                        v_env_3815_ = lean_ctor_get(v___x_3813_, 0);
                        v_nextMacroScope_3816_ = lean_ctor_get(v___x_3813_, 1);
                        v_ngen_3817_ = lean_ctor_get(v___x_3813_, 2);
                        v_auxDeclNGen_3818_ = lean_ctor_get(v___x_3813_, 3);
                        v_cache_3819_ = lean_ctor_get(v___x_3813_, 5);
                        v_messages_3820_ = lean_ctor_get(v___x_3813_, 6);
                        v_infoState_3821_ = lean_ctor_get(v___x_3813_, 7);
                        v_snapshotTasks_3822_ = lean_ctor_get(v___x_3813_, 8);
                        v_isSharedCheck_3841_ = (!lean_is_exclusive(v___x_3813_)) as u8;
                        if v_isSharedCheck_3841_ == 0 {
                            v___x_3824_ = v___x_3813_;
                            v_isShared_3825_ = v_isSharedCheck_3841_;
                            state = 11;
                            continue;
                        } else {
                            lean_inc(v_snapshotTasks_3822_);
                            lean_inc(v_infoState_3821_);
                            lean_inc(v_messages_3820_);
                            lean_inc(v_cache_3819_);
                            lean_inc(v_traceState_3814_);
                            lean_inc(v_auxDeclNGen_3818_);
                            lean_inc(v_ngen_3817_);
                            lean_inc(v_nextMacroScope_3816_);
                            lean_inc(v_env_3815_);
                            lean_dec(v___x_3813_);
                            v___x_3824_ = lean_box(0);
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
                v_tid_3826_ = lean_ctor_get_uint64(
                    v_traceState_3814_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_traces_3827_ = lean_ctor_get(v_traceState_3814_, 0);
                v_isSharedCheck_3840_ = (!lean_is_exclusive(v_traceState_3814_)) as u8;
                if v_isSharedCheck_3840_ == 0 {
                    v___x_3829_ = v_traceState_3814_;
                    v_isShared_3830_ = v_isSharedCheck_3840_;
                    state = 12;
                    continue;
                } else {
                    lean_inc(v_traces_3827_);
                    lean_dec(v_traceState_3814_);
                    v___x_3829_ = lean_box(0);
                    v_isShared_3830_ = v_isSharedCheck_3840_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_3831_ =
                    l_Lean_PersistentArray_append___redArg(v_oldTraces_3752_, v_traces_3827_);
                lean_dec_ref(v_traces_3827_);
                if v_isShared_3830_ == 0 {
                    lean_ctor_set(v___x_3829_, 0, v___x_3831_);
                    v___x_3833_ = v___x_3829_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3839_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3839_, 0, v___x_3831_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_3839_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_3826_,
                    );
                    v___x_3833_ = v_reuseFailAlloc_3839_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_3825_ == 0 {
                    lean_ctor_set(v___x_3824_, 4, v___x_3833_);
                    v___x_3835_ = v___x_3824_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3838_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3838_, 0, v_env_3815_);
                    lean_ctor_set(v_reuseFailAlloc_3838_, 1, v_nextMacroScope_3816_);
                    lean_ctor_set(v_reuseFailAlloc_3838_, 2, v_ngen_3817_);
                    lean_ctor_set(v_reuseFailAlloc_3838_, 3, v_auxDeclNGen_3818_);
                    lean_ctor_set(v_reuseFailAlloc_3838_, 4, v___x_3833_);
                    lean_ctor_set(v_reuseFailAlloc_3838_, 5, v_cache_3819_);
                    lean_ctor_set(v_reuseFailAlloc_3838_, 6, v_messages_3820_);
                    lean_ctor_set(v_reuseFailAlloc_3838_, 7, v_infoState_3821_);
                    lean_ctor_set(v_reuseFailAlloc_3838_, 8, v_snapshotTasks_3822_);
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
                v___x_3844_ = lean_unbox_float(v_snd_3780_);
                v___x_3845_ = lean_unbox_float(v_fst_3779_);
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
    mut v_cls_3860_: *mut LeanObject,
    mut v_collapsed_3861_: *mut LeanObject,
    mut v_tag_3862_: *mut LeanObject,
    mut v_opts_3863_: *mut LeanObject,
    mut v_clsEnabled_3864_: *mut LeanObject,
    mut v_oldTraces_3865_: *mut LeanObject,
    mut v_msg_3866_: *mut LeanObject,
    mut v_resStartStop_3867_: *mut LeanObject,
    mut v___y_3868_: *mut LeanObject,
    mut v___y_3869_: *mut LeanObject,
    mut v___y_3870_: *mut LeanObject,
    mut v___y_3871_: *mut LeanObject,
    mut v___y_3872_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_collapsed_boxed_3873_: u8 = 0;
    let mut v_clsEnabled_boxed_3874_: u8 = 0;
    let mut v_res_3875_: *mut LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_3873_ = (lean_unbox(v_collapsed_3861_) as u8);
    v_clsEnabled_boxed_3874_ = (lean_unbox(v_clsEnabled_3864_) as u8);
    v_res_3875_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_3860_, v_collapsed_boxed_3873_, v_tag_3862_, v_opts_3863_, v_clsEnabled_boxed_3874_, v_oldTraces_3865_, v_msg_3866_, v_resStartStop_3867_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_);
    lean_dec(v___y_3871_);
    lean_dec_ref(v___y_3870_);
    lean_dec(v___y_3869_);
    lean_dec_ref(v___y_3868_);
    lean_dec_ref(v_opts_3863_);
    return v_res_3875_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__1()
-> *mut LeanObject {
    let mut v___x_3877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3879_: *mut LeanObject = core::ptr::null_mut();
    v___x_3877_ = lean_box(0);
    v___x_3878_ = lean_unsigned_to_nat(16);
    v___x_3879_ = lean_mk_array(v___x_3878_, v___x_3877_);
    return v___x_3879_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__2()
-> *mut LeanObject {
    let mut v___x_3880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut LeanObject = core::ptr::null_mut();
    v___x_3880_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__1_once),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__1,
    );
    v___x_3881_ = lean_unsigned_to_nat(0);
    v___x_3882_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3882_, 0, v___x_3881_);
    lean_ctor_set(v___x_3882_, 1, v___x_3880_);
    return v___x_3882_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__3()
-> *mut LeanObject {
    let mut v___x_3883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3884_: *mut LeanObject = core::ptr::null_mut();
    v___x_3883_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__2_once),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__2,
    );
    v___x_3884_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_3884_, 0, v___x_3883_);
    lean_ctor_set(v___x_3884_, 1, v___x_3883_);
    lean_ctor_set(v___x_3884_, 2, v___x_3883_);
    lean_ctor_set(v___x_3884_, 3, v___x_3883_);
    return v___x_3884_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(
    mut v_g_3886_: *mut LeanObject,
    mut v_cfg_3887_: *mut LeanObject,
    mut v_a_3888_: *mut LeanObject,
    mut v_a_3889_: *mut LeanObject,
    mut v_a_3890_: *mut LeanObject,
    mut v_a_3891_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_options_3893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3894_: u8 = 0;
    let mut v___x_3895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3915_: u8 = 0;
    let mut v___x_3916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3920_: u8 = 0;
    let mut v_a_3921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3924_: u8 = 0;
    let mut v___x_3926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3928_: u8 = 0;
    let mut v_inheritedTraceOptions_3929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: u8 = 0;
    let mut v___y_3936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3940_: f64 = 0.0;
    let mut v___x_3941_: f64 = 0.0;
    let mut v___x_3942_: f64 = 0.0;
    let mut v___x_3943_: f64 = 0.0;
    let mut v___x_3944_: f64 = 0.0;
    let mut v___x_3945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: f64 = 0.0;
    let mut v___x_3966_: f64 = 0.0;
    let mut v___x_3967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3986_: u8 = 0;
    let mut v___x_3987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4034_: u8 = 0;
    let mut v___x_4035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4055_: u8 = 0;
    let mut v___x_4056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4060_: u8 = 0;
    let mut v_a_4061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4064_: u8 = 0;
    let mut v___x_4066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4068_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_3893_ = lean_ctor_get(v_a_3890_, 2);
                v_hasTrace_3894_ = lean_ctor_get_uint8(
                    v_options_3893_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                if v_hasTrace_3894_ == 0 {
                    v___x_3895_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__0;
                    lean_inc(v_g_3886_);
                    v___x_3896_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg(v_g_3886_, v___x_3895_, v_a_3888_, v_a_3889_, v_a_3890_, v_a_3891_);
                    if lean_obj_tag(v___x_3896_) == 0 {
                        v_a_3897_ = lean_ctor_get(v___x_3896_, 0);
                        lean_inc(v_a_3897_);
                        lean_dec_ref_known(v___x_3896_, 1);
                        v___x_3898_ = lean_array_get_size(v_a_3897_);
                        lean_dec(v_a_3897_);
                        v___x_3899_ = lean_unsigned_to_nat(0);
                        v___x_3900_ = lean_unsigned_to_nat(4);
                        v___x_3901_ = lean_nat_mul(v___x_3898_, v___x_3900_);
                        v___x_3902_ = lean_unsigned_to_nat(3);
                        v___x_3903_ = lean_nat_div(v___x_3901_, v___x_3902_);
                        lean_dec(v___x_3901_);
                        v___x_3904_ = l_Nat_nextPowerOfTwo(v___x_3903_);
                        lean_dec(v___x_3903_);
                        v___x_3905_ = lean_box(0);
                        v___x_3906_ = lean_mk_array(v___x_3904_, v___x_3905_);
                        v___x_3907_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_3907_, 0, v___x_3899_);
                        lean_ctor_set(v___x_3907_, 1, v___x_3906_);
                        v___x_3908_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__3_once
                            ),
                            _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__3,
                        );
                        lean_inc_ref(v___x_3907_);
                        v___x_3909_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v___x_3909_, 0, v___x_3907_);
                        lean_ctor_set(v___x_3909_, 1, v___x_3907_);
                        lean_ctor_set(v___x_3909_, 2, v___x_3908_);
                        v___x_3910_ = lean_st_mk_ref(v___x_3909_);
                        v___x_3911_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go(v_g_3886_, v_cfg_3887_, v___x_3910_, v_a_3888_, v_a_3889_, v_a_3890_, v_a_3891_);
                        if lean_obj_tag(v___x_3911_) == 0 {
                            v_a_3912_ = lean_ctor_get(v___x_3911_, 0);
                            v_isSharedCheck_3920_ = (!lean_is_exclusive(v___x_3911_)) as u8;
                            if v_isSharedCheck_3920_ == 0 {
                                v___x_3914_ = v___x_3911_;
                                v_isShared_3915_ = v_isSharedCheck_3920_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_3912_);
                                lean_dec(v___x_3911_);
                                v___x_3914_ = lean_box(0);
                                v_isShared_3915_ = v_isSharedCheck_3920_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v___x_3910_);
                            return v___x_3911_;
                        }
                    } else {
                        lean_dec(v_g_3886_);
                        v_a_3921_ = lean_ctor_get(v___x_3896_, 0);
                        v_isSharedCheck_3928_ = (!lean_is_exclusive(v___x_3896_)) as u8;
                        if v_isSharedCheck_3928_ == 0 {
                            v___x_3923_ = v___x_3896_;
                            v_isShared_3924_ = v_isSharedCheck_3928_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_3921_);
                            lean_dec(v___x_3896_);
                            v___x_3923_ = lean_box(0);
                            v_isShared_3924_ = v_isSharedCheck_3928_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_inheritedTraceOptions_3929_ = lean_ctor_get(v_a_3890_, 13);
                    v___f_3930_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__4;
                    v___x_3931_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__3;
                    v___x_3932_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__1;
                    v___x_3933_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7);
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
                            lean_inc(v_g_3886_);
                            v___x_4036_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg(v_g_3886_, v___x_4035_, v_a_3888_, v_a_3889_, v_a_3890_, v_a_3891_);
                            if lean_obj_tag(v___x_4036_) == 0 {
                                v_a_4037_ = lean_ctor_get(v___x_4036_, 0);
                                lean_inc(v_a_4037_);
                                lean_dec_ref_known(v___x_4036_, 1);
                                v___x_4038_ = lean_array_get_size(v_a_4037_);
                                lean_dec(v_a_4037_);
                                v___x_4039_ = lean_unsigned_to_nat(0);
                                v___x_4040_ = lean_unsigned_to_nat(4);
                                v___x_4041_ = lean_nat_mul(v___x_4038_, v___x_4040_);
                                v___x_4042_ = lean_unsigned_to_nat(3);
                                v___x_4043_ = lean_nat_div(v___x_4041_, v___x_4042_);
                                lean_dec(v___x_4041_);
                                v___x_4044_ = l_Nat_nextPowerOfTwo(v___x_4043_);
                                lean_dec(v___x_4043_);
                                v___x_4045_ = lean_box(0);
                                v___x_4046_ = lean_mk_array(v___x_4044_, v___x_4045_);
                                v___x_4047_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v___x_4047_, 0, v___x_4039_);
                                lean_ctor_set(v___x_4047_, 1, v___x_4046_);
                                v___x_4048_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__3), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__3_once), _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__3);
                                lean_inc_ref(v___x_4047_);
                                v___x_4049_ = lean_alloc_ctor(0, 3, (0) as u32);
                                lean_ctor_set(v___x_4049_, 0, v___x_4047_);
                                lean_ctor_set(v___x_4049_, 1, v___x_4047_);
                                lean_ctor_set(v___x_4049_, 2, v___x_4048_);
                                v___x_4050_ = lean_st_mk_ref(v___x_4049_);
                                v___x_4051_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go(v_g_3886_, v_cfg_3887_, v___x_4050_, v_a_3888_, v_a_3889_, v_a_3890_, v_a_3891_);
                                if lean_obj_tag(v___x_4051_) == 0 {
                                    v_a_4052_ = lean_ctor_get(v___x_4051_, 0);
                                    v_isSharedCheck_4060_ = (!lean_is_exclusive(v___x_4051_)) as u8;
                                    if v_isSharedCheck_4060_ == 0 {
                                        v___x_4054_ = v___x_4051_;
                                        v_isShared_4055_ = v_isSharedCheck_4060_;
                                        state = 12;
                                        continue;
                                    } else {
                                        lean_inc(v_a_4052_);
                                        lean_dec(v___x_4051_);
                                        v___x_4054_ = lean_box(0);
                                        v_isShared_4055_ = v_isSharedCheck_4060_;
                                        state = 12;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v___x_4050_);
                                    return v___x_4051_;
                                }
                            } else {
                                lean_dec(v_g_3886_);
                                v_a_4061_ = lean_ctor_get(v___x_4036_, 0);
                                v_isSharedCheck_4068_ = (!lean_is_exclusive(v___x_4036_)) as u8;
                                if v_isSharedCheck_4068_ == 0 {
                                    v___x_4063_ = v___x_4036_;
                                    v_isShared_4064_ = v_isSharedCheck_4068_;
                                    state = 14;
                                    continue;
                                } else {
                                    lean_inc(v_a_4061_);
                                    lean_dec(v___x_4036_);
                                    v___x_4063_ = lean_box(0);
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
                lean_dec(v___x_3910_);
                lean_dec(v___x_3916_);
                if v_isShared_3915_ == 0 {
                    v___x_3918_ = v___x_3914_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3919_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3919_, 0, v_a_3912_);
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
                    v_reuseFailAlloc_3927_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3927_, 0, v_a_3921_);
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
                v___x_3941_ = lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__4_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__4);
                v___x_3942_ = lean_float_div(v___x_3940_, v___x_3941_);
                v___x_3943_ = lean_float_of_nat(v___x_3939_);
                v___x_3944_ = lean_float_div(v___x_3943_, v___x_3941_);
                v___x_3945_ = lean_box_float(v___x_3942_);
                v___x_3946_ = lean_box_float(v___x_3944_);
                v___x_3947_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3947_, 0, v___x_3945_);
                lean_ctor_set(v___x_3947_, 1, v___x_3946_);
                v___x_3948_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3948_, 0, v_a_3938_);
                lean_ctor_set(v___x_3948_, 1, v___x_3947_);
                v___x_3949_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v___x_3931_, v_hasTrace_3894_, v___x_3932_, v_options_3893_, v___x_3934_, v___y_3936_, v___f_3930_, v___x_3948_, v_a_3888_, v_a_3889_, v_a_3890_, v_a_3891_);
                return v___x_3949_;
            }
            6 => {
                v___x_3954_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3954_, 0, v_a_3953_);
                v___y_3936_ = v___y_3951_;
                v___y_3937_ = v___y_3952_;
                v_a_3938_ = v___x_3954_;
                state = 5;
                continue;
            }
            7 => {
                v___x_3959_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3959_, 0, v_a_3958_);
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
                v___x_3967_ = lean_box_float(v___x_3965_);
                v___x_3968_ = lean_box_float(v___x_3966_);
                v___x_3969_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3969_, 0, v___x_3967_);
                lean_ctor_set(v___x_3969_, 1, v___x_3968_);
                v___x_3970_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3970_, 0, v_a_3963_);
                lean_ctor_set(v___x_3970_, 1, v___x_3969_);
                v___x_3971_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v___x_3931_, v_hasTrace_3894_, v___x_3932_, v_options_3893_, v___x_3934_, v___y_3962_, v___f_3930_, v___x_3970_, v_a_3888_, v_a_3889_, v_a_3890_, v_a_3891_);
                return v___x_3971_;
            }
            9 => {
                v___x_3976_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3976_, 0, v_a_3975_);
                v___y_3961_ = v___y_3973_;
                v___y_3962_ = v___y_3974_;
                v_a_3963_ = v___x_3976_;
                state = 8;
                continue;
            }
            10 => {
                v___x_3981_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3981_, 0, v_a_3980_);
                v___y_3961_ = v___y_3978_;
                v___y_3962_ = v___y_3979_;
                v_a_3963_ = v___x_3981_;
                state = 8;
                continue;
            }
            11 => {
                v___x_3983_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1___redArg(v_a_3891_);
                v_a_3984_ = lean_ctor_get(v___x_3983_, 0);
                lean_inc(v_a_3984_);
                lean_dec_ref(v___x_3983_);
                v___x_3985_ = l_Lean_trace_profiler_useHeartbeats;
                v___x_3986_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__1(v_options_3893_, v___x_3985_);
                if v___x_3986_ == 0 {
                    v___x_3987_ = lean_io_mono_nanos_now();
                    v___x_3988_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__0;
                    lean_inc(v_g_3886_);
                    v___x_3989_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg(v_g_3886_, v___x_3988_, v_a_3888_, v_a_3889_, v_a_3890_, v_a_3891_);
                    if lean_obj_tag(v___x_3989_) == 0 {
                        v_a_3990_ = lean_ctor_get(v___x_3989_, 0);
                        lean_inc(v_a_3990_);
                        lean_dec_ref_known(v___x_3989_, 1);
                        v___x_3991_ = lean_array_get_size(v_a_3990_);
                        lean_dec(v_a_3990_);
                        v___x_3992_ = lean_unsigned_to_nat(0);
                        v___x_3993_ = lean_unsigned_to_nat(4);
                        v___x_3994_ = lean_nat_mul(v___x_3991_, v___x_3993_);
                        v___x_3995_ = lean_unsigned_to_nat(3);
                        v___x_3996_ = lean_nat_div(v___x_3994_, v___x_3995_);
                        lean_dec(v___x_3994_);
                        v___x_3997_ = l_Nat_nextPowerOfTwo(v___x_3996_);
                        lean_dec(v___x_3996_);
                        v___x_3998_ = lean_box(0);
                        v___x_3999_ = lean_mk_array(v___x_3997_, v___x_3998_);
                        v___x_4000_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_4000_, 0, v___x_3992_);
                        lean_ctor_set(v___x_4000_, 1, v___x_3999_);
                        v___x_4001_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__3_once
                            ),
                            _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__3,
                        );
                        lean_inc_ref(v___x_4000_);
                        v___x_4002_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v___x_4002_, 0, v___x_4000_);
                        lean_ctor_set(v___x_4002_, 1, v___x_4000_);
                        lean_ctor_set(v___x_4002_, 2, v___x_4001_);
                        v___x_4003_ = lean_st_mk_ref(v___x_4002_);
                        v___x_4004_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go(v_g_3886_, v_cfg_3887_, v___x_4003_, v_a_3888_, v_a_3889_, v_a_3890_, v_a_3891_);
                        if lean_obj_tag(v___x_4004_) == 0 {
                            v_a_4005_ = lean_ctor_get(v___x_4004_, 0);
                            lean_inc(v_a_4005_);
                            lean_dec_ref_known(v___x_4004_, 1);
                            v___x_4006_ = lean_st_ref_get(v___x_4003_);
                            lean_dec(v___x_4003_);
                            lean_dec(v___x_4006_);
                            v___y_3956_ = v_a_3984_;
                            v___y_3957_ = v___x_3987_;
                            v_a_3958_ = v_a_4005_;
                            state = 7;
                            continue;
                        } else {
                            lean_dec(v___x_4003_);
                            if lean_obj_tag(v___x_4004_) == 0 {
                                v_a_4007_ = lean_ctor_get(v___x_4004_, 0);
                                lean_inc(v_a_4007_);
                                lean_dec_ref_known(v___x_4004_, 1);
                                v___y_3956_ = v_a_3984_;
                                v___y_3957_ = v___x_3987_;
                                v_a_3958_ = v_a_4007_;
                                state = 7;
                                continue;
                            } else {
                                v_a_4008_ = lean_ctor_get(v___x_4004_, 0);
                                lean_inc(v_a_4008_);
                                lean_dec_ref_known(v___x_4004_, 1);
                                v___y_3951_ = v_a_3984_;
                                v___y_3952_ = v___x_3987_;
                                v_a_3953_ = v_a_4008_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_g_3886_);
                        v_a_4009_ = lean_ctor_get(v___x_3989_, 0);
                        lean_inc(v_a_4009_);
                        lean_dec_ref_known(v___x_3989_, 1);
                        v___y_3951_ = v_a_3984_;
                        v___y_3952_ = v___x_3987_;
                        v_a_3953_ = v_a_4009_;
                        state = 6;
                        continue;
                    }
                } else {
                    v___x_4010_ = lean_io_get_num_heartbeats();
                    v___x_4011_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__0;
                    lean_inc(v_g_3886_);
                    v___x_4012_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg(v_g_3886_, v___x_4011_, v_a_3888_, v_a_3889_, v_a_3890_, v_a_3891_);
                    if lean_obj_tag(v___x_4012_) == 0 {
                        v_a_4013_ = lean_ctor_get(v___x_4012_, 0);
                        lean_inc(v_a_4013_);
                        lean_dec_ref_known(v___x_4012_, 1);
                        v___x_4014_ = lean_array_get_size(v_a_4013_);
                        lean_dec(v_a_4013_);
                        v___x_4015_ = lean_unsigned_to_nat(0);
                        v___x_4016_ = lean_unsigned_to_nat(4);
                        v___x_4017_ = lean_nat_mul(v___x_4014_, v___x_4016_);
                        v___x_4018_ = lean_unsigned_to_nat(3);
                        v___x_4019_ = lean_nat_div(v___x_4017_, v___x_4018_);
                        lean_dec(v___x_4017_);
                        v___x_4020_ = l_Nat_nextPowerOfTwo(v___x_4019_);
                        lean_dec(v___x_4019_);
                        v___x_4021_ = lean_box(0);
                        v___x_4022_ = lean_mk_array(v___x_4020_, v___x_4021_);
                        v___x_4023_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_4023_, 0, v___x_4015_);
                        lean_ctor_set(v___x_4023_, 1, v___x_4022_);
                        v___x_4024_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__3_once
                            ),
                            _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__3,
                        );
                        lean_inc_ref(v___x_4023_);
                        v___x_4025_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v___x_4025_, 0, v___x_4023_);
                        lean_ctor_set(v___x_4025_, 1, v___x_4023_);
                        lean_ctor_set(v___x_4025_, 2, v___x_4024_);
                        v___x_4026_ = lean_st_mk_ref(v___x_4025_);
                        v___x_4027_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go(v_g_3886_, v_cfg_3887_, v___x_4026_, v_a_3888_, v_a_3889_, v_a_3890_, v_a_3891_);
                        if lean_obj_tag(v___x_4027_) == 0 {
                            v_a_4028_ = lean_ctor_get(v___x_4027_, 0);
                            lean_inc(v_a_4028_);
                            lean_dec_ref_known(v___x_4027_, 1);
                            v___x_4029_ = lean_st_ref_get(v___x_4026_);
                            lean_dec(v___x_4026_);
                            lean_dec(v___x_4029_);
                            v___y_3978_ = v___x_4010_;
                            v___y_3979_ = v_a_3984_;
                            v_a_3980_ = v_a_4028_;
                            state = 10;
                            continue;
                        } else {
                            lean_dec(v___x_4026_);
                            if lean_obj_tag(v___x_4027_) == 0 {
                                v_a_4030_ = lean_ctor_get(v___x_4027_, 0);
                                lean_inc(v_a_4030_);
                                lean_dec_ref_known(v___x_4027_, 1);
                                v___y_3978_ = v___x_4010_;
                                v___y_3979_ = v_a_3984_;
                                v_a_3980_ = v_a_4030_;
                                state = 10;
                                continue;
                            } else {
                                v_a_4031_ = lean_ctor_get(v___x_4027_, 0);
                                lean_inc(v_a_4031_);
                                lean_dec_ref_known(v___x_4027_, 1);
                                v___y_3973_ = v___x_4010_;
                                v___y_3974_ = v_a_3984_;
                                v_a_3975_ = v_a_4031_;
                                state = 9;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_g_3886_);
                        v_a_4032_ = lean_ctor_get(v___x_4012_, 0);
                        lean_inc(v_a_4032_);
                        lean_dec_ref_known(v___x_4012_, 1);
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
                lean_dec(v___x_4050_);
                lean_dec(v___x_4056_);
                if v_isShared_4055_ == 0 {
                    v___x_4058_ = v___x_4054_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4059_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4059_, 0, v_a_4052_);
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
                    v_reuseFailAlloc_4067_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4067_, 0, v_a_4061_);
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
    mut v_g_4069_: *mut LeanObject,
    mut v_cfg_4070_: *mut LeanObject,
    mut v_a_4071_: *mut LeanObject,
    mut v_a_4072_: *mut LeanObject,
    mut v_a_4073_: *mut LeanObject,
    mut v_a_4074_: *mut LeanObject,
    mut v_a_4075_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4076_: *mut LeanObject = core::ptr::null_mut();
    v_res_4076_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(
        v_g_4069_,
        v_cfg_4070_,
        v_a_4071_,
        v_a_4072_,
        v_a_4073_,
        v_a_4074_,
    );
    lean_dec(v_a_4074_);
    lean_dec_ref(v_a_4073_);
    lean_dec(v_a_4072_);
    lean_dec_ref(v_a_4071_);
    lean_dec_ref(v_cfg_4070_);
    return v_res_4076_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__3(
    mut v_00_u03b1_4077_: *mut LeanObject,
    mut v_x_4078_: *mut LeanObject,
    mut v___y_4079_: *mut LeanObject,
    mut v___y_4080_: *mut LeanObject,
    mut v___y_4081_: *mut LeanObject,
    mut v___y_4082_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4084_: *mut LeanObject = core::ptr::null_mut();
    v___x_4084_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__3___redArg(v_x_4078_);
    return v___x_4084_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__3___boxed(
    mut v_00_u03b1_4085_: *mut LeanObject,
    mut v_x_4086_: *mut LeanObject,
    mut v___y_4087_: *mut LeanObject,
    mut v___y_4088_: *mut LeanObject,
    mut v___y_4089_: *mut LeanObject,
    mut v___y_4090_: *mut LeanObject,
    mut v___y_4091_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4092_: *mut LeanObject = core::ptr::null_mut();
    v_res_4092_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__3(v_00_u03b1_4085_, v_x_4086_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_);
    lean_dec(v___y_4090_);
    lean_dec_ref(v___y_4089_);
    lean_dec(v___y_4088_);
    lean_dec_ref(v___y_4087_);
    return v_res_4092_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_FalseOrByContra(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_ApplyControlFlow(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Simproc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_AC(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Structures(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Enums(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_TypeAnalysis(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_BVDecide_Normalize(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_FalseOrByContra(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_ApplyControlFlow(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_Simproc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_AC(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_Structures(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_Enums(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_TypeAnalysis(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_BVDecide_Normalize(builtin);
}
