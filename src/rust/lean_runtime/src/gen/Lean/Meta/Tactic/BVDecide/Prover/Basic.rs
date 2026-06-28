// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Prover.Basic
// Imports: Lean.Meta.Tactic.BVDecide.Reflect Lean.Meta.Tactic.BVDecide.Counterexample Lean.Meta.Tactic.BVDecide.LRAT.Cert
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_mkStr3, l_Lean_replaceRef,
};
use crate::r#gen::Lean::CoreM::l_Lean_Core_checkSystem;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::PersistentArray::{
    l_Lean_PersistentArray_append___redArg, l_Lean_PersistentArray_push___redArg,
    l_Lean_PersistentArray_toArray___redArg,
};
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_instBEqFVarId_beq, l_Lean_instBEqMVarId_beq, l_Lean_instHashableFVarId_hash,
    l_Lean_instHashableMVarId_hash, l_Lean_mkFVar,
};
use crate::r#gen::Lean::Message::{l_Lean_MessageData_ofFormat, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Meta::Basic::l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp;
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Counterexample::{
    initialize_Lean_Meta_Tactic_BVDecide_Counterexample,
    runtime_initialize_Lean_Meta_Tactic_BVDecide_Counterexample,
};
use crate::r#gen::Lean::Meta::Tactic::BVDecide::LRAT::Cert::{
    initialize_Lean_Meta_Tactic_BVDecide_LRAT_Cert,
    runtime_initialize_Lean_Meta_Tactic_BVDecide_LRAT_Cert,
};
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Reflect::Basic::{
    l_Lean_Meta_Tactic_BVDecide_LemmaM_run___redArg, l_Lean_Meta_Tactic_BVDecide_M_run___redArg,
};
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Reflect::SatAtBVLogical::{
    l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and,
    l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___boxed,
    l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___boxed,
};
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Reflect::{
    initialize_Lean_Meta_Tactic_BVDecide_Reflect,
    runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect,
};
use crate::r#gen::Lean::Meta::Tactic::Util::l_Lean_Meta_getPropHyps;
use crate::r#gen::Lean::Util::ShareCommon::l_Lean_ShareCommon_shareCommon___redArg;
use crate::r#gen::Lean::Util::Trace::{
    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go, l_Lean_TraceResult_toEmoji,
    l_Lean_trace_profiler, l_Lean_trace_profiler_threshold, l_Lean_trace_profiler_useHeartbeats,
};
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Basic::l_Std_Tactic_BVDecide_BVPred_toString;
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BoolExpr::Basic::l_Std_Tactic_BVDecide_Gate_toString;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::Float::{lean_float_decLt, lean_float_div, lean_float_sub};
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
    lean_usize_mul, lean_usize_shift_left, lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_uint64_of_nat, lean_usize_add, lean_usize_dec_le, lean_usize_dec_lt, lean_usize_of_nat,
    lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_size, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::IO::{
    lean_io_get_num_heartbeats, lean_io_mono_nanos_now,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_6,
    lean_apply_7, lean_apply_8, lean_box, lean_box_float, lean_closure_set, lean_ctor_get,
    lean_ctor_get_uint8, lean_ctor_get_uint64, lean_ctor_set, lean_ctor_set_float,
    lean_ctor_set_tag, lean_ctor_set_uint8, lean_ctor_set_uint64, lean_ctor_set_usize, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_float_once, lean_inc, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unbox_float, lean_unbox_usize, lean_unsigned_to_nat, lean_usize_once,
};
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__0_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [98, 118, 95, 100, 101, 99, 105, 100, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__1_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__1_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__3_value: LeanStringObject<443> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 443, m_capacity: 443, m_length: 442, m_data: [78, 111, 110, 101, 32, 111, 102, 32, 116, 104, 101, 32, 104, 121, 112, 111, 116, 104, 101, 115, 101, 115, 32, 97, 114, 101, 32, 105, 110, 32, 116, 104, 101, 32, 115, 117, 112, 112, 111, 114, 116, 101, 100, 32, 66, 105, 116, 86, 101, 99, 32, 102, 114, 97, 103, 109, 101, 110, 116, 32, 97, 102, 116, 101, 114, 32, 97, 112, 112, 108, 121, 105, 110, 103, 32, 112, 114, 101, 112, 114, 111, 99, 101, 115, 115, 105, 110, 103, 46, 10, 84, 104, 101, 114, 101, 32, 97, 114, 101, 32, 116, 104, 114, 101, 101, 32, 112, 111, 116, 101, 110, 116, 105, 97, 108, 32, 114, 101, 97, 115, 111, 110, 115, 32, 102, 111, 114, 32, 116, 104, 105, 115, 58, 10, 49, 46, 32, 73, 102, 32, 121, 111, 117, 32, 97, 114, 101, 32, 117, 115, 105, 110, 103, 32, 99, 117, 115, 116, 111, 109, 32, 66, 105, 116, 86, 101, 99, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 115, 32, 115, 105, 109, 112, 108, 105, 102, 121, 32, 116, 104, 101, 109, 32, 116, 111, 32, 98, 117, 105, 108, 116, 45, 105, 110, 32, 111, 110, 101, 115, 46, 10, 50, 46, 32, 73, 102, 32, 121, 111, 117, 114, 32, 112, 114, 111, 98, 108, 101, 109, 32, 105, 115, 32, 117, 115, 105, 110, 103, 32, 111, 110, 108, 121, 32, 98, 117, 105, 108, 116, 45, 105, 110, 32, 111, 110, 101, 115, 32, 105, 116, 32, 109, 105, 103, 104, 116, 32, 99, 117, 114, 114, 101, 110, 116, 108, 121, 32, 98, 101, 32, 111, 117, 116, 32, 111, 102, 32, 114, 101, 97, 99, 104, 46, 10, 32, 32, 32, 67, 111, 110, 115, 105, 100, 101, 114, 32, 101, 120, 112, 114, 101, 115, 115, 105, 110, 103, 32, 105, 116, 32, 105, 110, 32, 116, 101, 114, 109, 115, 32, 111, 102, 32, 100, 105, 102, 102, 101, 114, 101, 110, 116, 32, 111, 112, 101, 114, 97, 116, 105, 111, 110, 115, 32, 116, 104, 97, 116, 32, 97, 114, 101, 32, 98, 101, 116, 116, 101, 114, 32, 115, 117, 112, 112, 111, 114, 116, 101, 100, 46, 10, 51, 46, 32, 84, 104, 101, 32, 111, 114, 105, 103, 105, 110, 97, 108, 32, 103, 111, 97, 108, 32, 119, 97, 115, 32, 114, 101, 100, 117, 99, 101, 100, 32, 116, 111, 32, 70, 97, 108, 115, 101, 32, 97, 110, 100, 32, 105, 115, 32, 116, 104, 117, 115, 32, 105, 110, 118, 97, 108, 105, 100, 46, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__4_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__3_value) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__4_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__0_value:
    LeanStringObject<35> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 35,
    m_capacity: 35,
    m_length: 34,
    m_data: [
        82, 101, 102, 108, 101, 99, 116, 105, 110, 103, 32, 103, 111, 97, 108, 32, 105, 110, 116,
        111, 32, 66, 86, 76, 111, 103, 105, 99, 97, 108, 69, 120, 112, 114, 0,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__1_value:
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
        l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__0_value
    ) as *mut LeanObject],
};
static mut l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__1_value
) as *mut LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__2_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__2:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__0_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__2: f64 = 0.0;
pub static l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__3_value: LeanStringObject<54> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [60, 101, 120, 99, 101, 112, 116, 105, 111, 110, 32, 116, 104, 114, 111, 119, 110, 32, 119, 104, 105, 108, 101, 32, 112, 114, 111, 100, 117, 99, 105, 110, 103, 32, 116, 114, 97, 99, 101, 32, 110, 111, 100, 101, 32, 109, 101, 115, 115, 97, 103, 101, 62, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__3_value) as *mut LeanObject;
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__5: f64 = 0.0;
pub static l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [102, 97, 108, 115, 101, 0]};
static mut l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__0_value) as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__1_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 114, 117, 101, 0]};
static mut l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__1_value) as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__2_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [33, 0]};
static mut l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__2_value) as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__3_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__3_value) as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__4_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__4_value) as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__5_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [40, 105, 102, 32, 0]};
static mut l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__5_value) as *mut LeanObject;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6___redArg___closed__0_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6___redArg___closed__1_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6___redArg___closed__1_value) as *mut LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__0_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__0:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__2_value:
    LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [116, 114, 97, 99, 101, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__2_value
) as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__3_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__2_value
        ) as *mut LeanObject,
        14231257465488249300 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__3_value
) as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__4_value:
    LeanStringObject<34> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 34,
    m_capacity: 34,
    m_length: 33,
    m_data: [
        82, 101, 102, 108, 101, 99, 116, 101, 100, 32, 98, 118, 32, 108, 111, 103, 105, 99, 97,
        108, 32, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 58, 32, 0,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__4_value
) as *mut LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__5_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__5:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__6_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__6: f64 =
    0.0;
pub static l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___closed__0_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___closed__0_value
)
    as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___closed__1_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [77, 101, 116, 97, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___closed__1_value
)
    as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___closed__2_value:
    LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [84, 97, 99, 116, 105, 99, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___closed__2_value
)
    as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___closed__3_value:
    LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [98, 118, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___closed__3: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___closed__3_value
)
    as *mut LeanObject;
static l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___closed__4_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___closed__1_value
        ) as *mut LeanObject,
        142734480563613395 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___closed__4_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___closed__4_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___closed__2_value
        ) as *mut LeanObject,
        15847151208953044930 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___closed__4_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___closed__4_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___closed__3_value
        ) as *mut LeanObject,
        10551690841954068875 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___closed__4_value
)
    as *mut LeanObject;
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__4___redArg___lam__0(
    mut v_x_1797_: *mut LeanObject,
    mut v___y_1798_: *mut LeanObject,
    mut v___y_1799_: *mut LeanObject,
    mut v___y_1800_: *mut LeanObject,
    mut v___y_1801_: *mut LeanObject,
    mut v___y_1802_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1804_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_1798_);
    v___x_1804_ = lean_apply_6(
        v_x_1797_,
        v___y_1798_,
        v___y_1799_,
        v___y_1800_,
        v___y_1801_,
        v___y_1802_,
        lean_box(0),
    );
    return v___x_1804_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__4___redArg___lam__0___boxed(
    mut v_x_1805_: *mut LeanObject,
    mut v___y_1806_: *mut LeanObject,
    mut v___y_1807_: *mut LeanObject,
    mut v___y_1808_: *mut LeanObject,
    mut v___y_1809_: *mut LeanObject,
    mut v___y_1810_: *mut LeanObject,
    mut v___y_1811_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1812_: *mut LeanObject = core::ptr::null_mut();
    v_res_1812_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__4___redArg___lam__0(v_x_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_);
    lean_dec(v___y_1806_);
    return v_res_1812_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__4___redArg(
    mut v_mvarId_1813_: *mut LeanObject,
    mut v_x_1814_: *mut LeanObject,
    mut v___y_1815_: *mut LeanObject,
    mut v___y_1816_: *mut LeanObject,
    mut v___y_1817_: *mut LeanObject,
    mut v___y_1818_: *mut LeanObject,
    mut v___y_1819_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1826_: u8 = 0;
    let mut v___x_1828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1830_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_1815_);
                v___f_1821_ = lean_alloc_closure(l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__4___redArg___lam__0___boxed as *mut core::ffi::c_void, 7, 2);
                lean_closure_set(v___f_1821_, 0, v_x_1814_);
                lean_closure_set(v___f_1821_, 1, v___y_1815_);
                v___x_1822_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    lean_box(0),
                    v_mvarId_1813_,
                    v___f_1821_,
                    v___y_1816_,
                    v___y_1817_,
                    v___y_1818_,
                    v___y_1819_,
                );
                if lean_obj_tag(v___x_1822_) == 0 {
                    return v___x_1822_;
                } else {
                    v_a_1823_ = lean_ctor_get(v___x_1822_, 0);
                    v_isSharedCheck_1830_ = (!lean_is_exclusive(v___x_1822_)) as u8;
                    if v_isSharedCheck_1830_ == 0 {
                        v___x_1825_ = v___x_1822_;
                        v_isShared_1826_ = v_isSharedCheck_1830_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1823_);
                        lean_dec(v___x_1822_);
                        v___x_1825_ = lean_box(0);
                        v_isShared_1826_ = v_isSharedCheck_1830_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1826_ == 0 {
                    v___x_1828_ = v___x_1825_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1829_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1829_, 0, v_a_1823_);
                    v___x_1828_ = v_reuseFailAlloc_1829_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1828_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__4___redArg___boxed(
    mut v_mvarId_1831_: *mut LeanObject,
    mut v_x_1832_: *mut LeanObject,
    mut v___y_1833_: *mut LeanObject,
    mut v___y_1834_: *mut LeanObject,
    mut v___y_1835_: *mut LeanObject,
    mut v___y_1836_: *mut LeanObject,
    mut v___y_1837_: *mut LeanObject,
    mut v___y_1838_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1839_: *mut LeanObject = core::ptr::null_mut();
    v_res_1839_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__4___redArg(v_mvarId_1831_, v_x_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_);
    lean_dec(v___y_1837_);
    lean_dec_ref(v___y_1836_);
    lean_dec(v___y_1835_);
    lean_dec_ref(v___y_1834_);
    lean_dec(v___y_1833_);
    return v_res_1839_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__4(
    mut v_00_u03b1_1840_: *mut LeanObject,
    mut v_mvarId_1841_: *mut LeanObject,
    mut v_x_1842_: *mut LeanObject,
    mut v___y_1843_: *mut LeanObject,
    mut v___y_1844_: *mut LeanObject,
    mut v___y_1845_: *mut LeanObject,
    mut v___y_1846_: *mut LeanObject,
    mut v___y_1847_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1849_: *mut LeanObject = core::ptr::null_mut();
    v___x_1849_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__4___redArg(v_mvarId_1841_, v_x_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_);
    return v___x_1849_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__4___boxed(
    mut v_00_u03b1_1850_: *mut LeanObject,
    mut v_mvarId_1851_: *mut LeanObject,
    mut v_x_1852_: *mut LeanObject,
    mut v___y_1853_: *mut LeanObject,
    mut v___y_1854_: *mut LeanObject,
    mut v___y_1855_: *mut LeanObject,
    mut v___y_1856_: *mut LeanObject,
    mut v___y_1857_: *mut LeanObject,
    mut v___y_1858_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1859_: *mut LeanObject = core::ptr::null_mut();
    v_res_1859_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__4(v_00_u03b1_1850_, v_mvarId_1851_, v_x_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_);
    lean_dec(v___y_1857_);
    lean_dec_ref(v___y_1856_);
    lean_dec(v___y_1855_);
    lean_dec_ref(v___y_1854_);
    lean_dec(v___y_1853_);
    return v_res_1859_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1_spec__3_spec__8___redArg(
    mut v_x_1860_: *mut LeanObject,
    mut v_x_1861_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_1862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1867_: u8 = 0;
    let mut v___x_1868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: u64 = 0;
    let mut v___x_1870_: u64 = 0;
    let mut v___x_1871_: u64 = 0;
    let mut v_fold_1872_: u64 = 0;
    let mut v___x_1873_: u64 = 0;
    let mut v___x_1874_: u64 = 0;
    let mut v___x_1875_: u64 = 0;
    let mut v___x_1876_: usize = 0;
    let mut v___x_1877_: usize = 0;
    let mut v___x_1878_: usize = 0;
    let mut v___x_1879_: usize = 0;
    let mut v___x_1880_: usize = 0;
    let mut v___x_1881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1887_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1861_) == 0 {
                    return v_x_1860_;
                } else {
                    v_key_1862_ = lean_ctor_get(v_x_1861_, 0);
                    v_value_1863_ = lean_ctor_get(v_x_1861_, 1);
                    v_tail_1864_ = lean_ctor_get(v_x_1861_, 2);
                    v_isSharedCheck_1887_ = (!lean_is_exclusive(v_x_1861_)) as u8;
                    if v_isSharedCheck_1887_ == 0 {
                        v___x_1866_ = v_x_1861_;
                        v_isShared_1867_ = v_isSharedCheck_1887_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1864_);
                        lean_inc(v_value_1863_);
                        lean_inc(v_key_1862_);
                        lean_dec(v_x_1861_);
                        v___x_1866_ = lean_box(0);
                        v_isShared_1867_ = v_isSharedCheck_1887_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1868_ = lean_array_get_size(v_x_1860_);
                v___x_1869_ = l_Lean_instHashableFVarId_hash(v_key_1862_);
                v___x_1870_ = 32u64;
                v___x_1871_ = lean_uint64_shift_right(v___x_1869_, v___x_1870_);
                v_fold_1872_ = lean_uint64_xor(v___x_1869_, v___x_1871_);
                v___x_1873_ = 16u64;
                v___x_1874_ = lean_uint64_shift_right(v_fold_1872_, v___x_1873_);
                v___x_1875_ = lean_uint64_xor(v_fold_1872_, v___x_1874_);
                v___x_1876_ = lean_uint64_to_usize(v___x_1875_);
                v___x_1877_ = lean_usize_of_nat(v___x_1868_);
                v___x_1878_ = 1usize;
                v___x_1879_ = lean_usize_sub(v___x_1877_, v___x_1878_);
                v___x_1880_ = lean_usize_land(v___x_1876_, v___x_1879_);
                v___x_1881_ = lean_array_uget_borrowed(v_x_1860_, v___x_1880_);
                lean_inc(v___x_1881_);
                if v_isShared_1867_ == 0 {
                    lean_ctor_set(v___x_1866_, 2, v___x_1881_);
                    v___x_1883_ = v___x_1866_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1886_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1886_, 0, v_key_1862_);
                    lean_ctor_set(v_reuseFailAlloc_1886_, 1, v_value_1863_);
                    lean_ctor_set(v_reuseFailAlloc_1886_, 2, v___x_1881_);
                    v___x_1883_ = v_reuseFailAlloc_1886_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1884_ = lean_array_uset(v_x_1860_, v___x_1880_, v___x_1883_);
                v_x_1860_ = v___x_1884_;
                v_x_1861_ = v_tail_1864_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1_spec__3___redArg(
    mut v_i_1888_: *mut LeanObject,
    mut v_source_1889_: *mut LeanObject,
    mut v_target_1890_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: u8 = 0;
    let mut v_es_1893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_1895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_1896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1891_ = lean_array_get_size(v_source_1889_);
                v___x_1892_ = lean_nat_dec_lt(v_i_1888_, v___x_1891_);
                if v___x_1892_ == 0 {
                    lean_dec_ref(v_source_1889_);
                    lean_dec(v_i_1888_);
                    return v_target_1890_;
                } else {
                    v_es_1893_ = lean_array_fget(v_source_1889_, v_i_1888_);
                    v___x_1894_ = lean_box(0);
                    v_source_1895_ = lean_array_fset(v_source_1889_, v_i_1888_, v___x_1894_);
                    v_target_1896_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1_spec__3_spec__8___redArg(v_target_1890_, v_es_1893_);
                    v___x_1897_ = lean_unsigned_to_nat(1);
                    v___x_1898_ = lean_nat_add(v_i_1888_, v___x_1897_);
                    lean_dec(v_i_1888_);
                    v_i_1888_ = v___x_1898_;
                    v_source_1889_ = v_source_1895_;
                    v_target_1890_ = v_target_1896_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1___redArg(
    mut v_data_1900_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_1903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut LeanObject = core::ptr::null_mut();
    v___x_1901_ = lean_array_get_size(v_data_1900_);
    v___x_1902_ = lean_unsigned_to_nat(2);
    v_nbuckets_1903_ = lean_nat_mul(v___x_1901_, v___x_1902_);
    v___x_1904_ = lean_unsigned_to_nat(0);
    v___x_1905_ = lean_box(0);
    v___x_1906_ = lean_mk_array(v_nbuckets_1903_, v___x_1905_);
    v___x_1907_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1_spec__3___redArg(v___x_1904_, v_data_1900_, v___x_1906_);
    return v___x_1907_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0___redArg(
    mut v_a_1908_: *mut LeanObject,
    mut v_x_1909_: *mut LeanObject,
) -> u8 {
    let mut v___x_1910_: u8 = 0;
    let mut v_key_1911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1909_) == 0 {
                    v___x_1910_ = 0;
                    return v___x_1910_;
                } else {
                    v_key_1911_ = lean_ctor_get(v_x_1909_, 0);
                    v_tail_1912_ = lean_ctor_get(v_x_1909_, 2);
                    v___x_1913_ = l_Lean_instBEqFVarId_beq(v_key_1911_, v_a_1908_);
                    if v___x_1913_ == 0 {
                        v_x_1909_ = v_tail_1912_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1913_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0___redArg___boxed(
    mut v_a_1915_: *mut LeanObject,
    mut v_x_1916_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1917_: u8 = 0;
    let mut v_r_1918_: *mut LeanObject = core::ptr::null_mut();
    v_res_1917_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0___redArg(v_a_1915_, v_x_1916_);
    lean_dec(v_x_1916_);
    lean_dec(v_a_1915_);
    v_r_1918_ = lean_box((v_res_1917_) as usize);
    return v_r_1918_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__0___redArg(
    mut v_m_1919_: *mut LeanObject,
    mut v_a_1920_: *mut LeanObject,
    mut v_b_1921_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_1922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_1923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: u64 = 0;
    let mut v___x_1926_: u64 = 0;
    let mut v___x_1927_: u64 = 0;
    let mut v_fold_1928_: u64 = 0;
    let mut v___x_1929_: u64 = 0;
    let mut v___x_1930_: u64 = 0;
    let mut v___x_1931_: u64 = 0;
    let mut v___x_1932_: usize = 0;
    let mut v___x_1933_: usize = 0;
    let mut v___x_1934_: usize = 0;
    let mut v___x_1935_: usize = 0;
    let mut v___x_1936_: usize = 0;
    let mut v_bkt_1937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: u8 = 0;
    let mut v___x_1940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1941_: u8 = 0;
    let mut v___x_1942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: u8 = 0;
    let mut v_val_1952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1959_: u8 = 0;
    let mut v_unused_1960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1961_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1922_ = lean_ctor_get(v_m_1919_, 0);
                v_buckets_1923_ = lean_ctor_get(v_m_1919_, 1);
                v___x_1924_ = lean_array_get_size(v_buckets_1923_);
                v___x_1925_ = l_Lean_instHashableFVarId_hash(v_a_1920_);
                v___x_1926_ = 32u64;
                v___x_1927_ = lean_uint64_shift_right(v___x_1925_, v___x_1926_);
                v_fold_1928_ = lean_uint64_xor(v___x_1925_, v___x_1927_);
                v___x_1929_ = 16u64;
                v___x_1930_ = lean_uint64_shift_right(v_fold_1928_, v___x_1929_);
                v___x_1931_ = lean_uint64_xor(v_fold_1928_, v___x_1930_);
                v___x_1932_ = lean_uint64_to_usize(v___x_1931_);
                v___x_1933_ = lean_usize_of_nat(v___x_1924_);
                v___x_1934_ = 1usize;
                v___x_1935_ = lean_usize_sub(v___x_1933_, v___x_1934_);
                v___x_1936_ = lean_usize_land(v___x_1932_, v___x_1935_);
                v_bkt_1937_ = lean_array_uget_borrowed(v_buckets_1923_, v___x_1936_);
                v___x_1938_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0___redArg(v_a_1920_, v_bkt_1937_);
                if v___x_1938_ == 0 {
                    lean_inc_ref(v_buckets_1923_);
                    lean_inc(v_size_1922_);
                    v_isSharedCheck_1959_ = (!lean_is_exclusive(v_m_1919_)) as u8;
                    if v_isSharedCheck_1959_ == 0 {
                        v_unused_1960_ = lean_ctor_get(v_m_1919_, 1);
                        lean_dec(v_unused_1960_);
                        v_unused_1961_ = lean_ctor_get(v_m_1919_, 0);
                        lean_dec(v_unused_1961_);
                        v___x_1940_ = v_m_1919_;
                        v_isShared_1941_ = v_isSharedCheck_1959_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_m_1919_);
                        v___x_1940_ = lean_box(0);
                        v_isShared_1941_ = v_isSharedCheck_1959_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_b_1921_);
                    lean_dec(v_a_1920_);
                    return v_m_1919_;
                }
            }
            1 => {
                v___x_1942_ = lean_unsigned_to_nat(1);
                v_size_x27_1943_ = lean_nat_add(v_size_1922_, v___x_1942_);
                lean_dec(v_size_1922_);
                lean_inc(v_bkt_1937_);
                v___x_1944_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_1944_, 0, v_a_1920_);
                lean_ctor_set(v___x_1944_, 1, v_b_1921_);
                lean_ctor_set(v___x_1944_, 2, v_bkt_1937_);
                v_buckets_x27_1945_ = lean_array_uset(v_buckets_1923_, v___x_1936_, v___x_1944_);
                v___x_1946_ = lean_unsigned_to_nat(4);
                v___x_1947_ = lean_nat_mul(v_size_x27_1943_, v___x_1946_);
                v___x_1948_ = lean_unsigned_to_nat(3);
                v___x_1949_ = lean_nat_div(v___x_1947_, v___x_1948_);
                lean_dec(v___x_1947_);
                v___x_1950_ = lean_array_get_size(v_buckets_x27_1945_);
                v___x_1951_ = lean_nat_dec_le(v___x_1949_, v___x_1950_);
                lean_dec(v___x_1949_);
                if v___x_1951_ == 0 {
                    v_val_1952_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1___redArg(v_buckets_x27_1945_);
                    if v_isShared_1941_ == 0 {
                        lean_ctor_set(v___x_1940_, 1, v_val_1952_);
                        lean_ctor_set(v___x_1940_, 0, v_size_x27_1943_);
                        v___x_1954_ = v___x_1940_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1955_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1955_, 0, v_size_x27_1943_);
                        lean_ctor_set(v_reuseFailAlloc_1955_, 1, v_val_1952_);
                        v___x_1954_ = v_reuseFailAlloc_1955_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_1941_ == 0 {
                        lean_ctor_set(v___x_1940_, 1, v_buckets_x27_1945_);
                        lean_ctor_set(v___x_1940_, 0, v_size_x27_1943_);
                        v___x_1957_ = v___x_1940_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1958_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_size_x27_1943_);
                        lean_ctor_set(v_reuseFailAlloc_1958_, 1, v_buckets_x27_1945_);
                        v___x_1957_ = v_reuseFailAlloc_1958_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1954_;
            }
            3 => {
                return v___x_1957_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__2()
-> *mut LeanObject {
    let mut v___x_1965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: *mut LeanObject = core::ptr::null_mut();
    v___x_1965_ = lean_box(0);
    v___x_1966_ = lean_unsigned_to_nat(16);
    v___x_1967_ = lean_mk_array(v___x_1966_, v___x_1965_);
    return v___x_1967_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__3()
-> *mut LeanObject {
    let mut v___x_1968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: *mut LeanObject = core::ptr::null_mut();
    v___x_1968_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__2_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__2);
    v___x_1969_ = lean_unsigned_to_nat(0);
    v___x_1970_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1970_, 0, v___x_1969_);
    lean_ctor_set(v___x_1970_, 1, v___x_1968_);
    return v___x_1970_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__4()
-> *mut LeanObject {
    let mut v___x_1971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sats_1972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut LeanObject = core::ptr::null_mut();
    v___x_1971_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__3);
    v_sats_1972_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__1;
    v___x_1973_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_1973_, 0, v_sats_1972_);
    lean_ctor_set(v___x_1973_, 1, v___x_1971_);
    lean_ctor_set(v___x_1973_, 2, v___x_1971_);
    lean_ctor_set(v___x_1973_, 3, v___x_1971_);
    return v___x_1973_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__1(
    mut v_as_1974_: *mut LeanObject,
    mut v_sz_1975_: usize,
    mut v_i_1976_: usize,
    mut v_b_1977_: *mut LeanObject,
    mut v___y_1978_: *mut LeanObject,
    mut v___y_1979_: *mut LeanObject,
    mut v___y_1980_: *mut LeanObject,
    mut v___y_1981_: *mut LeanObject,
    mut v___y_1982_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: usize = 0;
    let mut v___x_1987_: usize = 0;
    let mut v___x_1989_: u8 = 0;
    let mut v___x_1990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2005_: u8 = 0;
    let mut v_val_2006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2012_: u8 = 0;
    let mut v_fst_2013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2017_: u8 = 0;
    let mut v___x_2018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2023_: u8 = 0;
    let mut v_a_2024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2027_: u8 = 0;
    let mut v___x_2029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2031_: u8 = 0;
    let mut v_a_2032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2035_: u8 = 0;
    let mut v___x_2037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2039_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1989_ = lean_usize_dec_lt(v_i_1976_, v_sz_1975_);
                if v___x_1989_ == 0 {
                    v___x_1990_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1990_, 0, v_b_1977_);
                    return v___x_1990_;
                } else {
                    v___x_1991_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__0;
                    v___x_1992_ = l_Lean_Core_checkSystem(v___x_1991_, v___y_1981_, v___y_1982_);
                    if lean_obj_tag(v___x_1992_) == 0 {
                        lean_dec_ref_known(v___x_1992_, 1);
                        v_a_1993_ = lean_array_uget_borrowed(v_as_1974_, v_i_1976_);
                        lean_inc(v_a_1993_);
                        v___x_1994_ = l_Lean_mkFVar(v_a_1993_);
                        v___x_1995_ = lean_alloc_closure(
                            l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___boxed
                                as *mut core::ffi::c_void,
                            8,
                            1,
                        );
                        lean_closure_set(v___x_1995_, 0, v___x_1994_);
                        v___x_1996_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__4), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__4_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__4);
                        v___x_1997_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_run___redArg(
                            v___x_1995_,
                            v___x_1996_,
                            v___y_1978_,
                            v___y_1979_,
                            v___y_1980_,
                            v___y_1981_,
                            v___y_1982_,
                        );
                        if lean_obj_tag(v___x_1997_) == 0 {
                            v_a_1998_ = lean_ctor_get(v___x_1997_, 0);
                            lean_inc(v_a_1998_);
                            lean_dec_ref_known(v___x_1997_, 1);
                            v_fst_1999_ = lean_ctor_get(v_a_1998_, 0);
                            lean_inc(v_fst_1999_);
                            if lean_obj_tag(v_fst_1999_) == 1 {
                                v_snd_2000_ = lean_ctor_get(v_a_1998_, 1);
                                lean_inc(v_snd_2000_);
                                lean_dec(v_a_1998_);
                                v_fst_2001_ = lean_ctor_get(v_b_1977_, 0);
                                v_snd_2002_ = lean_ctor_get(v_b_1977_, 1);
                                v_isSharedCheck_2012_ = (!lean_is_exclusive(v_b_1977_)) as u8;
                                if v_isSharedCheck_2012_ == 0 {
                                    v___x_2004_ = v_b_1977_;
                                    v_isShared_2005_ = v_isSharedCheck_2012_;
                                    state = 2;
                                    continue;
                                } else {
                                    lean_inc(v_snd_2002_);
                                    lean_inc(v_fst_2001_);
                                    lean_dec(v_b_1977_);
                                    v___x_2004_ = lean_box(0);
                                    v_isShared_2005_ = v_isSharedCheck_2012_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                lean_dec(v_fst_1999_);
                                lean_dec(v_a_1998_);
                                v_fst_2013_ = lean_ctor_get(v_b_1977_, 0);
                                v_snd_2014_ = lean_ctor_get(v_b_1977_, 1);
                                v_isSharedCheck_2023_ = (!lean_is_exclusive(v_b_1977_)) as u8;
                                if v_isSharedCheck_2023_ == 0 {
                                    v___x_2016_ = v_b_1977_;
                                    v_isShared_2017_ = v_isSharedCheck_2023_;
                                    state = 4;
                                    continue;
                                } else {
                                    lean_inc(v_snd_2014_);
                                    lean_inc(v_fst_2013_);
                                    lean_dec(v_b_1977_);
                                    v___x_2016_ = lean_box(0);
                                    v_isShared_2017_ = v_isSharedCheck_2023_;
                                    state = 4;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref(v_b_1977_);
                            v_a_2024_ = lean_ctor_get(v___x_1997_, 0);
                            v_isSharedCheck_2031_ = (!lean_is_exclusive(v___x_1997_)) as u8;
                            if v_isSharedCheck_2031_ == 0 {
                                v___x_2026_ = v___x_1997_;
                                v_isShared_2027_ = v_isSharedCheck_2031_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_2024_);
                                lean_dec(v___x_1997_);
                                v___x_2026_ = lean_box(0);
                                v_isShared_2027_ = v_isSharedCheck_2031_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_b_1977_);
                        v_a_2032_ = lean_ctor_get(v___x_1992_, 0);
                        v_isSharedCheck_2039_ = (!lean_is_exclusive(v___x_1992_)) as u8;
                        if v_isSharedCheck_2039_ == 0 {
                            v___x_2034_ = v___x_1992_;
                            v_isShared_2035_ = v_isSharedCheck_2039_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_2032_);
                            lean_dec(v___x_1992_);
                            v___x_2034_ = lean_box(0);
                            v_isShared_2035_ = v_isSharedCheck_2039_;
                            state = 8;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1986_ = 1usize;
                v___x_1987_ = lean_usize_add(v_i_1976_, v___x_1986_);
                v_i_1976_ = v___x_1987_;
                v_b_1977_ = v_a_1985_;
                state = 0;
                continue;
            }
            2 => {
                v_val_2006_ = lean_ctor_get(v_fst_1999_, 0);
                lean_inc(v_val_2006_);
                lean_dec_ref_known(v_fst_1999_, 1);
                v___x_2007_ = l_Array_append___redArg(v_fst_2001_, v_snd_2000_);
                lean_dec(v_snd_2000_);
                v___x_2008_ = lean_array_push(v___x_2007_, v_val_2006_);
                if v_isShared_2005_ == 0 {
                    lean_ctor_set(v___x_2004_, 0, v___x_2008_);
                    v___x_2010_ = v___x_2004_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2011_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2011_, 0, v___x_2008_);
                    lean_ctor_set(v_reuseFailAlloc_2011_, 1, v_snd_2002_);
                    v___x_2010_ = v_reuseFailAlloc_2011_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_a_1985_ = v___x_2010_;
                state = 1;
                continue;
            }
            4 => {
                v___x_2018_ = lean_box(0);
                lean_inc(v_a_1993_);
                v___x_2019_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__0___redArg(v_snd_2014_, v_a_1993_, v___x_2018_);
                if v_isShared_2017_ == 0 {
                    lean_ctor_set(v___x_2016_, 1, v___x_2019_);
                    v___x_2021_ = v___x_2016_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2022_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2022_, 0, v_fst_2013_);
                    lean_ctor_set(v_reuseFailAlloc_2022_, 1, v___x_2019_);
                    v___x_2021_ = v_reuseFailAlloc_2022_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_a_1985_ = v___x_2021_;
                state = 1;
                continue;
            }
            6 => {
                if v_isShared_2027_ == 0 {
                    v___x_2029_ = v___x_2026_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2030_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2030_, 0, v_a_2024_);
                    v___x_2029_ = v_reuseFailAlloc_2030_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2029_;
            }
            8 => {
                if v_isShared_2035_ == 0 {
                    v___x_2037_ = v___x_2034_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2038_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2038_, 0, v_a_2032_);
                    v___x_2037_ = v_reuseFailAlloc_2038_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2037_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___boxed(
    mut v_as_2040_: *mut LeanObject,
    mut v_sz_2041_: *mut LeanObject,
    mut v_i_2042_: *mut LeanObject,
    mut v_b_2043_: *mut LeanObject,
    mut v___y_2044_: *mut LeanObject,
    mut v___y_2045_: *mut LeanObject,
    mut v___y_2046_: *mut LeanObject,
    mut v___y_2047_: *mut LeanObject,
    mut v___y_2048_: *mut LeanObject,
    mut v___y_2049_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2050_: usize = 0;
    let mut v_i_boxed_2051_: usize = 0;
    let mut v_res_2052_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2050_ = lean_unbox_usize(v_sz_2041_);
    lean_dec(v_sz_2041_);
    v_i_boxed_2051_ = lean_unbox_usize(v_i_2042_);
    lean_dec(v_i_2042_);
    v_res_2052_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__1(v_as_2040_, v_sz_boxed_2050_, v_i_boxed_2051_, v_b_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_);
    lean_dec(v___y_2048_);
    lean_dec_ref(v___y_2047_);
    lean_dec(v___y_2046_);
    lean_dec_ref(v___y_2045_);
    lean_dec(v___y_2044_);
    lean_dec_ref(v_as_2040_);
    return v_res_2052_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__3_spec__5(
    mut v_msgData_2053_: *mut LeanObject,
    mut v___y_2054_: *mut LeanObject,
    mut v___y_2055_: *mut LeanObject,
    mut v___y_2056_: *mut LeanObject,
    mut v___y_2057_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_2062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_2063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut LeanObject = core::ptr::null_mut();
    v___x_2059_ = lean_st_ref_get(v___y_2057_);
    v_env_2060_ = lean_ctor_get(v___x_2059_, 0);
    lean_inc_ref(v_env_2060_);
    lean_dec(v___x_2059_);
    v___x_2061_ = lean_st_ref_get(v___y_2055_);
    v_mctx_2062_ = lean_ctor_get(v___x_2061_, 0);
    lean_inc_ref(v_mctx_2062_);
    lean_dec(v___x_2061_);
    v_lctx_2063_ = lean_ctor_get(v___y_2054_, 2);
    v_options_2064_ = lean_ctor_get(v___y_2056_, 2);
    lean_inc_ref(v_options_2064_);
    lean_inc_ref(v_lctx_2063_);
    v___x_2065_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_2065_, 0, v_env_2060_);
    lean_ctor_set(v___x_2065_, 1, v_mctx_2062_);
    lean_ctor_set(v___x_2065_, 2, v_lctx_2063_);
    lean_ctor_set(v___x_2065_, 3, v_options_2064_);
    v___x_2066_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_2066_, 0, v___x_2065_);
    lean_ctor_set(v___x_2066_, 1, v_msgData_2053_);
    v___x_2067_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2067_, 0, v___x_2066_);
    return v___x_2067_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__3_spec__5___boxed(
    mut v_msgData_2068_: *mut LeanObject,
    mut v___y_2069_: *mut LeanObject,
    mut v___y_2070_: *mut LeanObject,
    mut v___y_2071_: *mut LeanObject,
    mut v___y_2072_: *mut LeanObject,
    mut v___y_2073_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2074_: *mut LeanObject = core::ptr::null_mut();
    v_res_2074_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__3_spec__5(v_msgData_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_);
    lean_dec(v___y_2072_);
    lean_dec_ref(v___y_2071_);
    lean_dec(v___y_2070_);
    lean_dec_ref(v___y_2069_);
    return v_res_2074_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__3___redArg(
    mut v_msg_2075_: *mut LeanObject,
    mut v___y_2076_: *mut LeanObject,
    mut v___y_2077_: *mut LeanObject,
    mut v___y_2078_: *mut LeanObject,
    mut v___y_2079_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_2081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2086_: u8 = 0;
    let mut v___x_2087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2091_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2081_ = lean_ctor_get(v___y_2078_, 5);
                v___x_2082_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__3_spec__5(v_msg_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_);
                v_a_2083_ = lean_ctor_get(v___x_2082_, 0);
                v_isSharedCheck_2091_ = (!lean_is_exclusive(v___x_2082_)) as u8;
                if v_isSharedCheck_2091_ == 0 {
                    v___x_2085_ = v___x_2082_;
                    v_isShared_2086_ = v_isSharedCheck_2091_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_2083_);
                    lean_dec(v___x_2082_);
                    v___x_2085_ = lean_box(0);
                    v_isShared_2086_ = v_isSharedCheck_2091_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_2081_);
                v___x_2087_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2087_, 0, v_ref_2081_);
                lean_ctor_set(v___x_2087_, 1, v_a_2083_);
                if v_isShared_2086_ == 0 {
                    lean_ctor_set_tag(v___x_2085_, 1);
                    lean_ctor_set(v___x_2085_, 0, v___x_2087_);
                    v___x_2089_ = v___x_2085_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2090_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2090_, 0, v___x_2087_);
                    v___x_2089_ = v_reuseFailAlloc_2090_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2089_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__3___redArg___boxed(
    mut v_msg_2092_: *mut LeanObject,
    mut v___y_2093_: *mut LeanObject,
    mut v___y_2094_: *mut LeanObject,
    mut v___y_2095_: *mut LeanObject,
    mut v___y_2096_: *mut LeanObject,
    mut v___y_2097_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2098_: *mut LeanObject = core::ptr::null_mut();
    v_res_2098_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__3___redArg(v_msg_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_);
    lean_dec(v___y_2096_);
    lean_dec_ref(v___y_2095_);
    lean_dec(v___y_2094_);
    lean_dec_ref(v___y_2093_);
    return v_res_2098_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___redArg(
    mut v_a_2099_: *mut LeanObject,
    mut v_b_2100_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_array_2101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_2102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_2103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2106_: u8 = 0;
    let mut v___x_2107_: u8 = 0;
    let mut v___x_2108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2116_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_2101_ = lean_ctor_get(v_a_2099_, 0);
                v_start_2102_ = lean_ctor_get(v_a_2099_, 1);
                v_stop_2103_ = lean_ctor_get(v_a_2099_, 2);
                v_isSharedCheck_2116_ = (!lean_is_exclusive(v_a_2099_)) as u8;
                if v_isSharedCheck_2116_ == 0 {
                    v___x_2105_ = v_a_2099_;
                    v_isShared_2106_ = v_isSharedCheck_2116_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_stop_2103_);
                    lean_inc(v_start_2102_);
                    lean_inc(v_array_2101_);
                    lean_dec(v_a_2099_);
                    v___x_2105_ = lean_box(0);
                    v_isShared_2106_ = v_isSharedCheck_2116_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2107_ = lean_nat_dec_lt(v_start_2102_, v_stop_2103_);
                if v___x_2107_ == 0 {
                    lean_del_object(v___x_2105_);
                    lean_dec(v_stop_2103_);
                    lean_dec(v_start_2102_);
                    lean_dec_ref(v_array_2101_);
                    return v_b_2100_;
                } else {
                    v___x_2108_ = lean_unsigned_to_nat(1);
                    v___x_2109_ = lean_nat_add(v_start_2102_, v___x_2108_);
                    lean_inc_ref(v_array_2101_);
                    if v_isShared_2106_ == 0 {
                        lean_ctor_set(v___x_2105_, 1, v___x_2109_);
                        v___x_2111_ = v___x_2105_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2115_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2115_, 0, v_array_2101_);
                        lean_ctor_set(v_reuseFailAlloc_2115_, 1, v___x_2109_);
                        lean_ctor_set(v_reuseFailAlloc_2115_, 2, v_stop_2103_);
                        v___x_2111_ = v_reuseFailAlloc_2115_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2112_ = lean_array_fget(v_array_2101_, v_start_2102_);
                lean_dec(v_start_2102_);
                lean_dec_ref(v_array_2101_);
                v___x_2113_ =
                    l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and(v_b_2100_, v___x_2112_);
                v_a_2099_ = v___x_2111_;
                v_b_2100_ = v___x_2113_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__0()
-> *mut LeanObject {
    let mut v___x_2117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut LeanObject = core::ptr::null_mut();
    v___x_2117_ = lean_box(0);
    v___x_2118_ = lean_unsigned_to_nat(16);
    v___x_2119_ = lean_mk_array(v___x_2118_, v___x_2117_);
    return v___x_2119_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__1()
-> *mut LeanObject {
    let mut v___x_2120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unusedHypotheses_2122_: *mut LeanObject = core::ptr::null_mut();
    v___x_2120_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__0_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__0);
    v___x_2121_ = lean_unsigned_to_nat(0);
    v_unusedHypotheses_2122_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v_unusedHypotheses_2122_, 0, v___x_2121_);
    lean_ctor_set(v_unusedHypotheses_2122_, 1, v___x_2120_);
    return v_unusedHypotheses_2122_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__2()
-> *mut LeanObject {
    let mut v_unusedHypotheses_2123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sats_2124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut LeanObject = core::ptr::null_mut();
    v_unusedHypotheses_2123_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__1_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__1);
    v_sats_2124_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__1;
    v___x_2125_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2125_, 0, v_sats_2124_);
    lean_ctor_set(v___x_2125_, 1, v_unusedHypotheses_2123_);
    return v___x_2125_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__5()
-> *mut LeanObject {
    let mut v___x_2129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut LeanObject = core::ptr::null_mut();
    v___x_2129_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__4;
    v___x_2130_ = l_Lean_MessageData_ofFormat(v___x_2129_);
    return v___x_2130_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV___lam__0(
    mut v___y_2131_: *mut LeanObject,
    mut v___y_2132_: *mut LeanObject,
    mut v___y_2133_: *mut LeanObject,
    mut v___y_2134_: *mut LeanObject,
    mut v___y_2135_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2141_: usize = 0;
    let mut v___x_2142_: usize = 0;
    let mut v___x_2143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2147_: u8 = 0;
    let mut v_fst_2148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: u8 = 0;
    let mut v___x_2152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bvExpr_2156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_2157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2166_: u8 = 0;
    let mut v_a_2167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2170_: u8 = 0;
    let mut v___x_2172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2174_: u8 = 0;
    let mut v_a_2175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2178_: u8 = 0;
    let mut v___x_2180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2182_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2137_ =
                    l_Lean_Meta_getPropHyps(v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_);
                if lean_obj_tag(v___x_2137_) == 0 {
                    v_a_2138_ = lean_ctor_get(v___x_2137_, 0);
                    lean_inc(v_a_2138_);
                    lean_dec_ref_known(v___x_2137_, 1);
                    v___x_2139_ = lean_unsigned_to_nat(0);
                    v___x_2140_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__2_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__2);
                    v_sz_2141_ = lean_array_size(v_a_2138_);
                    v___x_2142_ = 0usize;
                    v___x_2143_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__1(v_a_2138_, v_sz_2141_, v___x_2142_, v___x_2140_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_);
                    lean_dec(v_a_2138_);
                    if lean_obj_tag(v___x_2143_) == 0 {
                        v_a_2144_ = lean_ctor_get(v___x_2143_, 0);
                        v_isSharedCheck_2166_ = (!lean_is_exclusive(v___x_2143_)) as u8;
                        if v_isSharedCheck_2166_ == 0 {
                            v___x_2146_ = v___x_2143_;
                            v_isShared_2147_ = v_isSharedCheck_2166_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2144_);
                            lean_dec(v___x_2143_);
                            v___x_2146_ = lean_box(0);
                            v_isShared_2147_ = v_isSharedCheck_2166_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2167_ = lean_ctor_get(v___x_2143_, 0);
                        v_isSharedCheck_2174_ = (!lean_is_exclusive(v___x_2143_)) as u8;
                        if v_isSharedCheck_2174_ == 0 {
                            v___x_2169_ = v___x_2143_;
                            v_isShared_2170_ = v_isSharedCheck_2174_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2167_);
                            lean_dec(v___x_2143_);
                            v___x_2169_ = lean_box(0);
                            v_isShared_2170_ = v_isSharedCheck_2174_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_2175_ = lean_ctor_get(v___x_2137_, 0);
                    v_isSharedCheck_2182_ = (!lean_is_exclusive(v___x_2137_)) as u8;
                    if v_isSharedCheck_2182_ == 0 {
                        v___x_2177_ = v___x_2137_;
                        v_isShared_2178_ = v_isSharedCheck_2182_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2175_);
                        lean_dec(v___x_2137_);
                        v___x_2177_ = lean_box(0);
                        v_isShared_2178_ = v_isSharedCheck_2182_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_2148_ = lean_ctor_get(v_a_2144_, 0);
                lean_inc(v_fst_2148_);
                v_snd_2149_ = lean_ctor_get(v_a_2144_, 1);
                lean_inc(v_snd_2149_);
                lean_dec(v_a_2144_);
                v___x_2150_ = lean_array_get_size(v_fst_2148_);
                v___x_2151_ = lean_nat_dec_eq(v___x_2150_, v___x_2139_);
                if v___x_2151_ == 0 {
                    v___x_2152_ = lean_array_fget(v_fst_2148_, v___x_2139_);
                    v___x_2153_ = lean_unsigned_to_nat(1);
                    v___x_2154_ =
                        l_Array_toSubarray___redArg(v_fst_2148_, v___x_2153_, v___x_2150_);
                    v___x_2155_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___redArg(v___x_2154_, v___x_2152_);
                    v_bvExpr_2156_ = lean_ctor_get(v___x_2155_, 0);
                    lean_inc_ref(v_bvExpr_2156_);
                    v_expr_2157_ = lean_ctor_get(v___x_2155_, 2);
                    lean_inc_ref(v_expr_2157_);
                    v___x_2158_ = l_Lean_ShareCommon_shareCommon___redArg(v_bvExpr_2156_);
                    v___x_2159_ = lean_alloc_closure(
                        l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___boxed
                            as *mut core::ffi::c_void,
                        8,
                        1,
                    );
                    lean_closure_set(v___x_2159_, 0, v___x_2155_);
                    v___x_2160_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v___x_2160_, 0, v___x_2158_);
                    lean_ctor_set(v___x_2160_, 1, v___x_2159_);
                    lean_ctor_set(v___x_2160_, 2, v_snd_2149_);
                    lean_ctor_set(v___x_2160_, 3, v_expr_2157_);
                    if v_isShared_2147_ == 0 {
                        lean_ctor_set(v___x_2146_, 0, v___x_2160_);
                        v___x_2162_ = v___x_2146_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2163_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2163_, 0, v___x_2160_);
                        v___x_2162_ = v_reuseFailAlloc_2163_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_snd_2149_);
                    lean_dec(v_fst_2148_);
                    lean_del_object(v___x_2146_);
                    v___x_2164_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__5_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__5);
                    v___x_2165_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__3___redArg(v___x_2164_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_);
                    return v___x_2165_;
                }
            }
            2 => {
                return v___x_2162_;
            }
            3 => {
                if v_isShared_2170_ == 0 {
                    v___x_2172_ = v___x_2169_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2173_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2173_, 0, v_a_2167_);
                    v___x_2172_ = v_reuseFailAlloc_2173_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2172_;
            }
            5 => {
                if v_isShared_2178_ == 0 {
                    v___x_2180_ = v___x_2177_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2181_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2181_, 0, v_a_2175_);
                    v___x_2180_ = v_reuseFailAlloc_2181_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2180_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___boxed(
    mut v___y_2183_: *mut LeanObject,
    mut v___y_2184_: *mut LeanObject,
    mut v___y_2185_: *mut LeanObject,
    mut v___y_2186_: *mut LeanObject,
    mut v___y_2187_: *mut LeanObject,
    mut v___y_2188_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2189_: *mut LeanObject = core::ptr::null_mut();
    v_res_2189_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV___lam__0(v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_);
    lean_dec(v___y_2187_);
    lean_dec_ref(v___y_2186_);
    lean_dec(v___y_2185_);
    lean_dec_ref(v___y_2184_);
    lean_dec(v___y_2183_);
    return v_res_2189_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV(
    mut v_g_2191_: *mut LeanObject,
    mut v_a_2192_: *mut LeanObject,
    mut v_a_2193_: *mut LeanObject,
    mut v_a_2194_: *mut LeanObject,
    mut v_a_2195_: *mut LeanObject,
    mut v_a_2196_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut LeanObject = core::ptr::null_mut();
    v___f_2198_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV___closed__0;
    v___x_2199_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__4___redArg(v_g_2191_, v___f_2198_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_);
    return v___x_2199_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV___boxed(
    mut v_g_2200_: *mut LeanObject,
    mut v_a_2201_: *mut LeanObject,
    mut v_a_2202_: *mut LeanObject,
    mut v_a_2203_: *mut LeanObject,
    mut v_a_2204_: *mut LeanObject,
    mut v_a_2205_: *mut LeanObject,
    mut v_a_2206_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2207_: *mut LeanObject = core::ptr::null_mut();
    v_res_2207_ =
        l___private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV(
            v_g_2200_, v_a_2201_, v_a_2202_, v_a_2203_, v_a_2204_, v_a_2205_,
        );
    lean_dec(v_a_2205_);
    lean_dec_ref(v_a_2204_);
    lean_dec(v_a_2203_);
    lean_dec_ref(v_a_2202_);
    lean_dec(v_a_2201_);
    return v_res_2207_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__0(
    mut v_00_u03b2_2208_: *mut LeanObject,
    mut v_m_2209_: *mut LeanObject,
    mut v_a_2210_: *mut LeanObject,
    mut v_b_2211_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2212_: *mut LeanObject = core::ptr::null_mut();
    v___x_2212_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__0___redArg(v_m_2209_, v_a_2210_, v_b_2211_);
    return v___x_2212_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__2(
    mut v_inst_2213_: *mut LeanObject,
    mut v_R_2214_: *mut LeanObject,
    mut v_a_2215_: *mut LeanObject,
    mut v_b_2216_: *mut LeanObject,
    mut v_c_2217_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2218_: *mut LeanObject = core::ptr::null_mut();
    v___x_2218_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___redArg(v_a_2215_, v_b_2216_);
    return v___x_2218_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__3(
    mut v_00_u03b1_2219_: *mut LeanObject,
    mut v_msg_2220_: *mut LeanObject,
    mut v___y_2221_: *mut LeanObject,
    mut v___y_2222_: *mut LeanObject,
    mut v___y_2223_: *mut LeanObject,
    mut v___y_2224_: *mut LeanObject,
    mut v___y_2225_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2227_: *mut LeanObject = core::ptr::null_mut();
    v___x_2227_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__3___redArg(v_msg_2220_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2225_);
    return v___x_2227_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__3___boxed(
    mut v_00_u03b1_2228_: *mut LeanObject,
    mut v_msg_2229_: *mut LeanObject,
    mut v___y_2230_: *mut LeanObject,
    mut v___y_2231_: *mut LeanObject,
    mut v___y_2232_: *mut LeanObject,
    mut v___y_2233_: *mut LeanObject,
    mut v___y_2234_: *mut LeanObject,
    mut v___y_2235_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2236_: *mut LeanObject = core::ptr::null_mut();
    v_res_2236_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__3(v_00_u03b1_2228_, v_msg_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_);
    lean_dec(v___y_2234_);
    lean_dec_ref(v___y_2233_);
    lean_dec(v___y_2232_);
    lean_dec_ref(v___y_2231_);
    lean_dec(v___y_2230_);
    return v_res_2236_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0(
    mut v_00_u03b2_2237_: *mut LeanObject,
    mut v_a_2238_: *mut LeanObject,
    mut v_x_2239_: *mut LeanObject,
) -> u8 {
    let mut v___x_2240_: u8 = 0;
    v___x_2240_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0___redArg(v_a_2238_, v_x_2239_);
    return v___x_2240_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0___boxed(
    mut v_00_u03b2_2241_: *mut LeanObject,
    mut v_a_2242_: *mut LeanObject,
    mut v_x_2243_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2244_: u8 = 0;
    let mut v_r_2245_: *mut LeanObject = core::ptr::null_mut();
    v_res_2244_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0(v_00_u03b2_2241_, v_a_2242_, v_x_2243_);
    lean_dec(v_x_2243_);
    lean_dec(v_a_2242_);
    v_r_2245_ = lean_box((v_res_2244_) as usize);
    return v_r_2245_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1(
    mut v_00_u03b2_2246_: *mut LeanObject,
    mut v_data_2247_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2248_: *mut LeanObject = core::ptr::null_mut();
    v___x_2248_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1___redArg(v_data_2247_);
    return v___x_2248_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1_spec__3(
    mut v_00_u03b2_2249_: *mut LeanObject,
    mut v_i_2250_: *mut LeanObject,
    mut v_source_2251_: *mut LeanObject,
    mut v_target_2252_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2253_: *mut LeanObject = core::ptr::null_mut();
    v___x_2253_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1_spec__3___redArg(v_i_2250_, v_source_2251_, v_target_2252_);
    return v___x_2253_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1_spec__3_spec__8(
    mut v_00_u03b2_2254_: *mut LeanObject,
    mut v_x_2255_: *mut LeanObject,
    mut v_x_2256_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2257_: *mut LeanObject = core::ptr::null_mut();
    v___x_2257_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1_spec__3_spec__8___redArg(v_x_2255_, v_x_2256_);
    return v___x_2257_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_2258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut LeanObject = core::ptr::null_mut();
    v___x_2258_ = lean_unsigned_to_nat(32);
    v___x_2259_ = lean_mk_empty_array_with_capacity(v___x_2258_);
    v___x_2260_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2260_, 0, v___x_2259_);
    return v___x_2260_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_2261_: usize = 0;
    let mut v___x_2262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut LeanObject = core::ptr::null_mut();
    v___x_2261_ = 5usize;
    v___x_2262_ = lean_unsigned_to_nat(0);
    v___x_2263_ = lean_unsigned_to_nat(32);
    v___x_2264_ = lean_mk_empty_array_with_capacity(v___x_2263_);
    v___x_2265_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7___redArg___closed__0_once), _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7___redArg___closed__0);
    v___x_2266_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_2266_, 0, v___x_2265_);
    lean_ctor_set(v___x_2266_, 1, v___x_2264_);
    lean_ctor_set(v___x_2266_, 2, v___x_2262_);
    lean_ctor_set(v___x_2266_, 3, v___x_2262_);
    lean_ctor_set_usize(v___x_2266_, 4, v___x_2261_);
    return v___x_2266_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7___redArg(
    mut v___y_2267_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_2270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traces_2271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_2273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_2276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_2278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_2279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_2280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2284_: u8 = 0;
    let mut v_tid_2285_: u64 = 0;
    let mut v___x_2287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2288_: u8 = 0;
    let mut v___x_2289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2298_: u8 = 0;
    let mut v_unused_2299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2300_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2269_ = lean_st_ref_get(v___y_2267_);
                v_traceState_2270_ = lean_ctor_get(v___x_2269_, 4);
                lean_inc_ref(v_traceState_2270_);
                lean_dec(v___x_2269_);
                v_traces_2271_ = lean_ctor_get(v_traceState_2270_, 0);
                lean_inc_ref(v_traces_2271_);
                lean_dec_ref(v_traceState_2270_);
                v___x_2272_ = lean_st_ref_take(v___y_2267_);
                v_traceState_2273_ = lean_ctor_get(v___x_2272_, 4);
                v_env_2274_ = lean_ctor_get(v___x_2272_, 0);
                v_nextMacroScope_2275_ = lean_ctor_get(v___x_2272_, 1);
                v_ngen_2276_ = lean_ctor_get(v___x_2272_, 2);
                v_auxDeclNGen_2277_ = lean_ctor_get(v___x_2272_, 3);
                v_cache_2278_ = lean_ctor_get(v___x_2272_, 5);
                v_messages_2279_ = lean_ctor_get(v___x_2272_, 6);
                v_infoState_2280_ = lean_ctor_get(v___x_2272_, 7);
                v_snapshotTasks_2281_ = lean_ctor_get(v___x_2272_, 8);
                v_isSharedCheck_2300_ = (!lean_is_exclusive(v___x_2272_)) as u8;
                if v_isSharedCheck_2300_ == 0 {
                    v___x_2283_ = v___x_2272_;
                    v_isShared_2284_ = v_isSharedCheck_2300_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_2281_);
                    lean_inc(v_infoState_2280_);
                    lean_inc(v_messages_2279_);
                    lean_inc(v_cache_2278_);
                    lean_inc(v_traceState_2273_);
                    lean_inc(v_auxDeclNGen_2277_);
                    lean_inc(v_ngen_2276_);
                    lean_inc(v_nextMacroScope_2275_);
                    lean_inc(v_env_2274_);
                    lean_dec(v___x_2272_);
                    v___x_2283_ = lean_box(0);
                    v_isShared_2284_ = v_isSharedCheck_2300_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_tid_2285_ = lean_ctor_get_uint64(
                    v_traceState_2273_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_2298_ = (!lean_is_exclusive(v_traceState_2273_)) as u8;
                if v_isSharedCheck_2298_ == 0 {
                    v_unused_2299_ = lean_ctor_get(v_traceState_2273_, 0);
                    lean_dec(v_unused_2299_);
                    v___x_2287_ = v_traceState_2273_;
                    v_isShared_2288_ = v_isSharedCheck_2298_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_traceState_2273_);
                    v___x_2287_ = lean_box(0);
                    v_isShared_2288_ = v_isSharedCheck_2298_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2289_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7___redArg___closed__1_once), _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7___redArg___closed__1);
                if v_isShared_2288_ == 0 {
                    lean_ctor_set(v___x_2287_, 0, v___x_2289_);
                    v___x_2291_ = v___x_2287_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2297_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2297_, 0, v___x_2289_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_2297_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_2285_,
                    );
                    v___x_2291_ = v_reuseFailAlloc_2297_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2284_ == 0 {
                    lean_ctor_set(v___x_2283_, 4, v___x_2291_);
                    v___x_2293_ = v___x_2283_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2296_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2296_, 0, v_env_2274_);
                    lean_ctor_set(v_reuseFailAlloc_2296_, 1, v_nextMacroScope_2275_);
                    lean_ctor_set(v_reuseFailAlloc_2296_, 2, v_ngen_2276_);
                    lean_ctor_set(v_reuseFailAlloc_2296_, 3, v_auxDeclNGen_2277_);
                    lean_ctor_set(v_reuseFailAlloc_2296_, 4, v___x_2291_);
                    lean_ctor_set(v_reuseFailAlloc_2296_, 5, v_cache_2278_);
                    lean_ctor_set(v_reuseFailAlloc_2296_, 6, v_messages_2279_);
                    lean_ctor_set(v_reuseFailAlloc_2296_, 7, v_infoState_2280_);
                    lean_ctor_set(v_reuseFailAlloc_2296_, 8, v_snapshotTasks_2281_);
                    v___x_2293_ = v_reuseFailAlloc_2296_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2294_ = lean_st_ref_set(v___y_2267_, v___x_2293_);
                v___x_2295_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2295_, 0, v_traces_2271_);
                return v___x_2295_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7___redArg___boxed(
    mut v___y_2301_: *mut LeanObject,
    mut v___y_2302_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2303_: *mut LeanObject = core::ptr::null_mut();
    v_res_2303_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7___redArg(v___y_2301_);
    lean_dec(v___y_2301_);
    return v_res_2303_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7(
    mut v___y_2304_: *mut LeanObject,
    mut v___y_2305_: *mut LeanObject,
    mut v___y_2306_: *mut LeanObject,
    mut v___y_2307_: *mut LeanObject,
    mut v___y_2308_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2310_: *mut LeanObject = core::ptr::null_mut();
    v___x_2310_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7___redArg(v___y_2308_);
    return v___x_2310_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7___boxed(
    mut v___y_2311_: *mut LeanObject,
    mut v___y_2312_: *mut LeanObject,
    mut v___y_2313_: *mut LeanObject,
    mut v___y_2314_: *mut LeanObject,
    mut v___y_2315_: *mut LeanObject,
    mut v___y_2316_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2317_: *mut LeanObject = core::ptr::null_mut();
    v_res_2317_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7(v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_);
    lean_dec(v___y_2315_);
    lean_dec_ref(v___y_2314_);
    lean_dec(v___y_2313_);
    lean_dec_ref(v___y_2312_);
    lean_dec(v___y_2311_);
    return v_res_2317_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8(
    mut v_opts_2318_: *mut LeanObject,
    mut v_opt_2319_: *mut LeanObject,
) -> u8 {
    let mut v_name_2320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_2321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_2322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut LeanObject = core::ptr::null_mut();
    v_name_2320_ = lean_ctor_get(v_opt_2319_, 0);
    v_defValue_2321_ = lean_ctor_get(v_opt_2319_, 1);
    v_map_2322_ = lean_ctor_get(v_opts_2318_, 0);
    v___x_2323_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2322_,
            v_name_2320_,
        );
    if lean_obj_tag(v___x_2323_) == 0 {
        let mut v___x_2324_: u8 = 0;
        v___x_2324_ = (lean_unbox(v_defValue_2321_) as u8);
        return v___x_2324_;
    } else {
        let mut v_val_2325_: *mut LeanObject = core::ptr::null_mut();
        v_val_2325_ = lean_ctor_get(v___x_2323_, 0);
        lean_inc(v_val_2325_);
        lean_dec_ref_known(v___x_2323_, 1);
        if lean_obj_tag(v_val_2325_) == 1 {
            let mut v_v_2326_: u8 = 0;
            v_v_2326_ = lean_ctor_get_uint8(v_val_2325_, 0 as u32);
            lean_dec_ref_known(v_val_2325_, 0);
            return v_v_2326_;
        } else {
            let mut v___x_2327_: u8 = 0;
            lean_dec(v_val_2325_);
            v___x_2327_ = (lean_unbox(v_defValue_2321_) as u8);
            return v___x_2327_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8___boxed(
    mut v_opts_2328_: *mut LeanObject,
    mut v_opt_2329_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2330_: u8 = 0;
    let mut v_r_2331_: *mut LeanObject = core::ptr::null_mut();
    v_res_2330_ =
        l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8(
            v_opts_2328_,
            v_opt_2329_,
        );
    lean_dec_ref(v_opt_2329_);
    lean_dec_ref(v_opts_2328_);
    v_r_2331_ = lean_box((v_res_2330_) as usize);
    return v_r_2331_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__2()
-> *mut LeanObject {
    let mut v___x_2335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut LeanObject = core::ptr::null_mut();
    v___x_2335_ = l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__1;
    v___x_2336_ = l_Lean_MessageData_ofFormat(v___x_2335_);
    return v___x_2336_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0(
    mut v_x_2337_: *mut LeanObject,
    mut v___y_2338_: *mut LeanObject,
    mut v___y_2339_: *mut LeanObject,
    mut v___y_2340_: *mut LeanObject,
    mut v___y_2341_: *mut LeanObject,
    mut v___y_2342_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: *mut LeanObject = core::ptr::null_mut();
    v___x_2344_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__2_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__2,
    );
    v___x_2345_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2345_, 0, v___x_2344_);
    return v___x_2345_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___boxed(
    mut v_x_2346_: *mut LeanObject,
    mut v___y_2347_: *mut LeanObject,
    mut v___y_2348_: *mut LeanObject,
    mut v___y_2349_: *mut LeanObject,
    mut v___y_2350_: *mut LeanObject,
    mut v___y_2351_: *mut LeanObject,
    mut v___y_2352_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2353_: *mut LeanObject = core::ptr::null_mut();
    v_res_2353_ = l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0(
        v_x_2346_,
        v___y_2347_,
        v___y_2348_,
        v___y_2349_,
        v___y_2350_,
        v___y_2351_,
    );
    lean_dec(v___y_2351_);
    lean_dec_ref(v___y_2350_);
    lean_dec(v___y_2349_);
    lean_dec_ref(v___y_2348_);
    lean_dec(v___y_2347_);
    lean_dec_ref(v_x_2346_);
    return v_res_2353_;
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__15(
    mut v_opts_2354_: *mut LeanObject,
    mut v_opt_2355_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_2356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_2357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_2358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut LeanObject = core::ptr::null_mut();
    v_name_2356_ = lean_ctor_get(v_opt_2355_, 0);
    v_defValue_2357_ = lean_ctor_get(v_opt_2355_, 1);
    v_map_2358_ = lean_ctor_get(v_opts_2354_, 0);
    v___x_2359_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2358_,
            v_name_2356_,
        );
    if lean_obj_tag(v___x_2359_) == 0 {
        lean_inc(v_defValue_2357_);
        return v_defValue_2357_;
    } else {
        let mut v_val_2360_: *mut LeanObject = core::ptr::null_mut();
        v_val_2360_ = lean_ctor_get(v___x_2359_, 0);
        lean_inc(v_val_2360_);
        lean_dec_ref_known(v___x_2359_, 1);
        if lean_obj_tag(v_val_2360_) == 3 {
            let mut v_v_2361_: *mut LeanObject = core::ptr::null_mut();
            v_v_2361_ = lean_ctor_get(v_val_2360_, 0);
            lean_inc(v_v_2361_);
            lean_dec_ref_known(v_val_2360_, 1);
            return v_v_2361_;
        } else {
            lean_dec(v_val_2360_);
            lean_inc(v_defValue_2357_);
            return v_defValue_2357_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__15___boxed(
    mut v_opts_2362_: *mut LeanObject,
    mut v_opt_2363_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2364_: *mut LeanObject = core::ptr::null_mut();
    v_res_2364_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__15(v_opts_2362_, v_opt_2363_);
    lean_dec_ref(v_opt_2363_);
    lean_dec_ref(v_opts_2362_);
    return v_res_2364_;
}
pub unsafe fn l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__12(
    mut v_e_2365_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_e_2365_) == 0 {
        let mut v___x_2366_: u8 = 0;
        v___x_2366_ = 2;
        return v___x_2366_;
    } else {
        let mut v___x_2367_: u8 = 0;
        v___x_2367_ = 0;
        return v___x_2367_;
    }
}
pub unsafe fn l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__12___boxed(
    mut v_e_2368_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2369_: u8 = 0;
    let mut v_r_2370_: *mut LeanObject = core::ptr::null_mut();
    v_res_2369_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__12(v_e_2368_);
    lean_dec_ref(v_e_2368_);
    v_r_2370_ = lean_box((v_res_2369_) as usize);
    return v_r_2370_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__14___redArg(
    mut v_x_2371_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2376_: u8 = 0;
    let mut v___x_2378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2380_: u8 = 0;
    let mut v_a_2381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2384_: u8 = 0;
    let mut v___x_2386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2388_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2371_) == 0 {
                    v_a_2373_ = lean_ctor_get(v_x_2371_, 0);
                    v_isSharedCheck_2380_ = (!lean_is_exclusive(v_x_2371_)) as u8;
                    if v_isSharedCheck_2380_ == 0 {
                        v___x_2375_ = v_x_2371_;
                        v_isShared_2376_ = v_isSharedCheck_2380_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2373_);
                        lean_dec(v_x_2371_);
                        v___x_2375_ = lean_box(0);
                        v_isShared_2376_ = v_isSharedCheck_2380_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2381_ = lean_ctor_get(v_x_2371_, 0);
                    v_isSharedCheck_2388_ = (!lean_is_exclusive(v_x_2371_)) as u8;
                    if v_isSharedCheck_2388_ == 0 {
                        v___x_2383_ = v_x_2371_;
                        v_isShared_2384_ = v_isSharedCheck_2388_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2381_);
                        lean_dec(v_x_2371_);
                        v___x_2383_ = lean_box(0);
                        v_isShared_2384_ = v_isSharedCheck_2388_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2376_ == 0 {
                    lean_ctor_set_tag(v___x_2375_, 1);
                    v___x_2378_ = v___x_2375_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2379_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2379_, 0, v_a_2373_);
                    v___x_2378_ = v_reuseFailAlloc_2379_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2378_;
            }
            3 => {
                if v_isShared_2384_ == 0 {
                    lean_ctor_set_tag(v___x_2383_, 0);
                    v___x_2386_ = v___x_2383_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2387_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2387_, 0, v_a_2381_);
                    v___x_2386_ = v_reuseFailAlloc_2387_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2386_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__14___redArg___boxed(
    mut v_x_2389_: *mut LeanObject,
    mut v___y_2390_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2391_: *mut LeanObject = core::ptr::null_mut();
    v_res_2391_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__14___redArg(v_x_2389_);
    return v_res_2391_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__13_spec__18(
    mut v_sz_2392_: usize,
    mut v_i_2393_: usize,
    mut v_bs_2394_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2395_: u8 = 0;
    let mut v_v_2396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msg_2397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2400_: usize = 0;
    let mut v___x_2401_: usize = 0;
    let mut v___x_2402_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2395_ = lean_usize_dec_lt(v_i_2393_, v_sz_2392_);
                if v___x_2395_ == 0 {
                    return v_bs_2394_;
                } else {
                    v_v_2396_ = lean_array_uget_borrowed(v_bs_2394_, v_i_2393_);
                    v_msg_2397_ = lean_ctor_get(v_v_2396_, 1);
                    lean_inc_ref(v_msg_2397_);
                    v___x_2398_ = lean_unsigned_to_nat(0);
                    v_bs_x27_2399_ = lean_array_uset(v_bs_2394_, v_i_2393_, v___x_2398_);
                    v___x_2400_ = 1usize;
                    v___x_2401_ = lean_usize_add(v_i_2393_, v___x_2400_);
                    v___x_2402_ = lean_array_uset(v_bs_x27_2399_, v_i_2393_, v_msg_2397_);
                    v_i_2393_ = v___x_2401_;
                    v_bs_2394_ = v___x_2402_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__13_spec__18___boxed(
    mut v_sz_2404_: *mut LeanObject,
    mut v_i_2405_: *mut LeanObject,
    mut v_bs_2406_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2407_: usize = 0;
    let mut v_i_boxed_2408_: usize = 0;
    let mut v_res_2409_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2407_ = lean_unbox_usize(v_sz_2404_);
    lean_dec(v_sz_2404_);
    v_i_boxed_2408_ = lean_unbox_usize(v_i_2405_);
    lean_dec(v_i_2405_);
    v_res_2409_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__13_spec__18(v_sz_boxed_2407_, v_i_boxed_2408_, v_bs_2406_);
    return v_res_2409_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__13___redArg(
    mut v_oldTraces_2410_: *mut LeanObject,
    mut v_data_2411_: *mut LeanObject,
    mut v_ref_2412_: *mut LeanObject,
    mut v_msg_2413_: *mut LeanObject,
    mut v___y_2414_: *mut LeanObject,
    mut v___y_2415_: *mut LeanObject,
    mut v___y_2416_: *mut LeanObject,
    mut v___y_2417_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_2419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_2427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_2428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_2431_: u8 = 0;
    let mut v_cancelTk_x3f_2432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2433_: u8 = 0;
    let mut v_inheritedTraceOptions_2434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_2436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traces_2437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2441_: usize = 0;
    let mut v___x_2442_: usize = 0;
    let mut v___x_2443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msg_2444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2449_: u8 = 0;
    let mut v___x_2450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_2451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_2454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_2456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_2457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_2458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2462_: u8 = 0;
    let mut v_tid_2463_: u64 = 0;
    let mut v___x_2465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2466_: u8 = 0;
    let mut v___x_2467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2480_: u8 = 0;
    let mut v_unused_2481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2482_: u8 = 0;
    let mut v_isSharedCheck_2483_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_2419_ = lean_ctor_get(v___y_2416_, 0);
                v_fileMap_2420_ = lean_ctor_get(v___y_2416_, 1);
                v_options_2421_ = lean_ctor_get(v___y_2416_, 2);
                v_currRecDepth_2422_ = lean_ctor_get(v___y_2416_, 3);
                v_maxRecDepth_2423_ = lean_ctor_get(v___y_2416_, 4);
                v_ref_2424_ = lean_ctor_get(v___y_2416_, 5);
                v_currNamespace_2425_ = lean_ctor_get(v___y_2416_, 6);
                v_openDecls_2426_ = lean_ctor_get(v___y_2416_, 7);
                v_initHeartbeats_2427_ = lean_ctor_get(v___y_2416_, 8);
                v_maxHeartbeats_2428_ = lean_ctor_get(v___y_2416_, 9);
                v_quotContext_2429_ = lean_ctor_get(v___y_2416_, 10);
                v_currMacroScope_2430_ = lean_ctor_get(v___y_2416_, 11);
                v_diag_2431_ = lean_ctor_get_uint8(
                    v___y_2416_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_2432_ = lean_ctor_get(v___y_2416_, 12);
                v_suppressElabErrors_2433_ = lean_ctor_get_uint8(
                    v___y_2416_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_2434_ = lean_ctor_get(v___y_2416_, 13);
                v___x_2435_ = lean_st_ref_get(v___y_2417_);
                v_traceState_2436_ = lean_ctor_get(v___x_2435_, 4);
                lean_inc_ref(v_traceState_2436_);
                lean_dec(v___x_2435_);
                v_traces_2437_ = lean_ctor_get(v_traceState_2436_, 0);
                lean_inc_ref(v_traces_2437_);
                lean_dec_ref(v_traceState_2436_);
                v_ref_2438_ = l_Lean_replaceRef(v_ref_2412_, v_ref_2424_);
                lean_inc_ref(v_inheritedTraceOptions_2434_);
                lean_inc(v_cancelTk_x3f_2432_);
                lean_inc(v_currMacroScope_2430_);
                lean_inc(v_quotContext_2429_);
                lean_inc(v_maxHeartbeats_2428_);
                lean_inc(v_initHeartbeats_2427_);
                lean_inc(v_openDecls_2426_);
                lean_inc(v_currNamespace_2425_);
                lean_inc(v_maxRecDepth_2423_);
                lean_inc(v_currRecDepth_2422_);
                lean_inc_ref(v_options_2421_);
                lean_inc_ref(v_fileMap_2420_);
                lean_inc_ref(v_fileName_2419_);
                v___x_2439_ = lean_alloc_ctor(0, 14, (2) as u32);
                lean_ctor_set(v___x_2439_, 0, v_fileName_2419_);
                lean_ctor_set(v___x_2439_, 1, v_fileMap_2420_);
                lean_ctor_set(v___x_2439_, 2, v_options_2421_);
                lean_ctor_set(v___x_2439_, 3, v_currRecDepth_2422_);
                lean_ctor_set(v___x_2439_, 4, v_maxRecDepth_2423_);
                lean_ctor_set(v___x_2439_, 5, v_ref_2438_);
                lean_ctor_set(v___x_2439_, 6, v_currNamespace_2425_);
                lean_ctor_set(v___x_2439_, 7, v_openDecls_2426_);
                lean_ctor_set(v___x_2439_, 8, v_initHeartbeats_2427_);
                lean_ctor_set(v___x_2439_, 9, v_maxHeartbeats_2428_);
                lean_ctor_set(v___x_2439_, 10, v_quotContext_2429_);
                lean_ctor_set(v___x_2439_, 11, v_currMacroScope_2430_);
                lean_ctor_set(v___x_2439_, 12, v_cancelTk_x3f_2432_);
                lean_ctor_set(v___x_2439_, 13, v_inheritedTraceOptions_2434_);
                lean_ctor_set_uint8(
                    v___x_2439_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    v_diag_2431_,
                );
                lean_ctor_set_uint8(
                    v___x_2439_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_2433_,
                );
                v___x_2440_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2437_);
                lean_dec_ref(v_traces_2437_);
                v_sz_2441_ = lean_array_size(v___x_2440_);
                v___x_2442_ = 0usize;
                v___x_2443_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__13_spec__18(v_sz_2441_, v___x_2442_, v___x_2440_);
                v_msg_2444_ = lean_alloc_ctor(9, 3, (0) as u32);
                lean_ctor_set(v_msg_2444_, 0, v_data_2411_);
                lean_ctor_set(v_msg_2444_, 1, v_msg_2413_);
                lean_ctor_set(v_msg_2444_, 2, v___x_2443_);
                v___x_2445_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__3_spec__5(v_msg_2444_, v___y_2414_, v___y_2415_, v___x_2439_, v___y_2417_);
                lean_dec_ref_known(v___x_2439_, 14);
                v_a_2446_ = lean_ctor_get(v___x_2445_, 0);
                v_isSharedCheck_2483_ = (!lean_is_exclusive(v___x_2445_)) as u8;
                if v_isSharedCheck_2483_ == 0 {
                    v___x_2448_ = v___x_2445_;
                    v_isShared_2449_ = v_isSharedCheck_2483_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_2446_);
                    lean_dec(v___x_2445_);
                    v___x_2448_ = lean_box(0);
                    v_isShared_2449_ = v_isSharedCheck_2483_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2450_ = lean_st_ref_take(v___y_2417_);
                v_traceState_2451_ = lean_ctor_get(v___x_2450_, 4);
                v_env_2452_ = lean_ctor_get(v___x_2450_, 0);
                v_nextMacroScope_2453_ = lean_ctor_get(v___x_2450_, 1);
                v_ngen_2454_ = lean_ctor_get(v___x_2450_, 2);
                v_auxDeclNGen_2455_ = lean_ctor_get(v___x_2450_, 3);
                v_cache_2456_ = lean_ctor_get(v___x_2450_, 5);
                v_messages_2457_ = lean_ctor_get(v___x_2450_, 6);
                v_infoState_2458_ = lean_ctor_get(v___x_2450_, 7);
                v_snapshotTasks_2459_ = lean_ctor_get(v___x_2450_, 8);
                v_isSharedCheck_2482_ = (!lean_is_exclusive(v___x_2450_)) as u8;
                if v_isSharedCheck_2482_ == 0 {
                    v___x_2461_ = v___x_2450_;
                    v_isShared_2462_ = v_isSharedCheck_2482_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_2459_);
                    lean_inc(v_infoState_2458_);
                    lean_inc(v_messages_2457_);
                    lean_inc(v_cache_2456_);
                    lean_inc(v_traceState_2451_);
                    lean_inc(v_auxDeclNGen_2455_);
                    lean_inc(v_ngen_2454_);
                    lean_inc(v_nextMacroScope_2453_);
                    lean_inc(v_env_2452_);
                    lean_dec(v___x_2450_);
                    v___x_2461_ = lean_box(0);
                    v_isShared_2462_ = v_isSharedCheck_2482_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_2463_ = lean_ctor_get_uint64(
                    v_traceState_2451_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_2480_ = (!lean_is_exclusive(v_traceState_2451_)) as u8;
                if v_isSharedCheck_2480_ == 0 {
                    v_unused_2481_ = lean_ctor_get(v_traceState_2451_, 0);
                    lean_dec(v_unused_2481_);
                    v___x_2465_ = v_traceState_2451_;
                    v_isShared_2466_ = v_isSharedCheck_2480_;
                    state = 3;
                    continue;
                } else {
                    lean_dec(v_traceState_2451_);
                    v___x_2465_ = lean_box(0);
                    v_isShared_2466_ = v_isSharedCheck_2480_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2467_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2467_, 0, v_ref_2412_);
                lean_ctor_set(v___x_2467_, 1, v_a_2446_);
                v___x_2468_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2410_, v___x_2467_);
                if v_isShared_2466_ == 0 {
                    lean_ctor_set(v___x_2465_, 0, v___x_2468_);
                    v___x_2470_ = v___x_2465_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2479_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2479_, 0, v___x_2468_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_2479_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_2463_,
                    );
                    v___x_2470_ = v_reuseFailAlloc_2479_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2462_ == 0 {
                    lean_ctor_set(v___x_2461_, 4, v___x_2470_);
                    v___x_2472_ = v___x_2461_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2478_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2478_, 0, v_env_2452_);
                    lean_ctor_set(v_reuseFailAlloc_2478_, 1, v_nextMacroScope_2453_);
                    lean_ctor_set(v_reuseFailAlloc_2478_, 2, v_ngen_2454_);
                    lean_ctor_set(v_reuseFailAlloc_2478_, 3, v_auxDeclNGen_2455_);
                    lean_ctor_set(v_reuseFailAlloc_2478_, 4, v___x_2470_);
                    lean_ctor_set(v_reuseFailAlloc_2478_, 5, v_cache_2456_);
                    lean_ctor_set(v_reuseFailAlloc_2478_, 6, v_messages_2457_);
                    lean_ctor_set(v_reuseFailAlloc_2478_, 7, v_infoState_2458_);
                    lean_ctor_set(v_reuseFailAlloc_2478_, 8, v_snapshotTasks_2459_);
                    v___x_2472_ = v_reuseFailAlloc_2478_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2473_ = lean_st_ref_set(v___y_2417_, v___x_2472_);
                v___x_2474_ = lean_box(0);
                if v_isShared_2449_ == 0 {
                    lean_ctor_set(v___x_2448_, 0, v___x_2474_);
                    v___x_2476_ = v___x_2448_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2477_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2477_, 0, v___x_2474_);
                    v___x_2476_ = v_reuseFailAlloc_2477_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2476_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__13___redArg___boxed(
    mut v_oldTraces_2484_: *mut LeanObject,
    mut v_data_2485_: *mut LeanObject,
    mut v_ref_2486_: *mut LeanObject,
    mut v_msg_2487_: *mut LeanObject,
    mut v___y_2488_: *mut LeanObject,
    mut v___y_2489_: *mut LeanObject,
    mut v___y_2490_: *mut LeanObject,
    mut v___y_2491_: *mut LeanObject,
    mut v___y_2492_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2493_: *mut LeanObject = core::ptr::null_mut();
    v_res_2493_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__13___redArg(v_oldTraces_2484_, v_data_2485_, v_ref_2486_, v_msg_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_);
    lean_dec(v___y_2491_);
    lean_dec_ref(v___y_2490_);
    lean_dec(v___y_2489_);
    lean_dec_ref(v___y_2488_);
    return v_res_2493_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__1()
-> *mut LeanObject {
    let mut v___x_2495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: *mut LeanObject = core::ptr::null_mut();
    v___x_2495_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__0;
    v___x_2496_ = l_Lean_stringToMessageData(v___x_2495_);
    return v___x_2496_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__2()
-> f64 {
    let mut v___x_2497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2498_: f64 = 0.0;
    v___x_2497_ = lean_unsigned_to_nat(0);
    v___x_2498_ = lean_float_of_nat(v___x_2497_);
    return v___x_2498_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__4()
-> *mut LeanObject {
    let mut v___x_2500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut LeanObject = core::ptr::null_mut();
    v___x_2500_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__3;
    v___x_2501_ = l_Lean_stringToMessageData(v___x_2500_);
    return v___x_2501_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__5()
-> f64 {
    let mut v___x_2502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2503_: f64 = 0.0;
    v___x_2502_ = lean_unsigned_to_nat(1000);
    v___x_2503_ = lean_float_of_nat(v___x_2502_);
    return v___x_2503_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9(
    mut v_cls_2504_: *mut LeanObject,
    mut v_collapsed_2505_: u8,
    mut v_tag_2506_: *mut LeanObject,
    mut v_opts_2507_: *mut LeanObject,
    mut v_clsEnabled_2508_: u8,
    mut v_oldTraces_2509_: *mut LeanObject,
    mut v_msg_2510_: *mut LeanObject,
    mut v_resStartStop_2511_: *mut LeanObject,
    mut v___y_2512_: *mut LeanObject,
    mut v___y_2513_: *mut LeanObject,
    mut v___y_2514_: *mut LeanObject,
    mut v___y_2515_: *mut LeanObject,
    mut v___y_2516_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_2518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2522_: u8 = 0;
    let mut v___y_2524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_2526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2532_: u8 = 0;
    let mut v___x_2534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2536_: u8 = 0;
    let mut v_fst_2537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2541_: u8 = 0;
    let mut v___x_2542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: u8 = 0;
    let mut v___y_2545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_result_2547_: u8 = 0;
    let mut v___x_2548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_m_2554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: f64 = 0.0;
    let mut v_data_2558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_2559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: f64 = 0.0;
    let mut v___x_2561_: f64 = 0.0;
    let mut v_reuseFailAlloc_2562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2570_: u8 = 0;
    let mut v___x_2571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_2572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_2575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_2577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_2578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_2579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2583_: u8 = 0;
    let mut v_tid_2584_: u64 = 0;
    let mut v_traces_2585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2588_: u8 = 0;
    let mut v___x_2589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2598_: u8 = 0;
    let mut v_isSharedCheck_2599_: u8 = 0;
    let mut v___y_2601_: f64 = 0.0;
    let mut v___x_2602_: f64 = 0.0;
    let mut v___x_2603_: f64 = 0.0;
    let mut v___x_2604_: f64 = 0.0;
    let mut v___x_2605_: u8 = 0;
    let mut v___x_2606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: u8 = 0;
    let mut v___x_2608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2610_: f64 = 0.0;
    let mut v___x_2611_: f64 = 0.0;
    let mut v___x_2612_: f64 = 0.0;
    let mut v___x_2613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2615_: f64 = 0.0;
    let mut v_isSharedCheck_2616_: u8 = 0;
    let mut v_isSharedCheck_2617_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2518_ = lean_ctor_get(v_resStartStop_2511_, 0);
                v_snd_2519_ = lean_ctor_get(v_resStartStop_2511_, 1);
                v_isSharedCheck_2617_ = (!lean_is_exclusive(v_resStartStop_2511_)) as u8;
                if v_isSharedCheck_2617_ == 0 {
                    v___x_2521_ = v_resStartStop_2511_;
                    v_isShared_2522_ = v_isSharedCheck_2617_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_2519_);
                    lean_inc(v_fst_2518_);
                    lean_dec(v_resStartStop_2511_);
                    v___x_2521_ = lean_box(0);
                    v_isShared_2522_ = v_isSharedCheck_2617_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_2537_ = lean_ctor_get(v_snd_2519_, 0);
                v_snd_2538_ = lean_ctor_get(v_snd_2519_, 1);
                v_isSharedCheck_2616_ = (!lean_is_exclusive(v_snd_2519_)) as u8;
                if v_isSharedCheck_2616_ == 0 {
                    v___x_2540_ = v_snd_2519_;
                    v_isShared_2541_ = v_isSharedCheck_2616_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_snd_2538_);
                    lean_inc(v_fst_2537_);
                    lean_dec(v_snd_2519_);
                    v___x_2540_ = lean_box(0);
                    v_isShared_2541_ = v_isSharedCheck_2616_;
                    state = 5;
                    continue;
                }
            }
            2 => {
                lean_inc(v___y_2524_);
                v___x_2527_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__13___redArg(v_oldTraces_2509_, v_data_2526_, v___y_2524_, v___y_2525_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_);
                if lean_obj_tag(v___x_2527_) == 0 {
                    lean_dec_ref_known(v___x_2527_, 1);
                    v___x_2528_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__14___redArg(v_fst_2518_);
                    return v___x_2528_;
                } else {
                    lean_dec(v_fst_2518_);
                    v_a_2529_ = lean_ctor_get(v___x_2527_, 0);
                    v_isSharedCheck_2536_ = (!lean_is_exclusive(v___x_2527_)) as u8;
                    if v_isSharedCheck_2536_ == 0 {
                        v___x_2531_ = v___x_2527_;
                        v_isShared_2532_ = v_isSharedCheck_2536_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2529_);
                        lean_dec(v___x_2527_);
                        v___x_2531_ = lean_box(0);
                        v_isShared_2532_ = v_isSharedCheck_2536_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_2532_ == 0 {
                    v___x_2534_ = v___x_2531_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2535_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2535_, 0, v_a_2529_);
                    v___x_2534_ = v_reuseFailAlloc_2535_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2534_;
            }
            5 => {
                v___x_2542_ = l_Lean_trace_profiler;
                v___x_2543_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8(v_opts_2507_, v___x_2542_);
                if v___x_2543_ == 0 {
                    v___y_2570_ = v___x_2543_;
                    state = 10;
                    continue;
                } else {
                    v___x_2606_ = l_Lean_trace_profiler_useHeartbeats;
                    v___x_2607_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8(v_opts_2507_, v___x_2606_);
                    if v___x_2607_ == 0 {
                        v___x_2608_ = l_Lean_trace_profiler_threshold;
                        v___x_2609_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__15(v_opts_2507_, v___x_2608_);
                        v___x_2610_ = lean_float_of_nat(v___x_2609_);
                        v___x_2611_ = lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__5_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__5);
                        v___x_2612_ = lean_float_div(v___x_2610_, v___x_2611_);
                        v___y_2601_ = v___x_2612_;
                        state = 15;
                        continue;
                    } else {
                        v___x_2613_ = l_Lean_trace_profiler_threshold;
                        v___x_2614_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__15(v_opts_2507_, v___x_2613_);
                        v___x_2615_ = lean_float_of_nat(v___x_2614_);
                        v___y_2601_ = v___x_2615_;
                        state = 15;
                        continue;
                    }
                }
            }
            6 => {
                v_result_2547_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__12(v_fst_2518_);
                v___x_2548_ = l_Lean_TraceResult_toEmoji(v_result_2547_);
                v___x_2549_ = l_Lean_stringToMessageData(v___x_2548_);
                v___x_2550_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__1_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__1);
                if v_isShared_2541_ == 0 {
                    lean_ctor_set_tag(v___x_2540_, 7);
                    lean_ctor_set(v___x_2540_, 1, v___x_2550_);
                    lean_ctor_set(v___x_2540_, 0, v___x_2549_);
                    v___x_2552_ = v___x_2540_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2563_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2563_, 0, v___x_2549_);
                    lean_ctor_set(v_reuseFailAlloc_2563_, 1, v___x_2550_);
                    v___x_2552_ = v_reuseFailAlloc_2563_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2522_ == 0 {
                    lean_ctor_set_tag(v___x_2521_, 7);
                    lean_ctor_set(v___x_2521_, 1, v_a_2546_);
                    lean_ctor_set(v___x_2521_, 0, v___x_2552_);
                    v_m_2554_ = v___x_2521_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2562_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2562_, 0, v___x_2552_);
                    lean_ctor_set(v_reuseFailAlloc_2562_, 1, v_a_2546_);
                    v_m_2554_ = v_reuseFailAlloc_2562_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2555_ = lean_box((v_result_2547_) as usize);
                v___x_2556_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2556_, 0, v___x_2555_);
                v___x_2557_ = lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__2_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__2);
                lean_inc_ref(v_tag_2506_);
                lean_inc_ref(v___x_2556_);
                lean_inc(v_cls_2504_);
                v_data_2558_ = lean_alloc_ctor(0, 3, (17) as u32);
                lean_ctor_set(v_data_2558_, 0, v_cls_2504_);
                lean_ctor_set(v_data_2558_, 1, v___x_2556_);
                lean_ctor_set(v_data_2558_, 2, v_tag_2506_);
                lean_ctor_set_float(
                    v_data_2558_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_2557_,
                );
                lean_ctor_set_float(
                    v_data_2558_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    v___x_2557_,
                );
                lean_ctor_set_uint8(
                    v_data_2558_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                    v_collapsed_2505_,
                );
                if v___x_2543_ == 0 {
                    lean_dec_ref_known(v___x_2556_, 1);
                    lean_dec(v_snd_2538_);
                    lean_dec(v_fst_2537_);
                    lean_dec_ref(v_tag_2506_);
                    lean_dec(v_cls_2504_);
                    v___y_2524_ = v___y_2545_;
                    v___y_2525_ = v_m_2554_;
                    v_data_2526_ = v_data_2558_;
                    state = 2;
                    continue;
                } else {
                    lean_dec_ref_known(v_data_2558_, 3);
                    v_data_2559_ = lean_alloc_ctor(0, 3, (17) as u32);
                    lean_ctor_set(v_data_2559_, 0, v_cls_2504_);
                    lean_ctor_set(v_data_2559_, 1, v___x_2556_);
                    lean_ctor_set(v_data_2559_, 2, v_tag_2506_);
                    v___x_2560_ = lean_unbox_float(v_fst_2537_);
                    lean_dec(v_fst_2537_);
                    lean_ctor_set_float(
                        v_data_2559_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v___x_2560_,
                    );
                    v___x_2561_ = lean_unbox_float(v_snd_2538_);
                    lean_dec(v_snd_2538_);
                    lean_ctor_set_float(
                        v_data_2559_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                        v___x_2561_,
                    );
                    lean_ctor_set_uint8(
                        v_data_2559_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                        v_collapsed_2505_,
                    );
                    v___y_2524_ = v___y_2545_;
                    v___y_2525_ = v_m_2554_;
                    v_data_2526_ = v_data_2559_;
                    state = 2;
                    continue;
                }
            }
            9 => {
                v_ref_2565_ = lean_ctor_get(v___y_2515_, 5);
                lean_inc(v___y_2516_);
                lean_inc_ref(v___y_2515_);
                lean_inc(v___y_2514_);
                lean_inc_ref(v___y_2513_);
                lean_inc(v___y_2512_);
                lean_inc(v_fst_2518_);
                v___x_2566_ = lean_apply_7(
                    v_msg_2510_,
                    v_fst_2518_,
                    v___y_2512_,
                    v___y_2513_,
                    v___y_2514_,
                    v___y_2515_,
                    v___y_2516_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_2566_) == 0 {
                    v_a_2567_ = lean_ctor_get(v___x_2566_, 0);
                    lean_inc(v_a_2567_);
                    lean_dec_ref_known(v___x_2566_, 1);
                    v___y_2545_ = v_ref_2565_;
                    v_a_2546_ = v_a_2567_;
                    state = 6;
                    continue;
                } else {
                    lean_dec_ref_known(v___x_2566_, 1);
                    v___x_2568_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__4_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__4);
                    v___y_2545_ = v_ref_2565_;
                    v_a_2546_ = v___x_2568_;
                    state = 6;
                    continue;
                }
            }
            10 => {
                if v_clsEnabled_2508_ == 0 {
                    if v___y_2570_ == 0 {
                        lean_del_object(v___x_2540_);
                        lean_dec(v_snd_2538_);
                        lean_dec(v_fst_2537_);
                        lean_del_object(v___x_2521_);
                        lean_dec_ref(v_msg_2510_);
                        lean_dec_ref(v_tag_2506_);
                        lean_dec(v_cls_2504_);
                        v___x_2571_ = lean_st_ref_take(v___y_2516_);
                        v_traceState_2572_ = lean_ctor_get(v___x_2571_, 4);
                        v_env_2573_ = lean_ctor_get(v___x_2571_, 0);
                        v_nextMacroScope_2574_ = lean_ctor_get(v___x_2571_, 1);
                        v_ngen_2575_ = lean_ctor_get(v___x_2571_, 2);
                        v_auxDeclNGen_2576_ = lean_ctor_get(v___x_2571_, 3);
                        v_cache_2577_ = lean_ctor_get(v___x_2571_, 5);
                        v_messages_2578_ = lean_ctor_get(v___x_2571_, 6);
                        v_infoState_2579_ = lean_ctor_get(v___x_2571_, 7);
                        v_snapshotTasks_2580_ = lean_ctor_get(v___x_2571_, 8);
                        v_isSharedCheck_2599_ = (!lean_is_exclusive(v___x_2571_)) as u8;
                        if v_isSharedCheck_2599_ == 0 {
                            v___x_2582_ = v___x_2571_;
                            v_isShared_2583_ = v_isSharedCheck_2599_;
                            state = 11;
                            continue;
                        } else {
                            lean_inc(v_snapshotTasks_2580_);
                            lean_inc(v_infoState_2579_);
                            lean_inc(v_messages_2578_);
                            lean_inc(v_cache_2577_);
                            lean_inc(v_traceState_2572_);
                            lean_inc(v_auxDeclNGen_2576_);
                            lean_inc(v_ngen_2575_);
                            lean_inc(v_nextMacroScope_2574_);
                            lean_inc(v_env_2573_);
                            lean_dec(v___x_2571_);
                            v___x_2582_ = lean_box(0);
                            v_isShared_2583_ = v_isSharedCheck_2599_;
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
                v_tid_2584_ = lean_ctor_get_uint64(
                    v_traceState_2572_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_traces_2585_ = lean_ctor_get(v_traceState_2572_, 0);
                v_isSharedCheck_2598_ = (!lean_is_exclusive(v_traceState_2572_)) as u8;
                if v_isSharedCheck_2598_ == 0 {
                    v___x_2587_ = v_traceState_2572_;
                    v_isShared_2588_ = v_isSharedCheck_2598_;
                    state = 12;
                    continue;
                } else {
                    lean_inc(v_traces_2585_);
                    lean_dec(v_traceState_2572_);
                    v___x_2587_ = lean_box(0);
                    v_isShared_2588_ = v_isSharedCheck_2598_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_2589_ =
                    l_Lean_PersistentArray_append___redArg(v_oldTraces_2509_, v_traces_2585_);
                lean_dec_ref(v_traces_2585_);
                if v_isShared_2588_ == 0 {
                    lean_ctor_set(v___x_2587_, 0, v___x_2589_);
                    v___x_2591_ = v___x_2587_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2597_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2597_, 0, v___x_2589_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_2597_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_2584_,
                    );
                    v___x_2591_ = v_reuseFailAlloc_2597_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_2583_ == 0 {
                    lean_ctor_set(v___x_2582_, 4, v___x_2591_);
                    v___x_2593_ = v___x_2582_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2596_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2596_, 0, v_env_2573_);
                    lean_ctor_set(v_reuseFailAlloc_2596_, 1, v_nextMacroScope_2574_);
                    lean_ctor_set(v_reuseFailAlloc_2596_, 2, v_ngen_2575_);
                    lean_ctor_set(v_reuseFailAlloc_2596_, 3, v_auxDeclNGen_2576_);
                    lean_ctor_set(v_reuseFailAlloc_2596_, 4, v___x_2591_);
                    lean_ctor_set(v_reuseFailAlloc_2596_, 5, v_cache_2577_);
                    lean_ctor_set(v_reuseFailAlloc_2596_, 6, v_messages_2578_);
                    lean_ctor_set(v_reuseFailAlloc_2596_, 7, v_infoState_2579_);
                    lean_ctor_set(v_reuseFailAlloc_2596_, 8, v_snapshotTasks_2580_);
                    v___x_2593_ = v_reuseFailAlloc_2596_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_2594_ = lean_st_ref_set(v___y_2516_, v___x_2593_);
                v___x_2595_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__14___redArg(v_fst_2518_);
                return v___x_2595_;
            }
            15 => {
                v___x_2602_ = lean_unbox_float(v_snd_2538_);
                v___x_2603_ = lean_unbox_float(v_fst_2537_);
                v___x_2604_ = lean_float_sub(v___x_2602_, v___x_2603_);
                v___x_2605_ = lean_float_decLt(v___y_2601_, v___x_2604_);
                v___y_2570_ = v___x_2605_;
                state = 10;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___boxed(
    mut v_cls_2618_: *mut LeanObject,
    mut v_collapsed_2619_: *mut LeanObject,
    mut v_tag_2620_: *mut LeanObject,
    mut v_opts_2621_: *mut LeanObject,
    mut v_clsEnabled_2622_: *mut LeanObject,
    mut v_oldTraces_2623_: *mut LeanObject,
    mut v_msg_2624_: *mut LeanObject,
    mut v_resStartStop_2625_: *mut LeanObject,
    mut v___y_2626_: *mut LeanObject,
    mut v___y_2627_: *mut LeanObject,
    mut v___y_2628_: *mut LeanObject,
    mut v___y_2629_: *mut LeanObject,
    mut v___y_2630_: *mut LeanObject,
    mut v___y_2631_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_collapsed_boxed_2632_: u8 = 0;
    let mut v_clsEnabled_boxed_2633_: u8 = 0;
    let mut v_res_2634_: *mut LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_2632_ = (lean_unbox(v_collapsed_2619_) as u8);
    v_clsEnabled_boxed_2633_ = (lean_unbox(v_clsEnabled_2622_) as u8);
    v_res_2634_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9(v_cls_2618_, v_collapsed_boxed_2632_, v_tag_2620_, v_opts_2621_, v_clsEnabled_boxed_2633_, v_oldTraces_2623_, v_msg_2624_, v_resStartStop_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_);
    lean_dec(v___y_2630_);
    lean_dec_ref(v___y_2629_);
    lean_dec(v___y_2628_);
    lean_dec_ref(v___y_2627_);
    lean_dec(v___y_2626_);
    lean_dec_ref(v_opts_2621_);
    return v_res_2634_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3(
    mut v_x_2635_: *mut LeanObject,
    mut v_x_2636_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_2636_) == 0 {
        lean_inc(v_x_2635_);
        return v_x_2635_;
    } else {
        let mut v_key_2637_: *mut LeanObject = core::ptr::null_mut();
        let mut v_value_2638_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_2639_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2640_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2641_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2642_: *mut LeanObject = core::ptr::null_mut();
        v_key_2637_ = lean_ctor_get(v_x_2636_, 0);
        v_value_2638_ = lean_ctor_get(v_x_2636_, 1);
        v_tail_2639_ = lean_ctor_get(v_x_2636_, 2);
        v___x_2640_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3(v_x_2635_, v_tail_2639_);
        lean_inc(v_value_2638_);
        lean_inc(v_key_2637_);
        v___x_2641_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2641_, 0, v_key_2637_);
        lean_ctor_set(v___x_2641_, 1, v_value_2638_);
        v___x_2642_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_2642_, 0, v___x_2641_);
        lean_ctor_set(v___x_2642_, 1, v___x_2640_);
        return v___x_2642_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3___boxed(
    mut v_x_2643_: *mut LeanObject,
    mut v_x_2644_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2645_: *mut LeanObject = core::ptr::null_mut();
    v_res_2645_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3(v_x_2643_, v_x_2644_);
    lean_dec(v_x_2644_);
    lean_dec(v_x_2643_);
    return v_res_2645_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4(
    mut v_as_2646_: *mut LeanObject,
    mut v_i_2647_: usize,
    mut v_stop_2648_: usize,
    mut v_b_2649_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2650_: u8 = 0;
    let mut v___x_2651_: usize = 0;
    let mut v___x_2652_: usize = 0;
    let mut v___x_2653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2650_ = lean_usize_dec_eq(v_i_2647_, v_stop_2648_);
                if v___x_2650_ == 0 {
                    v___x_2651_ = 1usize;
                    v___x_2652_ = lean_usize_sub(v_i_2647_, v___x_2651_);
                    v___x_2653_ = lean_array_uget_borrowed(v_as_2646_, v___x_2652_);
                    v___x_2654_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3(v_b_2649_, v___x_2653_);
                    lean_dec(v_b_2649_);
                    v_i_2647_ = v___x_2652_;
                    v_b_2649_ = v___x_2654_;
                    state = 0;
                    continue;
                } else {
                    return v_b_2649_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___boxed(
    mut v_as_2656_: *mut LeanObject,
    mut v_i_2657_: *mut LeanObject,
    mut v_stop_2658_: *mut LeanObject,
    mut v_b_2659_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2660_: usize = 0;
    let mut v_stop_boxed_2661_: usize = 0;
    let mut v_res_2662_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2660_ = lean_unbox_usize(v_i_2657_);
    lean_dec(v_i_2657_);
    v_stop_boxed_2661_ = lean_unbox_usize(v_stop_2658_);
    lean_dec(v_stop_2658_);
    v_res_2662_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4(v_as_2656_, v_i_boxed_2660_, v_stop_boxed_2661_, v_b_2659_);
    lean_dec_ref(v_as_2656_);
    return v_res_2662_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5(
    mut v_x_2669_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_2669_) {
        0 => {
            let mut v_a_2670_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2671_: *mut LeanObject = core::ptr::null_mut();
            v_a_2670_ = lean_ctor_get(v_x_2669_, 0);
            lean_inc(v_a_2670_);
            lean_dec_ref_known(v_x_2669_, 1);
            v___x_2671_ = l_Std_Tactic_BVDecide_BVPred_toString(v_a_2670_);
            return v___x_2671_;
        }
        1 => {
            let mut v_a_2672_: u8 = 0;
            v_a_2672_ = lean_ctor_get_uint8(v_x_2669_, 0 as u32);
            lean_dec_ref_known(v_x_2669_, 0);
            if v_a_2672_ == 0 {
                let mut v___x_2673_: *mut LeanObject = core::ptr::null_mut();
                v___x_2673_ = l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__0;
                return v___x_2673_;
            } else {
                let mut v___x_2674_: *mut LeanObject = core::ptr::null_mut();
                v___x_2674_ = l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__1;
                return v___x_2674_;
            }
        }
        2 => {
            let mut v_a_2675_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2676_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2677_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2678_: *mut LeanObject = core::ptr::null_mut();
            v_a_2675_ = lean_ctor_get(v_x_2669_, 0);
            lean_inc_ref(v_a_2675_);
            lean_dec_ref_known(v_x_2669_, 1);
            v___x_2676_ = l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__2;
            v___x_2677_ = l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5(v_a_2675_);
            v___x_2678_ = lean_string_append(v___x_2676_, v___x_2677_);
            lean_dec_ref(v___x_2677_);
            return v___x_2678_;
        }
        3 => {
            let mut v_a_2679_: u8 = 0;
            let mut v_a_2680_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_2681_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2682_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2683_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2684_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2685_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2686_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2687_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2688_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2689_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2690_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2691_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2692_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2693_: *mut LeanObject = core::ptr::null_mut();
            v_a_2679_ = lean_ctor_get_uint8(
                v_x_2669_,
                (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
            );
            v_a_2680_ = lean_ctor_get(v_x_2669_, 0);
            lean_inc_ref(v_a_2680_);
            v_a_2681_ = lean_ctor_get(v_x_2669_, 1);
            lean_inc_ref(v_a_2681_);
            lean_dec_ref_known(v_x_2669_, 2);
            v___x_2682_ = l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__3;
            v___x_2683_ = l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5(v_a_2680_);
            v___x_2684_ = lean_string_append(v___x_2682_, v___x_2683_);
            lean_dec_ref(v___x_2683_);
            v___x_2685_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__0;
            v___x_2686_ = lean_string_append(v___x_2684_, v___x_2685_);
            v___x_2687_ = l_Std_Tactic_BVDecide_Gate_toString(v_a_2679_);
            v___x_2688_ = lean_string_append(v___x_2686_, v___x_2687_);
            lean_dec_ref(v___x_2687_);
            v___x_2689_ = lean_string_append(v___x_2688_, v___x_2685_);
            v___x_2690_ = l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5(v_a_2681_);
            v___x_2691_ = lean_string_append(v___x_2689_, v___x_2690_);
            lean_dec_ref(v___x_2690_);
            v___x_2692_ = l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__4;
            v___x_2693_ = lean_string_append(v___x_2691_, v___x_2692_);
            return v___x_2693_;
        }
        _ => {
            let mut v_a_2694_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_2695_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_2696_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2697_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2698_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2699_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2700_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2701_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2702_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2703_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2704_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2705_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2706_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2707_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2708_: *mut LeanObject = core::ptr::null_mut();
            v_a_2694_ = lean_ctor_get(v_x_2669_, 0);
            lean_inc_ref(v_a_2694_);
            v_a_2695_ = lean_ctor_get(v_x_2669_, 1);
            lean_inc_ref(v_a_2695_);
            v_a_2696_ = lean_ctor_get(v_x_2669_, 2);
            lean_inc_ref(v_a_2696_);
            lean_dec_ref_known(v_x_2669_, 3);
            v___x_2697_ = l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__5;
            v___x_2698_ = l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5(v_a_2694_);
            v___x_2699_ = lean_string_append(v___x_2697_, v___x_2698_);
            lean_dec_ref(v___x_2698_);
            v___x_2700_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__0;
            v___x_2701_ = lean_string_append(v___x_2699_, v___x_2700_);
            v___x_2702_ = l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5(v_a_2695_);
            v___x_2703_ = lean_string_append(v___x_2701_, v___x_2702_);
            lean_dec_ref(v___x_2702_);
            v___x_2704_ = lean_string_append(v___x_2703_, v___x_2700_);
            v___x_2705_ = l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5(v_a_2696_);
            v___x_2706_ = lean_string_append(v___x_2704_, v___x_2705_);
            lean_dec_ref(v___x_2705_);
            v___x_2707_ = l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__4;
            v___x_2708_ = lean_string_append(v___x_2706_, v___x_2707_);
            return v___x_2708_;
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__4___redArg(
    mut v_a_2709_: *mut LeanObject,
    mut v_x_2710_: *mut LeanObject,
) -> u8 {
    let mut v___x_2711_: u8 = 0;
    let mut v_key_2712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2710_) == 0 {
                    v___x_2711_ = 0;
                    return v___x_2711_;
                } else {
                    v_key_2712_ = lean_ctor_get(v_x_2710_, 0);
                    v_tail_2713_ = lean_ctor_get(v_x_2710_, 2);
                    v___x_2714_ = lean_nat_dec_eq(v_key_2712_, v_a_2709_);
                    if v___x_2714_ == 0 {
                        v_x_2710_ = v_tail_2713_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2714_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__4___redArg___boxed(
    mut v_a_2716_: *mut LeanObject,
    mut v_x_2717_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2718_: u8 = 0;
    let mut v_r_2719_: *mut LeanObject = core::ptr::null_mut();
    v_res_2718_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__4___redArg(v_a_2716_, v_x_2717_);
    lean_dec(v_x_2717_);
    lean_dec(v_a_2716_);
    v_r_2719_ = lean_box((v_res_2718_) as usize);
    return v_r_2719_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__6___redArg(
    mut v_a_2720_: *mut LeanObject,
    mut v_b_2721_: *mut LeanObject,
    mut v_x_2722_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_2723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2728_: u8 = 0;
    let mut v___x_2729_: u8 = 0;
    let mut v___x_2730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2737_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2722_) == 0 {
                    lean_dec(v_b_2721_);
                    lean_dec(v_a_2720_);
                    return v_x_2722_;
                } else {
                    v_key_2723_ = lean_ctor_get(v_x_2722_, 0);
                    v_value_2724_ = lean_ctor_get(v_x_2722_, 1);
                    v_tail_2725_ = lean_ctor_get(v_x_2722_, 2);
                    v_isSharedCheck_2737_ = (!lean_is_exclusive(v_x_2722_)) as u8;
                    if v_isSharedCheck_2737_ == 0 {
                        v___x_2727_ = v_x_2722_;
                        v_isShared_2728_ = v_isSharedCheck_2737_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2725_);
                        lean_inc(v_value_2724_);
                        lean_inc(v_key_2723_);
                        lean_dec(v_x_2722_);
                        v___x_2727_ = lean_box(0);
                        v_isShared_2728_ = v_isSharedCheck_2737_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2729_ = lean_nat_dec_eq(v_key_2723_, v_a_2720_);
                if v___x_2729_ == 0 {
                    v___x_2730_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__6___redArg(v_a_2720_, v_b_2721_, v_tail_2725_);
                    if v_isShared_2728_ == 0 {
                        lean_ctor_set(v___x_2727_, 2, v___x_2730_);
                        v___x_2732_ = v___x_2727_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2733_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2733_, 0, v_key_2723_);
                        lean_ctor_set(v_reuseFailAlloc_2733_, 1, v_value_2724_);
                        lean_ctor_set(v_reuseFailAlloc_2733_, 2, v___x_2730_);
                        v___x_2732_ = v_reuseFailAlloc_2733_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_value_2724_);
                    lean_dec(v_key_2723_);
                    if v_isShared_2728_ == 0 {
                        lean_ctor_set(v___x_2727_, 1, v_b_2721_);
                        lean_ctor_set(v___x_2727_, 0, v_a_2720_);
                        v___x_2735_ = v___x_2727_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2736_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2736_, 0, v_a_2720_);
                        lean_ctor_set(v_reuseFailAlloc_2736_, 1, v_b_2721_);
                        lean_ctor_set(v_reuseFailAlloc_2736_, 2, v_tail_2725_);
                        v___x_2735_ = v_reuseFailAlloc_2736_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2732_;
            }
            3 => {
                return v___x_2735_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__5_spec__15_spec__19___redArg(
    mut v_x_2738_: *mut LeanObject,
    mut v_x_2739_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_2740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2745_: u8 = 0;
    let mut v___x_2746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: u64 = 0;
    let mut v___x_2748_: u64 = 0;
    let mut v___x_2749_: u64 = 0;
    let mut v_fold_2750_: u64 = 0;
    let mut v___x_2751_: u64 = 0;
    let mut v___x_2752_: u64 = 0;
    let mut v___x_2753_: u64 = 0;
    let mut v___x_2754_: usize = 0;
    let mut v___x_2755_: usize = 0;
    let mut v___x_2756_: usize = 0;
    let mut v___x_2757_: usize = 0;
    let mut v___x_2758_: usize = 0;
    let mut v___x_2759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2765_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2739_) == 0 {
                    return v_x_2738_;
                } else {
                    v_key_2740_ = lean_ctor_get(v_x_2739_, 0);
                    v_value_2741_ = lean_ctor_get(v_x_2739_, 1);
                    v_tail_2742_ = lean_ctor_get(v_x_2739_, 2);
                    v_isSharedCheck_2765_ = (!lean_is_exclusive(v_x_2739_)) as u8;
                    if v_isSharedCheck_2765_ == 0 {
                        v___x_2744_ = v_x_2739_;
                        v_isShared_2745_ = v_isSharedCheck_2765_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2742_);
                        lean_inc(v_value_2741_);
                        lean_inc(v_key_2740_);
                        lean_dec(v_x_2739_);
                        v___x_2744_ = lean_box(0);
                        v_isShared_2745_ = v_isSharedCheck_2765_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2746_ = lean_array_get_size(v_x_2738_);
                v___x_2747_ = lean_uint64_of_nat(v_key_2740_);
                v___x_2748_ = 32u64;
                v___x_2749_ = lean_uint64_shift_right(v___x_2747_, v___x_2748_);
                v_fold_2750_ = lean_uint64_xor(v___x_2747_, v___x_2749_);
                v___x_2751_ = 16u64;
                v___x_2752_ = lean_uint64_shift_right(v_fold_2750_, v___x_2751_);
                v___x_2753_ = lean_uint64_xor(v_fold_2750_, v___x_2752_);
                v___x_2754_ = lean_uint64_to_usize(v___x_2753_);
                v___x_2755_ = lean_usize_of_nat(v___x_2746_);
                v___x_2756_ = 1usize;
                v___x_2757_ = lean_usize_sub(v___x_2755_, v___x_2756_);
                v___x_2758_ = lean_usize_land(v___x_2754_, v___x_2757_);
                v___x_2759_ = lean_array_uget_borrowed(v_x_2738_, v___x_2758_);
                lean_inc(v___x_2759_);
                if v_isShared_2745_ == 0 {
                    lean_ctor_set(v___x_2744_, 2, v___x_2759_);
                    v___x_2761_ = v___x_2744_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2764_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2764_, 0, v_key_2740_);
                    lean_ctor_set(v_reuseFailAlloc_2764_, 1, v_value_2741_);
                    lean_ctor_set(v_reuseFailAlloc_2764_, 2, v___x_2759_);
                    v___x_2761_ = v_reuseFailAlloc_2764_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2762_ = lean_array_uset(v_x_2738_, v___x_2758_, v___x_2761_);
                v_x_2738_ = v___x_2762_;
                v_x_2739_ = v_tail_2742_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__5_spec__15___redArg(
    mut v_i_2766_: *mut LeanObject,
    mut v_source_2767_: *mut LeanObject,
    mut v_target_2768_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: u8 = 0;
    let mut v_es_2771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_2773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_2774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2776_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2769_ = lean_array_get_size(v_source_2767_);
                v___x_2770_ = lean_nat_dec_lt(v_i_2766_, v___x_2769_);
                if v___x_2770_ == 0 {
                    lean_dec_ref(v_source_2767_);
                    lean_dec(v_i_2766_);
                    return v_target_2768_;
                } else {
                    v_es_2771_ = lean_array_fget(v_source_2767_, v_i_2766_);
                    v___x_2772_ = lean_box(0);
                    v_source_2773_ = lean_array_fset(v_source_2767_, v_i_2766_, v___x_2772_);
                    v_target_2774_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__5_spec__15_spec__19___redArg(v_target_2768_, v_es_2771_);
                    v___x_2775_ = lean_unsigned_to_nat(1);
                    v___x_2776_ = lean_nat_add(v_i_2766_, v___x_2775_);
                    lean_dec(v_i_2766_);
                    v_i_2766_ = v___x_2776_;
                    v_source_2767_ = v_source_2773_;
                    v_target_2768_ = v_target_2774_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__5___redArg(
    mut v_data_2778_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_2781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2785_: *mut LeanObject = core::ptr::null_mut();
    v___x_2779_ = lean_array_get_size(v_data_2778_);
    v___x_2780_ = lean_unsigned_to_nat(2);
    v_nbuckets_2781_ = lean_nat_mul(v___x_2779_, v___x_2780_);
    v___x_2782_ = lean_unsigned_to_nat(0);
    v___x_2783_ = lean_box(0);
    v___x_2784_ = lean_mk_array(v_nbuckets_2781_, v___x_2783_);
    v___x_2785_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__5_spec__15___redArg(v___x_2782_, v_data_2778_, v___x_2784_);
    return v___x_2785_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1___redArg(
    mut v_m_2786_: *mut LeanObject,
    mut v_a_2787_: *mut LeanObject,
    mut v_b_2788_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_2789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_2790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2793_: u8 = 0;
    let mut v___x_2794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: u64 = 0;
    let mut v___x_2796_: u64 = 0;
    let mut v___x_2797_: u64 = 0;
    let mut v_fold_2798_: u64 = 0;
    let mut v___x_2799_: u64 = 0;
    let mut v___x_2800_: u64 = 0;
    let mut v___x_2801_: u64 = 0;
    let mut v___x_2802_: usize = 0;
    let mut v___x_2803_: usize = 0;
    let mut v___x_2804_: usize = 0;
    let mut v___x_2805_: usize = 0;
    let mut v___x_2806_: usize = 0;
    let mut v_bkt_2807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2808_: u8 = 0;
    let mut v___x_2809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: u8 = 0;
    let mut v_val_2819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2833_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2789_ = lean_ctor_get(v_m_2786_, 0);
                v_buckets_2790_ = lean_ctor_get(v_m_2786_, 1);
                v_isSharedCheck_2833_ = (!lean_is_exclusive(v_m_2786_)) as u8;
                if v_isSharedCheck_2833_ == 0 {
                    v___x_2792_ = v_m_2786_;
                    v_isShared_2793_ = v_isSharedCheck_2833_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buckets_2790_);
                    lean_inc(v_size_2789_);
                    lean_dec(v_m_2786_);
                    v___x_2792_ = lean_box(0);
                    v_isShared_2793_ = v_isSharedCheck_2833_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2794_ = lean_array_get_size(v_buckets_2790_);
                v___x_2795_ = lean_uint64_of_nat(v_a_2787_);
                v___x_2796_ = 32u64;
                v___x_2797_ = lean_uint64_shift_right(v___x_2795_, v___x_2796_);
                v_fold_2798_ = lean_uint64_xor(v___x_2795_, v___x_2797_);
                v___x_2799_ = 16u64;
                v___x_2800_ = lean_uint64_shift_right(v_fold_2798_, v___x_2799_);
                v___x_2801_ = lean_uint64_xor(v_fold_2798_, v___x_2800_);
                v___x_2802_ = lean_uint64_to_usize(v___x_2801_);
                v___x_2803_ = lean_usize_of_nat(v___x_2794_);
                v___x_2804_ = 1usize;
                v___x_2805_ = lean_usize_sub(v___x_2803_, v___x_2804_);
                v___x_2806_ = lean_usize_land(v___x_2802_, v___x_2805_);
                v_bkt_2807_ = lean_array_uget_borrowed(v_buckets_2790_, v___x_2806_);
                v___x_2808_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__4___redArg(v_a_2787_, v_bkt_2807_);
                if v___x_2808_ == 0 {
                    v___x_2809_ = lean_unsigned_to_nat(1);
                    v_size_x27_2810_ = lean_nat_add(v_size_2789_, v___x_2809_);
                    lean_dec(v_size_2789_);
                    lean_inc(v_bkt_2807_);
                    v___x_2811_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_2811_, 0, v_a_2787_);
                    lean_ctor_set(v___x_2811_, 1, v_b_2788_);
                    lean_ctor_set(v___x_2811_, 2, v_bkt_2807_);
                    v_buckets_x27_2812_ =
                        lean_array_uset(v_buckets_2790_, v___x_2806_, v___x_2811_);
                    v___x_2813_ = lean_unsigned_to_nat(4);
                    v___x_2814_ = lean_nat_mul(v_size_x27_2810_, v___x_2813_);
                    v___x_2815_ = lean_unsigned_to_nat(3);
                    v___x_2816_ = lean_nat_div(v___x_2814_, v___x_2815_);
                    lean_dec(v___x_2814_);
                    v___x_2817_ = lean_array_get_size(v_buckets_x27_2812_);
                    v___x_2818_ = lean_nat_dec_le(v___x_2816_, v___x_2817_);
                    lean_dec(v___x_2816_);
                    if v___x_2818_ == 0 {
                        v_val_2819_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__5___redArg(v_buckets_x27_2812_);
                        if v_isShared_2793_ == 0 {
                            lean_ctor_set(v___x_2792_, 1, v_val_2819_);
                            lean_ctor_set(v___x_2792_, 0, v_size_x27_2810_);
                            v___x_2821_ = v___x_2792_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_2822_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2822_, 0, v_size_x27_2810_);
                            lean_ctor_set(v_reuseFailAlloc_2822_, 1, v_val_2819_);
                            v___x_2821_ = v_reuseFailAlloc_2822_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_2793_ == 0 {
                            lean_ctor_set(v___x_2792_, 1, v_buckets_x27_2812_);
                            lean_ctor_set(v___x_2792_, 0, v_size_x27_2810_);
                            v___x_2824_ = v___x_2792_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2825_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2825_, 0, v_size_x27_2810_);
                            lean_ctor_set(v_reuseFailAlloc_2825_, 1, v_buckets_x27_2812_);
                            v___x_2824_ = v_reuseFailAlloc_2825_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_inc(v_bkt_2807_);
                    v___x_2826_ = lean_box(0);
                    v_buckets_x27_2827_ =
                        lean_array_uset(v_buckets_2790_, v___x_2806_, v___x_2826_);
                    v___x_2828_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__6___redArg(v_a_2787_, v_b_2788_, v_bkt_2807_);
                    v___x_2829_ = lean_array_uset(v_buckets_x27_2827_, v___x_2806_, v___x_2828_);
                    if v_isShared_2793_ == 0 {
                        lean_ctor_set(v___x_2792_, 1, v___x_2829_);
                        v___x_2831_ = v___x_2792_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2832_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2832_, 0, v_size_2789_);
                        lean_ctor_set(v_reuseFailAlloc_2832_, 1, v___x_2829_);
                        v___x_2831_ = v_reuseFailAlloc_2832_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2821_;
            }
            3 => {
                return v___x_2824_;
            }
            4 => {
                return v___x_2831_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__2___redArg(
    mut v_as_x27_2834_: *mut LeanObject,
    mut v_b_2835_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_2836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2840_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_2834_) == 0 {
                    return v_b_2835_;
                } else {
                    v_head_2836_ = lean_ctor_get(v_as_x27_2834_, 0);
                    v_tail_2837_ = lean_ctor_get(v_as_x27_2834_, 1);
                    v_fst_2838_ = lean_ctor_get(v_head_2836_, 0);
                    v_snd_2839_ = lean_ctor_get(v_head_2836_, 1);
                    lean_inc(v_snd_2839_);
                    lean_inc(v_fst_2838_);
                    v_r_2840_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1___redArg(v_b_2835_, v_fst_2838_, v_snd_2839_);
                    v_as_x27_2834_ = v_tail_2837_;
                    v_b_2835_ = v_r_2840_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__2___redArg___boxed(
    mut v_as_x27_2842_: *mut LeanObject,
    mut v_b_2843_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2844_: *mut LeanObject = core::ptr::null_mut();
    v_res_2844_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__2___redArg(v_as_x27_2842_, v_b_2843_);
    lean_dec(v_as_x27_2842_);
    return v_res_2844_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1(
    mut v_m_2845_: *mut LeanObject,
    mut v_l_2846_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2847_: *mut LeanObject = core::ptr::null_mut();
    v___x_2847_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__2___redArg(v_l_2846_, v_m_2845_);
    return v___x_2847_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1___boxed(
    mut v_m_2848_: *mut LeanObject,
    mut v_l_2849_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2850_: *mut LeanObject = core::ptr::null_mut();
    v_res_2850_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1(v_m_2848_, v_l_2849_);
    lean_dec(v_l_2849_);
    return v_res_2850_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10_spec__20_spec__23___redArg(
    mut v_x_2851_: *mut LeanObject,
    mut v_x_2852_: *mut LeanObject,
    mut v_x_2853_: *mut LeanObject,
    mut v_x_2854_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_2855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2859_: u8 = 0;
    let mut v___x_2860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: u8 = 0;
    let mut v___x_2862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: u8 = 0;
    let mut v___x_2870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2880_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_2855_ = lean_ctor_get(v_x_2851_, 0);
                v_vs_2856_ = lean_ctor_get(v_x_2851_, 1);
                v_isSharedCheck_2880_ = (!lean_is_exclusive(v_x_2851_)) as u8;
                if v_isSharedCheck_2880_ == 0 {
                    v___x_2858_ = v_x_2851_;
                    v_isShared_2859_ = v_isSharedCheck_2880_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_2856_);
                    lean_inc(v_ks_2855_);
                    lean_dec(v_x_2851_);
                    v___x_2858_ = lean_box(0);
                    v_isShared_2859_ = v_isSharedCheck_2880_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2860_ = lean_array_get_size(v_ks_2855_);
                v___x_2861_ = lean_nat_dec_lt(v_x_2852_, v___x_2860_);
                if v___x_2861_ == 0 {
                    lean_dec(v_x_2852_);
                    v___x_2862_ = lean_array_push(v_ks_2855_, v_x_2853_);
                    v___x_2863_ = lean_array_push(v_vs_2856_, v_x_2854_);
                    if v_isShared_2859_ == 0 {
                        lean_ctor_set(v___x_2858_, 1, v___x_2863_);
                        lean_ctor_set(v___x_2858_, 0, v___x_2862_);
                        v___x_2865_ = v___x_2858_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2866_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2866_, 0, v___x_2862_);
                        lean_ctor_set(v_reuseFailAlloc_2866_, 1, v___x_2863_);
                        v___x_2865_ = v_reuseFailAlloc_2866_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_2867_ = lean_array_fget_borrowed(v_ks_2855_, v_x_2852_);
                    v___x_2868_ = l_Lean_instBEqMVarId_beq(v_x_2853_, v_k_x27_2867_);
                    if v___x_2868_ == 0 {
                        if v_isShared_2859_ == 0 {
                            v___x_2870_ = v___x_2858_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2874_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2874_, 0, v_ks_2855_);
                            lean_ctor_set(v_reuseFailAlloc_2874_, 1, v_vs_2856_);
                            v___x_2870_ = v_reuseFailAlloc_2874_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_2875_ = lean_array_fset(v_ks_2855_, v_x_2852_, v_x_2853_);
                        v___x_2876_ = lean_array_fset(v_vs_2856_, v_x_2852_, v_x_2854_);
                        lean_dec(v_x_2852_);
                        if v_isShared_2859_ == 0 {
                            lean_ctor_set(v___x_2858_, 1, v___x_2876_);
                            lean_ctor_set(v___x_2858_, 0, v___x_2875_);
                            v___x_2878_ = v___x_2858_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2879_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2879_, 0, v___x_2875_);
                            lean_ctor_set(v_reuseFailAlloc_2879_, 1, v___x_2876_);
                            v___x_2878_ = v_reuseFailAlloc_2879_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_2865_;
            }
            3 => {
                v___x_2871_ = lean_unsigned_to_nat(1);
                v___x_2872_ = lean_nat_add(v_x_2852_, v___x_2871_);
                lean_dec(v_x_2852_);
                v_x_2851_ = v___x_2870_;
                v_x_2852_ = v___x_2872_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_2878_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10_spec__20___redArg(
    mut v_n_2881_: *mut LeanObject,
    mut v_k_2882_: *mut LeanObject,
    mut v_v_2883_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2885_: *mut LeanObject = core::ptr::null_mut();
    v___x_2884_ = lean_unsigned_to_nat(0);
    v___x_2885_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10_spec__20_spec__23___redArg(v_n_2881_, v___x_2884_, v_k_2882_, v_v_2883_);
    return v___x_2885_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10___redArg___closed__0()
-> usize {
    let mut v___x_2886_: usize = 0;
    let mut v___x_2887_: usize = 0;
    let mut v___x_2888_: usize = 0;
    v___x_2886_ = 5usize;
    v___x_2887_ = 1usize;
    v___x_2888_ = lean_usize_shift_left(v___x_2887_, v___x_2886_);
    return v___x_2888_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10___redArg___closed__1()
-> usize {
    let mut v___x_2889_: usize = 0;
    let mut v___x_2890_: usize = 0;
    let mut v___x_2891_: usize = 0;
    v___x_2889_ = 1usize;
    v___x_2890_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10___redArg___closed__0);
    v___x_2891_ = lean_usize_sub(v___x_2890_, v___x_2889_);
    return v___x_2891_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_2892_: *mut LeanObject = core::ptr::null_mut();
    v___x_2892_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_2892_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10___redArg(
    mut v_x_2893_: *mut LeanObject,
    mut v_x_2894_: usize,
    mut v_x_2895_: usize,
    mut v_x_2896_: *mut LeanObject,
    mut v_x_2897_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_2898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2899_: usize = 0;
    let mut v___x_2900_: usize = 0;
    let mut v___x_2901_: usize = 0;
    let mut v___x_2902_: usize = 0;
    let mut v_j_2903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: u8 = 0;
    let mut v___x_2907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2908_: u8 = 0;
    let mut v_v_2909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_2918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2922_: u8 = 0;
    let mut v___x_2923_: u8 = 0;
    let mut v___x_2924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2929_: u8 = 0;
    let mut v_node_2930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2933_: u8 = 0;
    let mut v___x_2934_: usize = 0;
    let mut v___x_2935_: usize = 0;
    let mut v___x_2936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2940_: u8 = 0;
    let mut v___x_2941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2942_: u8 = 0;
    let mut v_unused_2943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_2944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2948_: u8 = 0;
    let mut v___x_2950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_2951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2953_: u8 = 0;
    let mut v_ks_2954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: usize = 0;
    let mut v___x_2960_: u8 = 0;
    let mut v___x_2961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: u8 = 0;
    let mut v_reuseFailAlloc_2964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2965_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2893_) == 0 {
                    v_es_2898_ = lean_ctor_get(v_x_2893_, 0);
                    v___x_2899_ = 5usize;
                    v___x_2900_ = 1usize;
                    v___x_2901_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10___redArg___closed__1);
                    v___x_2902_ = lean_usize_land(v_x_2894_, v___x_2901_);
                    v_j_2903_ = lean_usize_to_nat(v___x_2902_);
                    v___x_2904_ = lean_array_get_size(v_es_2898_);
                    v___x_2905_ = lean_nat_dec_lt(v_j_2903_, v___x_2904_);
                    if v___x_2905_ == 0 {
                        lean_dec(v_j_2903_);
                        lean_dec(v_x_2897_);
                        lean_dec(v_x_2896_);
                        return v_x_2893_;
                    } else {
                        lean_inc_ref(v_es_2898_);
                        v_isSharedCheck_2942_ = (!lean_is_exclusive(v_x_2893_)) as u8;
                        if v_isSharedCheck_2942_ == 0 {
                            v_unused_2943_ = lean_ctor_get(v_x_2893_, 0);
                            lean_dec(v_unused_2943_);
                            v___x_2907_ = v_x_2893_;
                            v_isShared_2908_ = v_isSharedCheck_2942_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_2893_);
                            v___x_2907_ = lean_box(0);
                            v_isShared_2908_ = v_isSharedCheck_2942_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_2944_ = lean_ctor_get(v_x_2893_, 0);
                    v_vs_2945_ = lean_ctor_get(v_x_2893_, 1);
                    v_isSharedCheck_2965_ = (!lean_is_exclusive(v_x_2893_)) as u8;
                    if v_isSharedCheck_2965_ == 0 {
                        v___x_2947_ = v_x_2893_;
                        v_isShared_2948_ = v_isSharedCheck_2965_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_2945_);
                        lean_inc(v_ks_2944_);
                        lean_dec(v_x_2893_);
                        v___x_2947_ = lean_box(0);
                        v_isShared_2948_ = v_isSharedCheck_2965_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_2909_ = lean_array_fget(v_es_2898_, v_j_2903_);
                v___x_2910_ = lean_box(0);
                v_xs_x27_2911_ = lean_array_fset(v_es_2898_, v_j_2903_, v___x_2910_);
                match lean_obj_tag(v_v_2909_) {
                    0 => {
                        v_key_2918_ = lean_ctor_get(v_v_2909_, 0);
                        v_val_2919_ = lean_ctor_get(v_v_2909_, 1);
                        v_isSharedCheck_2929_ = (!lean_is_exclusive(v_v_2909_)) as u8;
                        if v_isSharedCheck_2929_ == 0 {
                            v___x_2921_ = v_v_2909_;
                            v_isShared_2922_ = v_isSharedCheck_2929_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_2919_);
                            lean_inc(v_key_2918_);
                            lean_dec(v_v_2909_);
                            v___x_2921_ = lean_box(0);
                            v_isShared_2922_ = v_isSharedCheck_2929_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_2930_ = lean_ctor_get(v_v_2909_, 0);
                        v_isSharedCheck_2940_ = (!lean_is_exclusive(v_v_2909_)) as u8;
                        if v_isSharedCheck_2940_ == 0 {
                            v___x_2932_ = v_v_2909_;
                            v_isShared_2933_ = v_isSharedCheck_2940_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_2930_);
                            lean_dec(v_v_2909_);
                            v___x_2932_ = lean_box(0);
                            v_isShared_2933_ = v_isSharedCheck_2940_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_2941_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_2941_, 0, v_x_2896_);
                        lean_ctor_set(v___x_2941_, 1, v_x_2897_);
                        v___y_2913_ = v___x_2941_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2914_ = lean_array_fset(v_xs_x27_2911_, v_j_2903_, v___y_2913_);
                lean_dec(v_j_2903_);
                if v_isShared_2908_ == 0 {
                    lean_ctor_set(v___x_2907_, 0, v___x_2914_);
                    v___x_2916_ = v___x_2907_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2917_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2917_, 0, v___x_2914_);
                    v___x_2916_ = v_reuseFailAlloc_2917_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2916_;
            }
            4 => {
                v___x_2923_ = l_Lean_instBEqMVarId_beq(v_x_2896_, v_key_2918_);
                if v___x_2923_ == 0 {
                    lean_del_object(v___x_2921_);
                    v___x_2924_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_2918_,
                        v_val_2919_,
                        v_x_2896_,
                        v_x_2897_,
                    );
                    v___x_2925_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2925_, 0, v___x_2924_);
                    v___y_2913_ = v___x_2925_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_2919_);
                    lean_dec(v_key_2918_);
                    if v_isShared_2922_ == 0 {
                        lean_ctor_set(v___x_2921_, 1, v_x_2897_);
                        lean_ctor_set(v___x_2921_, 0, v_x_2896_);
                        v___x_2927_ = v___x_2921_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2928_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2928_, 0, v_x_2896_);
                        lean_ctor_set(v_reuseFailAlloc_2928_, 1, v_x_2897_);
                        v___x_2927_ = v_reuseFailAlloc_2928_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_2913_ = v___x_2927_;
                state = 2;
                continue;
            }
            6 => {
                v___x_2934_ = lean_usize_shift_right(v_x_2894_, v___x_2899_);
                v___x_2935_ = lean_usize_add(v_x_2895_, v___x_2900_);
                v___x_2936_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10___redArg(v_node_2930_, v___x_2934_, v___x_2935_, v_x_2896_, v_x_2897_);
                if v_isShared_2933_ == 0 {
                    lean_ctor_set(v___x_2932_, 0, v___x_2936_);
                    v___x_2938_ = v___x_2932_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2939_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2939_, 0, v___x_2936_);
                    v___x_2938_ = v_reuseFailAlloc_2939_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_2913_ = v___x_2938_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_2948_ == 0 {
                    v___x_2950_ = v___x_2947_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2964_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2964_, 0, v_ks_2944_);
                    lean_ctor_set(v_reuseFailAlloc_2964_, 1, v_vs_2945_);
                    v___x_2950_ = v_reuseFailAlloc_2964_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_2951_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10_spec__20___redArg(v___x_2950_, v_x_2896_, v_x_2897_);
                v___x_2959_ = 7usize;
                v___x_2960_ = lean_usize_dec_le(v___x_2959_, v_x_2895_);
                if v___x_2960_ == 0 {
                    v___x_2961_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2951_);
                    v___x_2962_ = lean_unsigned_to_nat(4);
                    v___x_2963_ = lean_nat_dec_lt(v___x_2961_, v___x_2962_);
                    lean_dec(v___x_2961_);
                    v___y_2953_ = v___x_2963_;
                    state = 10;
                    continue;
                } else {
                    v___y_2953_ = v___x_2960_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_2953_ == 0 {
                    v_ks_2954_ = lean_ctor_get(v_newNode_2951_, 0);
                    lean_inc_ref(v_ks_2954_);
                    v_vs_2955_ = lean_ctor_get(v_newNode_2951_, 1);
                    lean_inc_ref(v_vs_2955_);
                    lean_dec_ref(v_newNode_2951_);
                    v___x_2956_ = lean_unsigned_to_nat(0);
                    v___x_2957_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10___redArg___closed__2);
                    v___x_2958_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10_spec__21___redArg(v_x_2895_, v_ks_2954_, v_vs_2955_, v___x_2956_, v___x_2957_);
                    lean_dec_ref(v_vs_2955_);
                    lean_dec_ref(v_ks_2954_);
                    return v___x_2958_;
                } else {
                    return v_newNode_2951_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10_spec__21___redArg(
    mut v_depth_2966_: usize,
    mut v_keys_2967_: *mut LeanObject,
    mut v_vals_2968_: *mut LeanObject,
    mut v_i_2969_: *mut LeanObject,
    mut v_entries_2970_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2972_: u8 = 0;
    let mut v_k_2973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: u64 = 0;
    let mut v_h_2976_: usize = 0;
    let mut v___x_2977_: usize = 0;
    let mut v___x_2978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: usize = 0;
    let mut v___x_2980_: usize = 0;
    let mut v___x_2981_: usize = 0;
    let mut v_h_2982_: usize = 0;
    let mut v___x_2983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2971_ = lean_array_get_size(v_keys_2967_);
                v___x_2972_ = lean_nat_dec_lt(v_i_2969_, v___x_2971_);
                if v___x_2972_ == 0 {
                    lean_dec(v_i_2969_);
                    return v_entries_2970_;
                } else {
                    v_k_2973_ = lean_array_fget_borrowed(v_keys_2967_, v_i_2969_);
                    v_v_2974_ = lean_array_fget_borrowed(v_vals_2968_, v_i_2969_);
                    v___x_2975_ = l_Lean_instHashableMVarId_hash(v_k_2973_);
                    v_h_2976_ = lean_uint64_to_usize(v___x_2975_);
                    v___x_2977_ = 5usize;
                    v___x_2978_ = lean_unsigned_to_nat(1);
                    v___x_2979_ = 1usize;
                    v___x_2980_ = lean_usize_sub(v_depth_2966_, v___x_2979_);
                    v___x_2981_ = lean_usize_mul(v___x_2977_, v___x_2980_);
                    v_h_2982_ = lean_usize_shift_right(v_h_2976_, v___x_2981_);
                    v___x_2983_ = lean_nat_add(v_i_2969_, v___x_2978_);
                    lean_dec(v_i_2969_);
                    lean_inc(v_v_2974_);
                    lean_inc(v_k_2973_);
                    v___x_2984_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10___redArg(v_entries_2970_, v_h_2982_, v_depth_2966_, v_k_2973_, v_v_2974_);
                    v_i_2969_ = v___x_2983_;
                    v_entries_2970_ = v___x_2984_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10_spec__21___redArg___boxed(
    mut v_depth_2986_: *mut LeanObject,
    mut v_keys_2987_: *mut LeanObject,
    mut v_vals_2988_: *mut LeanObject,
    mut v_i_2989_: *mut LeanObject,
    mut v_entries_2990_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_2991_: usize = 0;
    let mut v_res_2992_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_2991_ = lean_unbox_usize(v_depth_2986_);
    lean_dec(v_depth_2986_);
    v_res_2992_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10_spec__21___redArg(v_depth_boxed_2991_, v_keys_2987_, v_vals_2988_, v_i_2989_, v_entries_2990_);
    lean_dec_ref(v_vals_2988_);
    lean_dec_ref(v_keys_2987_);
    return v_res_2992_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10___redArg___boxed(
    mut v_x_2993_: *mut LeanObject,
    mut v_x_2994_: *mut LeanObject,
    mut v_x_2995_: *mut LeanObject,
    mut v_x_2996_: *mut LeanObject,
    mut v_x_2997_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_17012__boxed_2998_: usize = 0;
    let mut v_x_17013__boxed_2999_: usize = 0;
    let mut v_res_3000_: *mut LeanObject = core::ptr::null_mut();
    v_x_17012__boxed_2998_ = lean_unbox_usize(v_x_2994_);
    lean_dec(v_x_2994_);
    v_x_17013__boxed_2999_ = lean_unbox_usize(v_x_2995_);
    lean_dec(v_x_2995_);
    v_res_3000_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10___redArg(v_x_2993_, v_x_17012__boxed_2998_, v_x_17013__boxed_2999_, v_x_2996_, v_x_2997_);
    return v_res_3000_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4___redArg(
    mut v_x_3001_: *mut LeanObject,
    mut v_x_3002_: *mut LeanObject,
    mut v_x_3003_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3004_: u64 = 0;
    let mut v___x_3005_: usize = 0;
    let mut v___x_3006_: usize = 0;
    let mut v___x_3007_: *mut LeanObject = core::ptr::null_mut();
    v___x_3004_ = l_Lean_instHashableMVarId_hash(v_x_3002_);
    v___x_3005_ = lean_uint64_to_usize(v___x_3004_);
    v___x_3006_ = 1usize;
    v___x_3007_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10___redArg(v_x_3001_, v___x_3005_, v___x_3006_, v_x_3002_, v_x_3003_);
    return v___x_3007_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___redArg(
    mut v_mvarId_3008_: *mut LeanObject,
    mut v_val_3009_: *mut LeanObject,
    mut v___y_3010_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_3013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_3014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_3016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_3017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3020_: u8 = 0;
    let mut v_depth_3021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_3022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_3023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_3024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lDecls_3025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_3026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_userNames_3027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_3028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_3029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_3030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3033_: u8 = 0;
    let mut v___x_3034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3044_: u8 = 0;
    let mut v_isSharedCheck_3045_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3012_ = lean_st_ref_take(v___y_3010_);
                v_mctx_3013_ = lean_ctor_get(v___x_3012_, 0);
                v_cache_3014_ = lean_ctor_get(v___x_3012_, 1);
                v_zetaDeltaFVarIds_3015_ = lean_ctor_get(v___x_3012_, 2);
                v_postponed_3016_ = lean_ctor_get(v___x_3012_, 3);
                v_diag_3017_ = lean_ctor_get(v___x_3012_, 4);
                v_isSharedCheck_3045_ = (!lean_is_exclusive(v___x_3012_)) as u8;
                if v_isSharedCheck_3045_ == 0 {
                    v___x_3019_ = v___x_3012_;
                    v_isShared_3020_ = v_isSharedCheck_3045_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_diag_3017_);
                    lean_inc(v_postponed_3016_);
                    lean_inc(v_zetaDeltaFVarIds_3015_);
                    lean_inc(v_cache_3014_);
                    lean_inc(v_mctx_3013_);
                    lean_dec(v___x_3012_);
                    v___x_3019_ = lean_box(0);
                    v_isShared_3020_ = v_isSharedCheck_3045_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_3021_ = lean_ctor_get(v_mctx_3013_, 0);
                v_levelAssignDepth_3022_ = lean_ctor_get(v_mctx_3013_, 1);
                v_lmvarCounter_3023_ = lean_ctor_get(v_mctx_3013_, 2);
                v_mvarCounter_3024_ = lean_ctor_get(v_mctx_3013_, 3);
                v_lDecls_3025_ = lean_ctor_get(v_mctx_3013_, 4);
                v_decls_3026_ = lean_ctor_get(v_mctx_3013_, 5);
                v_userNames_3027_ = lean_ctor_get(v_mctx_3013_, 6);
                v_lAssignment_3028_ = lean_ctor_get(v_mctx_3013_, 7);
                v_eAssignment_3029_ = lean_ctor_get(v_mctx_3013_, 8);
                v_dAssignment_3030_ = lean_ctor_get(v_mctx_3013_, 9);
                v_isSharedCheck_3044_ = (!lean_is_exclusive(v_mctx_3013_)) as u8;
                if v_isSharedCheck_3044_ == 0 {
                    v___x_3032_ = v_mctx_3013_;
                    v_isShared_3033_ = v_isSharedCheck_3044_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_dAssignment_3030_);
                    lean_inc(v_eAssignment_3029_);
                    lean_inc(v_lAssignment_3028_);
                    lean_inc(v_userNames_3027_);
                    lean_inc(v_decls_3026_);
                    lean_inc(v_lDecls_3025_);
                    lean_inc(v_mvarCounter_3024_);
                    lean_inc(v_lmvarCounter_3023_);
                    lean_inc(v_levelAssignDepth_3022_);
                    lean_inc(v_depth_3021_);
                    lean_dec(v_mctx_3013_);
                    v___x_3032_ = lean_box(0);
                    v_isShared_3033_ = v_isSharedCheck_3044_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3034_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4___redArg(v_eAssignment_3029_, v_mvarId_3008_, v_val_3009_);
                if v_isShared_3033_ == 0 {
                    lean_ctor_set(v___x_3032_, 8, v___x_3034_);
                    v___x_3036_ = v___x_3032_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3043_ = lean_alloc_ctor(0, 10, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3043_, 0, v_depth_3021_);
                    lean_ctor_set(v_reuseFailAlloc_3043_, 1, v_levelAssignDepth_3022_);
                    lean_ctor_set(v_reuseFailAlloc_3043_, 2, v_lmvarCounter_3023_);
                    lean_ctor_set(v_reuseFailAlloc_3043_, 3, v_mvarCounter_3024_);
                    lean_ctor_set(v_reuseFailAlloc_3043_, 4, v_lDecls_3025_);
                    lean_ctor_set(v_reuseFailAlloc_3043_, 5, v_decls_3026_);
                    lean_ctor_set(v_reuseFailAlloc_3043_, 6, v_userNames_3027_);
                    lean_ctor_set(v_reuseFailAlloc_3043_, 7, v_lAssignment_3028_);
                    lean_ctor_set(v_reuseFailAlloc_3043_, 8, v___x_3034_);
                    lean_ctor_set(v_reuseFailAlloc_3043_, 9, v_dAssignment_3030_);
                    v___x_3036_ = v_reuseFailAlloc_3043_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3020_ == 0 {
                    lean_ctor_set(v___x_3019_, 0, v___x_3036_);
                    v___x_3038_ = v___x_3019_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3042_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3042_, 0, v___x_3036_);
                    lean_ctor_set(v_reuseFailAlloc_3042_, 1, v_cache_3014_);
                    lean_ctor_set(v_reuseFailAlloc_3042_, 2, v_zetaDeltaFVarIds_3015_);
                    lean_ctor_set(v_reuseFailAlloc_3042_, 3, v_postponed_3016_);
                    lean_ctor_set(v_reuseFailAlloc_3042_, 4, v_diag_3017_);
                    v___x_3038_ = v_reuseFailAlloc_3042_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3039_ = lean_st_ref_set(v___y_3010_, v___x_3038_);
                v___x_3040_ = lean_box(0);
                v___x_3041_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3041_, 0, v___x_3040_);
                return v___x_3041_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___redArg___boxed(
    mut v_mvarId_3046_: *mut LeanObject,
    mut v_val_3047_: *mut LeanObject,
    mut v___y_3048_: *mut LeanObject,
    mut v___y_3049_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3050_: *mut LeanObject = core::ptr::null_mut();
    v_res_3050_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___redArg(v_mvarId_3046_, v_val_3047_, v___y_3048_);
    lean_dec(v___y_3048_);
    return v_res_3050_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0(
    mut v_a_3051_: *mut LeanObject,
    mut v_a_3052_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3059_: u8 = 0;
    let mut v_fst_3060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3063_: u8 = 0;
    let mut v_width_3064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_atomNumber_3065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_synthetic_3066_: u8 = 0;
    let mut v___x_3067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3077_: u8 = 0;
    let mut v_unused_3078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3079_: u8 = 0;
    let mut v_unused_3080_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_3051_) == 0 {
                    v___x_3053_ = l_List_reverse___redArg(v_a_3052_);
                    return v___x_3053_;
                } else {
                    v_head_3054_ = lean_ctor_get(v_a_3051_, 0);
                    lean_inc(v_head_3054_);
                    v_snd_3055_ = lean_ctor_get(v_head_3054_, 1);
                    lean_inc(v_snd_3055_);
                    v_tail_3056_ = lean_ctor_get(v_a_3051_, 1);
                    v_isSharedCheck_3079_ = (!lean_is_exclusive(v_a_3051_)) as u8;
                    if v_isSharedCheck_3079_ == 0 {
                        v_unused_3080_ = lean_ctor_get(v_a_3051_, 0);
                        lean_dec(v_unused_3080_);
                        v___x_3058_ = v_a_3051_;
                        v_isShared_3059_ = v_isSharedCheck_3079_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3056_);
                        lean_dec(v_a_3051_);
                        v___x_3058_ = lean_box(0);
                        v_isShared_3059_ = v_isSharedCheck_3079_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_3060_ = lean_ctor_get(v_head_3054_, 0);
                v_isSharedCheck_3077_ = (!lean_is_exclusive(v_head_3054_)) as u8;
                if v_isSharedCheck_3077_ == 0 {
                    v_unused_3078_ = lean_ctor_get(v_head_3054_, 1);
                    lean_dec(v_unused_3078_);
                    v___x_3062_ = v_head_3054_;
                    v_isShared_3063_ = v_isSharedCheck_3077_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_fst_3060_);
                    lean_dec(v_head_3054_);
                    v___x_3062_ = lean_box(0);
                    v_isShared_3063_ = v_isSharedCheck_3077_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_width_3064_ = lean_ctor_get(v_snd_3055_, 0);
                lean_inc(v_width_3064_);
                v_atomNumber_3065_ = lean_ctor_get(v_snd_3055_, 1);
                lean_inc(v_atomNumber_3065_);
                v_synthetic_3066_ = lean_ctor_get_uint8(
                    v_snd_3055_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                );
                lean_dec(v_snd_3055_);
                v___x_3067_ = lean_box((v_synthetic_3066_) as usize);
                if v_isShared_3063_ == 0 {
                    lean_ctor_set(v___x_3062_, 1, v___x_3067_);
                    v___x_3069_ = v___x_3062_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3076_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3076_, 0, v_fst_3060_);
                    lean_ctor_set(v_reuseFailAlloc_3076_, 1, v___x_3067_);
                    v___x_3069_ = v_reuseFailAlloc_3076_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3070_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3070_, 0, v_width_3064_);
                lean_ctor_set(v___x_3070_, 1, v___x_3069_);
                v___x_3071_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3071_, 0, v_atomNumber_3065_);
                lean_ctor_set(v___x_3071_, 1, v___x_3070_);
                if v_isShared_3059_ == 0 {
                    lean_ctor_set(v___x_3058_, 1, v_a_3052_);
                    lean_ctor_set(v___x_3058_, 0, v___x_3071_);
                    v___x_3073_ = v___x_3058_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3075_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3075_, 0, v___x_3071_);
                    lean_ctor_set(v_reuseFailAlloc_3075_, 1, v_a_3052_);
                    v___x_3073_ = v_reuseFailAlloc_3075_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_a_3051_ = v_tail_3056_;
                v_a_3052_ = v___x_3073_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6___redArg(
    mut v_cls_3084_: *mut LeanObject,
    mut v_msg_3085_: *mut LeanObject,
    mut v___y_3086_: *mut LeanObject,
    mut v___y_3087_: *mut LeanObject,
    mut v___y_3088_: *mut LeanObject,
    mut v___y_3089_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_3091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3096_: u8 = 0;
    let mut v___x_3097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_3098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_3101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_3103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_3104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_3105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3109_: u8 = 0;
    let mut v_tid_3110_: u64 = 0;
    let mut v_traces_3111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3114_: u8 = 0;
    let mut v___x_3115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3116_: f64 = 0.0;
    let mut v___x_3117_: u8 = 0;
    let mut v___x_3118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3135_: u8 = 0;
    let mut v_isSharedCheck_3136_: u8 = 0;
    let mut v_isSharedCheck_3137_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3091_ = lean_ctor_get(v___y_3088_, 5);
                v___x_3092_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__3_spec__5(v_msg_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_);
                v_a_3093_ = lean_ctor_get(v___x_3092_, 0);
                v_isSharedCheck_3137_ = (!lean_is_exclusive(v___x_3092_)) as u8;
                if v_isSharedCheck_3137_ == 0 {
                    v___x_3095_ = v___x_3092_;
                    v_isShared_3096_ = v_isSharedCheck_3137_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_3093_);
                    lean_dec(v___x_3092_);
                    v___x_3095_ = lean_box(0);
                    v_isShared_3096_ = v_isSharedCheck_3137_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3097_ = lean_st_ref_take(v___y_3089_);
                v_traceState_3098_ = lean_ctor_get(v___x_3097_, 4);
                v_env_3099_ = lean_ctor_get(v___x_3097_, 0);
                v_nextMacroScope_3100_ = lean_ctor_get(v___x_3097_, 1);
                v_ngen_3101_ = lean_ctor_get(v___x_3097_, 2);
                v_auxDeclNGen_3102_ = lean_ctor_get(v___x_3097_, 3);
                v_cache_3103_ = lean_ctor_get(v___x_3097_, 5);
                v_messages_3104_ = lean_ctor_get(v___x_3097_, 6);
                v_infoState_3105_ = lean_ctor_get(v___x_3097_, 7);
                v_snapshotTasks_3106_ = lean_ctor_get(v___x_3097_, 8);
                v_isSharedCheck_3136_ = (!lean_is_exclusive(v___x_3097_)) as u8;
                if v_isSharedCheck_3136_ == 0 {
                    v___x_3108_ = v___x_3097_;
                    v_isShared_3109_ = v_isSharedCheck_3136_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_3106_);
                    lean_inc(v_infoState_3105_);
                    lean_inc(v_messages_3104_);
                    lean_inc(v_cache_3103_);
                    lean_inc(v_traceState_3098_);
                    lean_inc(v_auxDeclNGen_3102_);
                    lean_inc(v_ngen_3101_);
                    lean_inc(v_nextMacroScope_3100_);
                    lean_inc(v_env_3099_);
                    lean_dec(v___x_3097_);
                    v___x_3108_ = lean_box(0);
                    v_isShared_3109_ = v_isSharedCheck_3136_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_3110_ = lean_ctor_get_uint64(
                    v_traceState_3098_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_traces_3111_ = lean_ctor_get(v_traceState_3098_, 0);
                v_isSharedCheck_3135_ = (!lean_is_exclusive(v_traceState_3098_)) as u8;
                if v_isSharedCheck_3135_ == 0 {
                    v___x_3113_ = v_traceState_3098_;
                    v_isShared_3114_ = v_isSharedCheck_3135_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_traces_3111_);
                    lean_dec(v_traceState_3098_);
                    v___x_3113_ = lean_box(0);
                    v_isShared_3114_ = v_isSharedCheck_3135_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3115_ = lean_box(0);
                v___x_3116_ = lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__2_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__2);
                v___x_3117_ = 0;
                v___x_3118_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6___redArg___closed__0;
                v___x_3119_ = lean_alloc_ctor(0, 3, (17) as u32);
                lean_ctor_set(v___x_3119_, 0, v_cls_3084_);
                lean_ctor_set(v___x_3119_, 1, v___x_3115_);
                lean_ctor_set(v___x_3119_, 2, v___x_3118_);
                lean_ctor_set_float(
                    v___x_3119_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_3116_,
                );
                lean_ctor_set_float(
                    v___x_3119_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    v___x_3116_,
                );
                lean_ctor_set_uint8(
                    v___x_3119_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                    v___x_3117_,
                );
                v___x_3120_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6___redArg___closed__1;
                v___x_3121_ = lean_alloc_ctor(9, 3, (0) as u32);
                lean_ctor_set(v___x_3121_, 0, v___x_3119_);
                lean_ctor_set(v___x_3121_, 1, v_a_3093_);
                lean_ctor_set(v___x_3121_, 2, v___x_3120_);
                lean_inc(v_ref_3091_);
                v___x_3122_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3122_, 0, v_ref_3091_);
                lean_ctor_set(v___x_3122_, 1, v___x_3121_);
                v___x_3123_ = l_Lean_PersistentArray_push___redArg(v_traces_3111_, v___x_3122_);
                if v_isShared_3114_ == 0 {
                    lean_ctor_set(v___x_3113_, 0, v___x_3123_);
                    v___x_3125_ = v___x_3113_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3134_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3134_, 0, v___x_3123_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_3134_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_3110_,
                    );
                    v___x_3125_ = v_reuseFailAlloc_3134_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3109_ == 0 {
                    lean_ctor_set(v___x_3108_, 4, v___x_3125_);
                    v___x_3127_ = v___x_3108_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3133_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3133_, 0, v_env_3099_);
                    lean_ctor_set(v_reuseFailAlloc_3133_, 1, v_nextMacroScope_3100_);
                    lean_ctor_set(v_reuseFailAlloc_3133_, 2, v_ngen_3101_);
                    lean_ctor_set(v_reuseFailAlloc_3133_, 3, v_auxDeclNGen_3102_);
                    lean_ctor_set(v_reuseFailAlloc_3133_, 4, v___x_3125_);
                    lean_ctor_set(v_reuseFailAlloc_3133_, 5, v_cache_3103_);
                    lean_ctor_set(v_reuseFailAlloc_3133_, 6, v_messages_3104_);
                    lean_ctor_set(v_reuseFailAlloc_3133_, 7, v_infoState_3105_);
                    lean_ctor_set(v_reuseFailAlloc_3133_, 8, v_snapshotTasks_3106_);
                    v___x_3127_ = v_reuseFailAlloc_3133_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3128_ = lean_st_ref_set(v___y_3089_, v___x_3127_);
                v___x_3129_ = lean_box(0);
                if v_isShared_3096_ == 0 {
                    lean_ctor_set(v___x_3095_, 0, v___x_3129_);
                    v___x_3131_ = v___x_3095_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3132_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3132_, 0, v___x_3129_);
                    v___x_3131_ = v_reuseFailAlloc_3132_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3131_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6___redArg___boxed(
    mut v_cls_3138_: *mut LeanObject,
    mut v_msg_3139_: *mut LeanObject,
    mut v___y_3140_: *mut LeanObject,
    mut v___y_3141_: *mut LeanObject,
    mut v___y_3142_: *mut LeanObject,
    mut v___y_3143_: *mut LeanObject,
    mut v___y_3144_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3145_: *mut LeanObject = core::ptr::null_mut();
    v_res_3145_ =
        l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6___redArg(
            v_cls_3138_,
            v_msg_3139_,
            v___y_3140_,
            v___y_3141_,
            v___y_3142_,
            v___y_3143_,
        );
    lean_dec(v___y_3143_);
    lean_dec_ref(v___y_3142_);
    lean_dec(v___y_3141_);
    lean_dec_ref(v___y_3140_);
    return v_res_3145_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__0()
-> *mut LeanObject {
    let mut v___x_3146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3148_: *mut LeanObject = core::ptr::null_mut();
    v___x_3146_ = lean_box(0);
    v___x_3147_ = lean_unsigned_to_nat(16);
    v___x_3148_ = lean_mk_array(v___x_3147_, v___x_3146_);
    return v___x_3148_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__1()
-> *mut LeanObject {
    let mut v___x_3149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut LeanObject = core::ptr::null_mut();
    v___x_3149_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__0_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__0,
    );
    v___x_3150_ = lean_unsigned_to_nat(0);
    v___x_3151_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3151_, 0, v___x_3150_);
    lean_ctor_set(v___x_3151_, 1, v___x_3149_);
    return v___x_3151_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__5()
-> *mut LeanObject {
    let mut v___x_3156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3157_: *mut LeanObject = core::ptr::null_mut();
    v___x_3156_ = l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__4;
    v___x_3157_ = l_Lean_stringToMessageData(v___x_3156_);
    return v___x_3157_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__6()
-> f64 {
    let mut v___x_3158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: f64 = 0.0;
    v___x_3158_ = lean_unsigned_to_nat(1000000000);
    v___x_3159_ = lean_float_of_nat(v___x_3158_);
    return v___x_3159_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1(
    mut v_unsatProver_3160_: *mut LeanObject,
    mut v_g_3161_: *mut LeanObject,
    mut v_cls_3162_: *mut LeanObject,
    mut v___x_3163_: u8,
    mut v___x_3164_: *mut LeanObject,
    mut v___f_3165_: *mut LeanObject,
    mut v___y_3166_: *mut LeanObject,
    mut v___y_3167_: *mut LeanObject,
    mut v___y_3168_: *mut LeanObject,
    mut v___y_3169_: *mut LeanObject,
    mut v___y_3170_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3188_: u8 = 0;
    let mut v_a_3189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3192_: u8 = 0;
    let mut v___x_3194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3199_: u8 = 0;
    let mut v_a_3200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3203_: u8 = 0;
    let mut v_proof_3204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cert_3205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proveFalse_3206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3212_: u8 = 0;
    let mut v___x_3214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3219_: u8 = 0;
    let mut v_unused_3220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3224_: u8 = 0;
    let mut v___x_3226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3228_: u8 = 0;
    let mut v_isSharedCheck_3229_: u8 = 0;
    let mut v_isSharedCheck_3230_: u8 = 0;
    let mut v_a_3231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3234_: u8 = 0;
    let mut v___x_3236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3238_: u8 = 0;
    let mut v___y_3240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_atoms_3247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_3248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3252_: u8 = 0;
    let mut v___x_3253_: usize = 0;
    let mut v___x_3254_: usize = 0;
    let mut v___x_3255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_3256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_3257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3258_: u8 = 0;
    let mut v___y_3260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: u8 = 0;
    let mut v_bvExpr_3266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3276_: u8 = 0;
    let mut v___x_3278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3280_: u8 = 0;
    let mut v_a_3281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3284_: u8 = 0;
    let mut v___x_3286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3288_: u8 = 0;
    let mut v___x_3289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: u8 = 0;
    let mut v___y_3294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3298_: f64 = 0.0;
    let mut v___x_3299_: f64 = 0.0;
    let mut v___x_3300_: f64 = 0.0;
    let mut v___x_3301_: f64 = 0.0;
    let mut v___x_3302_: f64 = 0.0;
    let mut v___x_3303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: f64 = 0.0;
    let mut v___x_3314_: f64 = 0.0;
    let mut v___x_3315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: u8 = 0;
    let mut v___x_3325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3330_: u8 = 0;
    let mut v___x_3332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3334_: u8 = 0;
    let mut v_a_3335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3338_: u8 = 0;
    let mut v___x_3340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3342_: u8 = 0;
    let mut v___x_3343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3348_: u8 = 0;
    let mut v___x_3350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3352_: u8 = 0;
    let mut v_a_3353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3356_: u8 = 0;
    let mut v___x_3358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3360_: u8 = 0;
    let mut v___x_3361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3362_: u8 = 0;
    let mut v___x_3363_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_3256_ = lean_ctor_get(v___y_3169_, 2);
                v_inheritedTraceOptions_3257_ = lean_ctor_get(v___y_3169_, 13);
                v_hasTrace_3258_ = lean_ctor_get_uint8(
                    v_options_3256_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                if v_hasTrace_3258_ == 0 {
                    lean_dec_ref(v___f_3165_);
                    lean_dec_ref(v___x_3164_);
                    lean_inc(v_g_3161_);
                    v___x_3289_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV(v_g_3161_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_);
                    v___y_3260_ = v___x_3289_;
                    state = 15;
                    continue;
                } else {
                    v___x_3290_ = l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__3;
                    lean_inc(v_cls_3162_);
                    v___x_3291_ = l_Lean_Name_append(v___x_3290_, v_cls_3162_);
                    v___x_3292_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_3257_,
                        v_options_3256_,
                        v___x_3291_,
                    );
                    lean_dec(v___x_3291_);
                    if v___x_3292_ == 0 {
                        v___x_3361_ = l_Lean_trace_profiler;
                        v___x_3362_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8(v_options_3256_, v___x_3361_);
                        if v___x_3362_ == 0 {
                            lean_dec_ref(v___f_3165_);
                            lean_dec_ref(v___x_3164_);
                            lean_inc(v_g_3161_);
                            v___x_3363_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV(v_g_3161_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_);
                            v___y_3260_ = v___x_3363_;
                            state = 15;
                            continue;
                        } else {
                            state = 22;
                            continue;
                        }
                    } else {
                        state = 22;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3180_ = lean_box(0);
                v___x_3181_ = l_List_mapTR_loop___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0(v___y_3179_, v___x_3180_);
                v___x_3182_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__1_once), _init_l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__1);
                v___x_3183_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__2___redArg(v___x_3181_, v___x_3182_);
                lean_dec(v___x_3181_);
                lean_inc(v___y_3175_);
                lean_inc_ref(v___y_3178_);
                lean_inc(v___y_3176_);
                lean_inc_ref(v___y_3177_);
                lean_inc_ref(v___y_3174_);
                lean_inc(v_g_3161_);
                v___x_3184_ = lean_apply_8(
                    v_unsatProver_3160_,
                    v_g_3161_,
                    v___y_3174_,
                    v___x_3183_,
                    v___y_3177_,
                    v___y_3176_,
                    v___y_3178_,
                    v___y_3175_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_3184_) == 0 {
                    v_a_3185_ = lean_ctor_get(v___x_3184_, 0);
                    v_isSharedCheck_3230_ = (!lean_is_exclusive(v___x_3184_)) as u8;
                    if v_isSharedCheck_3230_ == 0 {
                        v___x_3187_ = v___x_3184_;
                        v_isShared_3188_ = v_isSharedCheck_3230_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_3185_);
                        lean_dec(v___x_3184_);
                        v___x_3187_ = lean_box(0);
                        v_isShared_3188_ = v_isSharedCheck_3230_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___y_3174_);
                    lean_dec(v_g_3161_);
                    v_a_3231_ = lean_ctor_get(v___x_3184_, 0);
                    v_isSharedCheck_3238_ = (!lean_is_exclusive(v___x_3184_)) as u8;
                    if v_isSharedCheck_3238_ == 0 {
                        v___x_3233_ = v___x_3184_;
                        v_isShared_3234_ = v_isSharedCheck_3238_;
                        state = 12;
                        continue;
                    } else {
                        lean_inc(v_a_3231_);
                        lean_dec(v___x_3184_);
                        v___x_3233_ = lean_box(0);
                        v_isShared_3234_ = v_isSharedCheck_3238_;
                        state = 12;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_3185_) == 0 {
                    lean_dec_ref(v___y_3174_);
                    lean_dec(v_g_3161_);
                    v_a_3189_ = lean_ctor_get(v_a_3185_, 0);
                    v_isSharedCheck_3199_ = (!lean_is_exclusive(v_a_3185_)) as u8;
                    if v_isSharedCheck_3199_ == 0 {
                        v___x_3191_ = v_a_3185_;
                        v_isShared_3192_ = v_isSharedCheck_3199_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3189_);
                        lean_dec(v_a_3185_);
                        v___x_3191_ = lean_box(0);
                        v_isShared_3192_ = v_isSharedCheck_3199_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3187_);
                    v_a_3200_ = lean_ctor_get(v_a_3185_, 0);
                    v_isSharedCheck_3229_ = (!lean_is_exclusive(v_a_3185_)) as u8;
                    if v_isSharedCheck_3229_ == 0 {
                        v___x_3202_ = v_a_3185_;
                        v_isShared_3203_ = v_isSharedCheck_3229_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_3200_);
                        lean_dec(v_a_3185_);
                        v___x_3202_ = lean_box(0);
                        v_isShared_3203_ = v_isSharedCheck_3229_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_3192_ == 0 {
                    v___x_3194_ = v___x_3191_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3198_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3198_, 0, v_a_3189_);
                    v___x_3194_ = v_reuseFailAlloc_3198_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3188_ == 0 {
                    lean_ctor_set(v___x_3187_, 0, v___x_3194_);
                    v___x_3196_ = v___x_3187_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3197_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3197_, 0, v___x_3194_);
                    v___x_3196_ = v_reuseFailAlloc_3197_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3196_;
            }
            6 => {
                v_proof_3204_ = lean_ctor_get(v_a_3200_, 0);
                lean_inc_ref(v_proof_3204_);
                v_cert_3205_ = lean_ctor_get(v_a_3200_, 1);
                lean_inc(v_cert_3205_);
                lean_dec(v_a_3200_);
                v_proveFalse_3206_ = lean_ctor_get(v___y_3174_, 1);
                lean_inc_ref(v_proveFalse_3206_);
                lean_dec_ref(v___y_3174_);
                lean_inc(v___y_3175_);
                lean_inc_ref(v___y_3178_);
                lean_inc(v___y_3176_);
                lean_inc_ref(v___y_3177_);
                lean_inc(v___y_3173_);
                v___x_3207_ = lean_apply_7(
                    v_proveFalse_3206_,
                    v_proof_3204_,
                    v___y_3173_,
                    v___y_3177_,
                    v___y_3176_,
                    v___y_3178_,
                    v___y_3175_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_3207_) == 0 {
                    v_a_3208_ = lean_ctor_get(v___x_3207_, 0);
                    lean_inc(v_a_3208_);
                    lean_dec_ref_known(v___x_3207_, 1);
                    v___x_3209_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___redArg(v_g_3161_, v_a_3208_, v___y_3176_);
                    v_isSharedCheck_3219_ = (!lean_is_exclusive(v___x_3209_)) as u8;
                    if v_isSharedCheck_3219_ == 0 {
                        v_unused_3220_ = lean_ctor_get(v___x_3209_, 0);
                        lean_dec(v_unused_3220_);
                        v___x_3211_ = v___x_3209_;
                        v_isShared_3212_ = v_isSharedCheck_3219_;
                        state = 7;
                        continue;
                    } else {
                        lean_dec(v___x_3209_);
                        v___x_3211_ = lean_box(0);
                        v_isShared_3212_ = v_isSharedCheck_3219_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_dec(v_cert_3205_);
                    lean_del_object(v___x_3202_);
                    lean_dec(v_g_3161_);
                    v_a_3221_ = lean_ctor_get(v___x_3207_, 0);
                    v_isSharedCheck_3228_ = (!lean_is_exclusive(v___x_3207_)) as u8;
                    if v_isSharedCheck_3228_ == 0 {
                        v___x_3223_ = v___x_3207_;
                        v_isShared_3224_ = v_isSharedCheck_3228_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_3221_);
                        lean_dec(v___x_3207_);
                        v___x_3223_ = lean_box(0);
                        v_isShared_3224_ = v_isSharedCheck_3228_;
                        state = 10;
                        continue;
                    }
                }
            }
            7 => {
                if v_isShared_3203_ == 0 {
                    lean_ctor_set(v___x_3202_, 0, v_cert_3205_);
                    v___x_3214_ = v___x_3202_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3218_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3218_, 0, v_cert_3205_);
                    v___x_3214_ = v_reuseFailAlloc_3218_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_3212_ == 0 {
                    lean_ctor_set(v___x_3211_, 0, v___x_3214_);
                    v___x_3216_ = v___x_3211_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3217_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3217_, 0, v___x_3214_);
                    v___x_3216_ = v_reuseFailAlloc_3217_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3216_;
            }
            10 => {
                if v_isShared_3224_ == 0 {
                    v___x_3226_ = v___x_3223_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3227_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3227_, 0, v_a_3221_);
                    v___x_3226_ = v_reuseFailAlloc_3227_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3226_;
            }
            12 => {
                if v_isShared_3234_ == 0 {
                    v___x_3236_ = v___x_3233_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3237_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3237_, 0, v_a_3231_);
                    v___x_3236_ = v_reuseFailAlloc_3237_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3236_;
            }
            14 => {
                v___x_3246_ = lean_st_ref_get(v___y_3241_);
                v_atoms_3247_ = lean_ctor_get(v___x_3246_, 0);
                lean_inc_ref(v_atoms_3247_);
                lean_dec(v___x_3246_);
                v_buckets_3248_ = lean_ctor_get(v_atoms_3247_, 1);
                lean_inc_ref(v_buckets_3248_);
                lean_dec_ref(v_atoms_3247_);
                v___x_3249_ = lean_box(0);
                v___x_3250_ = lean_array_get_size(v_buckets_3248_);
                v___x_3251_ = lean_unsigned_to_nat(0);
                v___x_3252_ = lean_nat_dec_lt(v___x_3251_, v___x_3250_);
                if v___x_3252_ == 0 {
                    lean_dec_ref(v_buckets_3248_);
                    v___y_3173_ = v___y_3241_;
                    v___y_3174_ = v___y_3240_;
                    v___y_3175_ = v___y_3245_;
                    v___y_3176_ = v___y_3243_;
                    v___y_3177_ = v___y_3242_;
                    v___y_3178_ = v___y_3244_;
                    v___y_3179_ = v___x_3249_;
                    state = 1;
                    continue;
                } else {
                    v___x_3253_ = lean_usize_of_nat(v___x_3250_);
                    v___x_3254_ = 0usize;
                    v___x_3255_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4(v_buckets_3248_, v___x_3253_, v___x_3254_, v___x_3249_);
                    lean_dec_ref(v_buckets_3248_);
                    v___y_3173_ = v___y_3241_;
                    v___y_3174_ = v___y_3240_;
                    v___y_3175_ = v___y_3245_;
                    v___y_3176_ = v___y_3243_;
                    v___y_3177_ = v___y_3242_;
                    v___y_3178_ = v___y_3244_;
                    v___y_3179_ = v___x_3255_;
                    state = 1;
                    continue;
                }
            }
            15 => {
                if lean_obj_tag(v___y_3260_) == 0 {
                    if v_hasTrace_3258_ == 0 {
                        lean_dec(v_cls_3162_);
                        v_a_3261_ = lean_ctor_get(v___y_3260_, 0);
                        lean_inc(v_a_3261_);
                        lean_dec_ref_known(v___y_3260_, 1);
                        v___y_3240_ = v_a_3261_;
                        v___y_3241_ = v___y_3166_;
                        v___y_3242_ = v___y_3167_;
                        v___y_3243_ = v___y_3168_;
                        v___y_3244_ = v___y_3169_;
                        v___y_3245_ = v___y_3170_;
                        state = 14;
                        continue;
                    } else {
                        v_a_3262_ = lean_ctor_get(v___y_3260_, 0);
                        lean_inc(v_a_3262_);
                        lean_dec_ref_known(v___y_3260_, 1);
                        v___x_3263_ = l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__3;
                        lean_inc(v_cls_3162_);
                        v___x_3264_ = l_Lean_Name_append(v___x_3263_, v_cls_3162_);
                        v___x_3265_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_3257_,
                            v_options_3256_,
                            v___x_3264_,
                        );
                        lean_dec(v___x_3264_);
                        if v___x_3265_ == 0 {
                            lean_dec(v_cls_3162_);
                            v___y_3240_ = v_a_3262_;
                            v___y_3241_ = v___y_3166_;
                            v___y_3242_ = v___y_3167_;
                            v___y_3243_ = v___y_3168_;
                            v___y_3244_ = v___y_3169_;
                            v___y_3245_ = v___y_3170_;
                            state = 14;
                            continue;
                        } else {
                            v_bvExpr_3266_ = lean_ctor_get(v_a_3262_, 0);
                            v___x_3267_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__5), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__5_once), _init_l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__5);
                            lean_inc_ref(v_bvExpr_3266_);
                            v___x_3268_ = l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5(v_bvExpr_3266_);
                            v___x_3269_ = lean_alloc_ctor(3, 1, (0) as u32);
                            lean_ctor_set(v___x_3269_, 0, v___x_3268_);
                            v___x_3270_ = l_Lean_MessageData_ofFormat(v___x_3269_);
                            v___x_3271_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_3271_, 0, v___x_3267_);
                            lean_ctor_set(v___x_3271_, 1, v___x_3270_);
                            v___x_3272_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6___redArg(v_cls_3162_, v___x_3271_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_);
                            if lean_obj_tag(v___x_3272_) == 0 {
                                lean_dec_ref_known(v___x_3272_, 1);
                                v___y_3240_ = v_a_3262_;
                                v___y_3241_ = v___y_3166_;
                                v___y_3242_ = v___y_3167_;
                                v___y_3243_ = v___y_3168_;
                                v___y_3244_ = v___y_3169_;
                                v___y_3245_ = v___y_3170_;
                                state = 14;
                                continue;
                            } else {
                                lean_dec(v_a_3262_);
                                lean_dec(v_g_3161_);
                                lean_dec_ref(v_unsatProver_3160_);
                                v_a_3273_ = lean_ctor_get(v___x_3272_, 0);
                                v_isSharedCheck_3280_ = (!lean_is_exclusive(v___x_3272_)) as u8;
                                if v_isSharedCheck_3280_ == 0 {
                                    v___x_3275_ = v___x_3272_;
                                    v_isShared_3276_ = v_isSharedCheck_3280_;
                                    state = 16;
                                    continue;
                                } else {
                                    lean_inc(v_a_3273_);
                                    lean_dec(v___x_3272_);
                                    v___x_3275_ = lean_box(0);
                                    v_isShared_3276_ = v_isSharedCheck_3280_;
                                    state = 16;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_dec(v_cls_3162_);
                    lean_dec(v_g_3161_);
                    lean_dec_ref(v_unsatProver_3160_);
                    v_a_3281_ = lean_ctor_get(v___y_3260_, 0);
                    v_isSharedCheck_3288_ = (!lean_is_exclusive(v___y_3260_)) as u8;
                    if v_isSharedCheck_3288_ == 0 {
                        v___x_3283_ = v___y_3260_;
                        v_isShared_3284_ = v_isSharedCheck_3288_;
                        state = 18;
                        continue;
                    } else {
                        lean_inc(v_a_3281_);
                        lean_dec(v___y_3260_);
                        v___x_3283_ = lean_box(0);
                        v_isShared_3284_ = v_isSharedCheck_3288_;
                        state = 18;
                        continue;
                    }
                }
            }
            16 => {
                if v_isShared_3276_ == 0 {
                    v___x_3278_ = v___x_3275_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_3279_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3279_, 0, v_a_3273_);
                    v___x_3278_ = v_reuseFailAlloc_3279_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_3278_;
            }
            18 => {
                if v_isShared_3284_ == 0 {
                    v___x_3286_ = v___x_3283_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_3287_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3287_, 0, v_a_3281_);
                    v___x_3286_ = v_reuseFailAlloc_3287_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_3286_;
            }
            20 => {
                v___x_3297_ = lean_io_mono_nanos_now();
                v___x_3298_ = lean_float_of_nat(v___y_3294_);
                v___x_3299_ = lean_float_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__6), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__6_once), _init_l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__6);
                v___x_3300_ = lean_float_div(v___x_3298_, v___x_3299_);
                v___x_3301_ = lean_float_of_nat(v___x_3297_);
                v___x_3302_ = lean_float_div(v___x_3301_, v___x_3299_);
                v___x_3303_ = lean_box_float(v___x_3300_);
                v___x_3304_ = lean_box_float(v___x_3302_);
                v___x_3305_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3305_, 0, v___x_3303_);
                lean_ctor_set(v___x_3305_, 1, v___x_3304_);
                v___x_3306_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3306_, 0, v_a_3296_);
                lean_ctor_set(v___x_3306_, 1, v___x_3305_);
                lean_inc(v_cls_3162_);
                v___x_3307_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9(v_cls_3162_, v___x_3163_, v___x_3164_, v_options_3256_, v___x_3292_, v___y_3295_, v___f_3165_, v___x_3306_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_);
                v___y_3260_ = v___x_3307_;
                state = 15;
                continue;
            }
            21 => {
                v___x_3312_ = lean_io_get_num_heartbeats();
                v___x_3313_ = lean_float_of_nat(v___y_3309_);
                v___x_3314_ = lean_float_of_nat(v___x_3312_);
                v___x_3315_ = lean_box_float(v___x_3313_);
                v___x_3316_ = lean_box_float(v___x_3314_);
                v___x_3317_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3317_, 0, v___x_3315_);
                lean_ctor_set(v___x_3317_, 1, v___x_3316_);
                v___x_3318_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3318_, 0, v_a_3311_);
                lean_ctor_set(v___x_3318_, 1, v___x_3317_);
                lean_inc(v_cls_3162_);
                v___x_3319_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9(v_cls_3162_, v___x_3163_, v___x_3164_, v_options_3256_, v___x_3292_, v___y_3310_, v___f_3165_, v___x_3318_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_);
                v___y_3260_ = v___x_3319_;
                state = 15;
                continue;
            }
            22 => {
                v___x_3321_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7___redArg(v___y_3170_);
                v_a_3322_ = lean_ctor_get(v___x_3321_, 0);
                lean_inc(v_a_3322_);
                lean_dec_ref(v___x_3321_);
                v___x_3323_ = l_Lean_trace_profiler_useHeartbeats;
                v___x_3324_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8(v_options_3256_, v___x_3323_);
                if v___x_3324_ == 0 {
                    v___x_3325_ = lean_io_mono_nanos_now();
                    lean_inc(v_g_3161_);
                    v___x_3326_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV(v_g_3161_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_);
                    if lean_obj_tag(v___x_3326_) == 0 {
                        v_a_3327_ = lean_ctor_get(v___x_3326_, 0);
                        v_isSharedCheck_3334_ = (!lean_is_exclusive(v___x_3326_)) as u8;
                        if v_isSharedCheck_3334_ == 0 {
                            v___x_3329_ = v___x_3326_;
                            v_isShared_3330_ = v_isSharedCheck_3334_;
                            state = 23;
                            continue;
                        } else {
                            lean_inc(v_a_3327_);
                            lean_dec(v___x_3326_);
                            v___x_3329_ = lean_box(0);
                            v_isShared_3330_ = v_isSharedCheck_3334_;
                            state = 23;
                            continue;
                        }
                    } else {
                        v_a_3335_ = lean_ctor_get(v___x_3326_, 0);
                        v_isSharedCheck_3342_ = (!lean_is_exclusive(v___x_3326_)) as u8;
                        if v_isSharedCheck_3342_ == 0 {
                            v___x_3337_ = v___x_3326_;
                            v_isShared_3338_ = v_isSharedCheck_3342_;
                            state = 25;
                            continue;
                        } else {
                            lean_inc(v_a_3335_);
                            lean_dec(v___x_3326_);
                            v___x_3337_ = lean_box(0);
                            v_isShared_3338_ = v_isSharedCheck_3342_;
                            state = 25;
                            continue;
                        }
                    }
                } else {
                    v___x_3343_ = lean_io_get_num_heartbeats();
                    lean_inc(v_g_3161_);
                    v___x_3344_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV(v_g_3161_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_);
                    if lean_obj_tag(v___x_3344_) == 0 {
                        v_a_3345_ = lean_ctor_get(v___x_3344_, 0);
                        v_isSharedCheck_3352_ = (!lean_is_exclusive(v___x_3344_)) as u8;
                        if v_isSharedCheck_3352_ == 0 {
                            v___x_3347_ = v___x_3344_;
                            v_isShared_3348_ = v_isSharedCheck_3352_;
                            state = 27;
                            continue;
                        } else {
                            lean_inc(v_a_3345_);
                            lean_dec(v___x_3344_);
                            v___x_3347_ = lean_box(0);
                            v_isShared_3348_ = v_isSharedCheck_3352_;
                            state = 27;
                            continue;
                        }
                    } else {
                        v_a_3353_ = lean_ctor_get(v___x_3344_, 0);
                        v_isSharedCheck_3360_ = (!lean_is_exclusive(v___x_3344_)) as u8;
                        if v_isSharedCheck_3360_ == 0 {
                            v___x_3355_ = v___x_3344_;
                            v_isShared_3356_ = v_isSharedCheck_3360_;
                            state = 29;
                            continue;
                        } else {
                            lean_inc(v_a_3353_);
                            lean_dec(v___x_3344_);
                            v___x_3355_ = lean_box(0);
                            v_isShared_3356_ = v_isSharedCheck_3360_;
                            state = 29;
                            continue;
                        }
                    }
                }
            }
            23 => {
                if v_isShared_3330_ == 0 {
                    lean_ctor_set_tag(v___x_3329_, 1);
                    v___x_3332_ = v___x_3329_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_3333_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3333_, 0, v_a_3327_);
                    v___x_3332_ = v_reuseFailAlloc_3333_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                v___y_3294_ = v___x_3325_;
                v___y_3295_ = v_a_3322_;
                v_a_3296_ = v___x_3332_;
                state = 20;
                continue;
            }
            25 => {
                if v_isShared_3338_ == 0 {
                    lean_ctor_set_tag(v___x_3337_, 0);
                    v___x_3340_ = v___x_3337_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_3341_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3341_, 0, v_a_3335_);
                    v___x_3340_ = v_reuseFailAlloc_3341_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                v___y_3294_ = v___x_3325_;
                v___y_3295_ = v_a_3322_;
                v_a_3296_ = v___x_3340_;
                state = 20;
                continue;
            }
            27 => {
                if v_isShared_3348_ == 0 {
                    lean_ctor_set_tag(v___x_3347_, 1);
                    v___x_3350_ = v___x_3347_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_3351_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3351_, 0, v_a_3345_);
                    v___x_3350_ = v_reuseFailAlloc_3351_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                v___y_3309_ = v___x_3343_;
                v___y_3310_ = v_a_3322_;
                v_a_3311_ = v___x_3350_;
                state = 21;
                continue;
            }
            29 => {
                if v_isShared_3356_ == 0 {
                    lean_ctor_set_tag(v___x_3355_, 0);
                    v___x_3358_ = v___x_3355_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_3359_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3359_, 0, v_a_3353_);
                    v___x_3358_ = v_reuseFailAlloc_3359_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                v___y_3309_ = v___x_3343_;
                v___y_3310_ = v_a_3322_;
                v_a_3311_ = v___x_3358_;
                state = 21;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___boxed(
    mut v_unsatProver_3364_: *mut LeanObject,
    mut v_g_3365_: *mut LeanObject,
    mut v_cls_3366_: *mut LeanObject,
    mut v___x_3367_: *mut LeanObject,
    mut v___x_3368_: *mut LeanObject,
    mut v___f_3369_: *mut LeanObject,
    mut v___y_3370_: *mut LeanObject,
    mut v___y_3371_: *mut LeanObject,
    mut v___y_3372_: *mut LeanObject,
    mut v___y_3373_: *mut LeanObject,
    mut v___y_3374_: *mut LeanObject,
    mut v___y_3375_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_17421__boxed_3376_: u8 = 0;
    let mut v_res_3377_: *mut LeanObject = core::ptr::null_mut();
    v___x_17421__boxed_3376_ = (lean_unbox(v___x_3367_) as u8);
    v_res_3377_ = l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1(
        v_unsatProver_3364_,
        v_g_3365_,
        v_cls_3366_,
        v___x_17421__boxed_3376_,
        v___x_3368_,
        v___f_3369_,
        v___y_3370_,
        v___y_3371_,
        v___y_3372_,
        v___y_3373_,
        v___y_3374_,
    );
    lean_dec(v___y_3374_);
    lean_dec_ref(v___y_3373_);
    lean_dec(v___y_3372_);
    lean_dec_ref(v___y_3371_);
    lean_dec(v___y_3370_);
    return v_res_3377_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg(
    mut v_g_3386_: *mut LeanObject,
    mut v_unsatProver_3387_: *mut LeanObject,
    mut v_a_3388_: *mut LeanObject,
    mut v_a_3389_: *mut LeanObject,
    mut v_a_3390_: *mut LeanObject,
    mut v_a_3391_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cls_3394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3395_: u8 = 0;
    let mut v___x_3396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3400_: *mut LeanObject = core::ptr::null_mut();
    v___f_3393_ = l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___closed__0;
    v_cls_3394_ = l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___closed__4;
    v___x_3395_ = 1;
    v___x_3396_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6___redArg___closed__0;
    v___x_3397_ = lean_box((v___x_3395_) as usize);
    lean_inc(v_g_3386_);
    v___f_3398_ = lean_alloc_closure(
        l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        12,
        6,
    );
    lean_closure_set(v___f_3398_, 0, v_unsatProver_3387_);
    lean_closure_set(v___f_3398_, 1, v_g_3386_);
    lean_closure_set(v___f_3398_, 2, v_cls_3394_);
    lean_closure_set(v___f_3398_, 3, v___x_3397_);
    lean_closure_set(v___f_3398_, 4, v___x_3396_);
    lean_closure_set(v___f_3398_, 5, v___f_3393_);
    v___x_3399_ = lean_alloc_closure(l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Basic_0__Lean_Meta_Tactic_BVDecide_reflectBV_spec__4___boxed as *mut core::ffi::c_void, 9, 3);
    lean_closure_set(v___x_3399_, 0, lean_box(0));
    lean_closure_set(v___x_3399_, 1, v_g_3386_);
    lean_closure_set(v___x_3399_, 2, v___f_3398_);
    v___x_3400_ = l_Lean_Meta_Tactic_BVDecide_M_run___redArg(
        v___x_3399_,
        v_a_3388_,
        v_a_3389_,
        v_a_3390_,
        v_a_3391_,
    );
    return v___x_3400_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___boxed(
    mut v_g_3401_: *mut LeanObject,
    mut v_unsatProver_3402_: *mut LeanObject,
    mut v_a_3403_: *mut LeanObject,
    mut v_a_3404_: *mut LeanObject,
    mut v_a_3405_: *mut LeanObject,
    mut v_a_3406_: *mut LeanObject,
    mut v_a_3407_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3408_: *mut LeanObject = core::ptr::null_mut();
    v_res_3408_ = l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg(
        v_g_3401_,
        v_unsatProver_3402_,
        v_a_3403_,
        v_a_3404_,
        v_a_3405_,
        v_a_3406_,
    );
    lean_dec(v_a_3406_);
    lean_dec_ref(v_a_3405_);
    lean_dec(v_a_3404_);
    lean_dec_ref(v_a_3403_);
    return v_res_3408_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection(
    mut v_00_u03b1_3409_: *mut LeanObject,
    mut v_g_3410_: *mut LeanObject,
    mut v_unsatProver_3411_: *mut LeanObject,
    mut v_a_3412_: *mut LeanObject,
    mut v_a_3413_: *mut LeanObject,
    mut v_a_3414_: *mut LeanObject,
    mut v_a_3415_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3417_: *mut LeanObject = core::ptr::null_mut();
    v___x_3417_ = l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg(
        v_g_3410_,
        v_unsatProver_3411_,
        v_a_3412_,
        v_a_3413_,
        v_a_3414_,
        v_a_3415_,
    );
    return v___x_3417_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___boxed(
    mut v_00_u03b1_3418_: *mut LeanObject,
    mut v_g_3419_: *mut LeanObject,
    mut v_unsatProver_3420_: *mut LeanObject,
    mut v_a_3421_: *mut LeanObject,
    mut v_a_3422_: *mut LeanObject,
    mut v_a_3423_: *mut LeanObject,
    mut v_a_3424_: *mut LeanObject,
    mut v_a_3425_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3426_: *mut LeanObject = core::ptr::null_mut();
    v_res_3426_ = l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection(
        v_00_u03b1_3418_,
        v_g_3419_,
        v_unsatProver_3420_,
        v_a_3421_,
        v_a_3422_,
        v_a_3423_,
        v_a_3424_,
    );
    lean_dec(v_a_3424_);
    lean_dec_ref(v_a_3423_);
    lean_dec(v_a_3422_);
    lean_dec_ref(v_a_3421_);
    return v_res_3426_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2(
    mut v_mvarId_3427_: *mut LeanObject,
    mut v_val_3428_: *mut LeanObject,
    mut v___y_3429_: *mut LeanObject,
    mut v___y_3430_: *mut LeanObject,
    mut v___y_3431_: *mut LeanObject,
    mut v___y_3432_: *mut LeanObject,
    mut v___y_3433_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3435_: *mut LeanObject = core::ptr::null_mut();
    v___x_3435_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___redArg(v_mvarId_3427_, v_val_3428_, v___y_3431_);
    return v___x_3435_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___boxed(
    mut v_mvarId_3436_: *mut LeanObject,
    mut v_val_3437_: *mut LeanObject,
    mut v___y_3438_: *mut LeanObject,
    mut v___y_3439_: *mut LeanObject,
    mut v___y_3440_: *mut LeanObject,
    mut v___y_3441_: *mut LeanObject,
    mut v___y_3442_: *mut LeanObject,
    mut v___y_3443_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3444_: *mut LeanObject = core::ptr::null_mut();
    v_res_3444_ =
        l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2(
            v_mvarId_3436_,
            v_val_3437_,
            v___y_3438_,
            v___y_3439_,
            v___y_3440_,
            v___y_3441_,
            v___y_3442_,
        );
    lean_dec(v___y_3442_);
    lean_dec_ref(v___y_3441_);
    lean_dec(v___y_3440_);
    lean_dec_ref(v___y_3439_);
    lean_dec(v___y_3438_);
    return v_res_3444_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6(
    mut v_cls_3445_: *mut LeanObject,
    mut v_msg_3446_: *mut LeanObject,
    mut v___y_3447_: *mut LeanObject,
    mut v___y_3448_: *mut LeanObject,
    mut v___y_3449_: *mut LeanObject,
    mut v___y_3450_: *mut LeanObject,
    mut v___y_3451_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3453_: *mut LeanObject = core::ptr::null_mut();
    v___x_3453_ =
        l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6___redArg(
            v_cls_3445_,
            v_msg_3446_,
            v___y_3448_,
            v___y_3449_,
            v___y_3450_,
            v___y_3451_,
        );
    return v___x_3453_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6___boxed(
    mut v_cls_3454_: *mut LeanObject,
    mut v_msg_3455_: *mut LeanObject,
    mut v___y_3456_: *mut LeanObject,
    mut v___y_3457_: *mut LeanObject,
    mut v___y_3458_: *mut LeanObject,
    mut v___y_3459_: *mut LeanObject,
    mut v___y_3460_: *mut LeanObject,
    mut v___y_3461_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3462_: *mut LeanObject = core::ptr::null_mut();
    v_res_3462_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6(
        v_cls_3454_,
        v_msg_3455_,
        v___y_3456_,
        v___y_3457_,
        v___y_3458_,
        v___y_3459_,
        v___y_3460_,
    );
    lean_dec(v___y_3460_);
    lean_dec_ref(v___y_3459_);
    lean_dec(v___y_3458_);
    lean_dec_ref(v___y_3457_);
    lean_dec(v___y_3456_);
    return v_res_3462_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__14(
    mut v_00_u03b1_3463_: *mut LeanObject,
    mut v_x_3464_: *mut LeanObject,
    mut v___y_3465_: *mut LeanObject,
    mut v___y_3466_: *mut LeanObject,
    mut v___y_3467_: *mut LeanObject,
    mut v___y_3468_: *mut LeanObject,
    mut v___y_3469_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3471_: *mut LeanObject = core::ptr::null_mut();
    v___x_3471_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__14___redArg(v_x_3464_);
    return v___x_3471_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__14___boxed(
    mut v_00_u03b1_3472_: *mut LeanObject,
    mut v_x_3473_: *mut LeanObject,
    mut v___y_3474_: *mut LeanObject,
    mut v___y_3475_: *mut LeanObject,
    mut v___y_3476_: *mut LeanObject,
    mut v___y_3477_: *mut LeanObject,
    mut v___y_3478_: *mut LeanObject,
    mut v___y_3479_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3480_: *mut LeanObject = core::ptr::null_mut();
    v_res_3480_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__14(v_00_u03b1_3472_, v_x_3473_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_);
    lean_dec(v___y_3478_);
    lean_dec_ref(v___y_3477_);
    lean_dec(v___y_3476_);
    lean_dec_ref(v___y_3475_);
    lean_dec(v___y_3474_);
    return v_res_3480_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1(
    mut v_00_u03b2_3481_: *mut LeanObject,
    mut v_m_3482_: *mut LeanObject,
    mut v_a_3483_: *mut LeanObject,
    mut v_b_3484_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3485_: *mut LeanObject = core::ptr::null_mut();
    v___x_3485_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1___redArg(v_m_3482_, v_a_3483_, v_b_3484_);
    return v___x_3485_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__2(
    mut v_as_3486_: *mut LeanObject,
    mut v_as_x27_3487_: *mut LeanObject,
    mut v_b_3488_: *mut LeanObject,
    mut v_a_3489_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3490_: *mut LeanObject = core::ptr::null_mut();
    v___x_3490_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__2___redArg(v_as_x27_3487_, v_b_3488_);
    return v___x_3490_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__2___boxed(
    mut v_as_3491_: *mut LeanObject,
    mut v_as_x27_3492_: *mut LeanObject,
    mut v_b_3493_: *mut LeanObject,
    mut v_a_3494_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3495_: *mut LeanObject = core::ptr::null_mut();
    v_res_3495_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__2(v_as_3491_, v_as_x27_3492_, v_b_3493_, v_a_3494_);
    lean_dec(v_as_x27_3492_);
    lean_dec(v_as_3491_);
    return v_res_3495_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4(
    mut v_00_u03b2_3496_: *mut LeanObject,
    mut v_x_3497_: *mut LeanObject,
    mut v_x_3498_: *mut LeanObject,
    mut v_x_3499_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3500_: *mut LeanObject = core::ptr::null_mut();
    v___x_3500_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4___redArg(v_x_3497_, v_x_3498_, v_x_3499_);
    return v___x_3500_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__13(
    mut v_oldTraces_3501_: *mut LeanObject,
    mut v_data_3502_: *mut LeanObject,
    mut v_ref_3503_: *mut LeanObject,
    mut v_msg_3504_: *mut LeanObject,
    mut v___y_3505_: *mut LeanObject,
    mut v___y_3506_: *mut LeanObject,
    mut v___y_3507_: *mut LeanObject,
    mut v___y_3508_: *mut LeanObject,
    mut v___y_3509_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3511_: *mut LeanObject = core::ptr::null_mut();
    v___x_3511_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__13___redArg(v_oldTraces_3501_, v_data_3502_, v_ref_3503_, v_msg_3504_, v___y_3506_, v___y_3507_, v___y_3508_, v___y_3509_);
    return v___x_3511_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__13___boxed(
    mut v_oldTraces_3512_: *mut LeanObject,
    mut v_data_3513_: *mut LeanObject,
    mut v_ref_3514_: *mut LeanObject,
    mut v_msg_3515_: *mut LeanObject,
    mut v___y_3516_: *mut LeanObject,
    mut v___y_3517_: *mut LeanObject,
    mut v___y_3518_: *mut LeanObject,
    mut v___y_3519_: *mut LeanObject,
    mut v___y_3520_: *mut LeanObject,
    mut v___y_3521_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3522_: *mut LeanObject = core::ptr::null_mut();
    v_res_3522_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__13(v_oldTraces_3512_, v_data_3513_, v_ref_3514_, v_msg_3515_, v___y_3516_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_);
    lean_dec(v___y_3520_);
    lean_dec_ref(v___y_3519_);
    lean_dec(v___y_3518_);
    lean_dec_ref(v___y_3517_);
    lean_dec(v___y_3516_);
    return v_res_3522_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__4(
    mut v_00_u03b2_3523_: *mut LeanObject,
    mut v_a_3524_: *mut LeanObject,
    mut v_x_3525_: *mut LeanObject,
) -> u8 {
    let mut v___x_3526_: u8 = 0;
    v___x_3526_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__4___redArg(v_a_3524_, v_x_3525_);
    return v___x_3526_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__4___boxed(
    mut v_00_u03b2_3527_: *mut LeanObject,
    mut v_a_3528_: *mut LeanObject,
    mut v_x_3529_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3530_: u8 = 0;
    let mut v_r_3531_: *mut LeanObject = core::ptr::null_mut();
    v_res_3530_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__4(v_00_u03b2_3527_, v_a_3528_, v_x_3529_);
    lean_dec(v_x_3529_);
    lean_dec(v_a_3528_);
    v_r_3531_ = lean_box((v_res_3530_) as usize);
    return v_r_3531_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__5(
    mut v_00_u03b2_3532_: *mut LeanObject,
    mut v_data_3533_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3534_: *mut LeanObject = core::ptr::null_mut();
    v___x_3534_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__5___redArg(v_data_3533_);
    return v___x_3534_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__6(
    mut v_00_u03b2_3535_: *mut LeanObject,
    mut v_a_3536_: *mut LeanObject,
    mut v_b_3537_: *mut LeanObject,
    mut v_x_3538_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3539_: *mut LeanObject = core::ptr::null_mut();
    v___x_3539_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__6___redArg(v_a_3536_, v_b_3537_, v_x_3538_);
    return v___x_3539_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10(
    mut v_00_u03b2_3540_: *mut LeanObject,
    mut v_x_3541_: *mut LeanObject,
    mut v_x_3542_: usize,
    mut v_x_3543_: usize,
    mut v_x_3544_: *mut LeanObject,
    mut v_x_3545_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3546_: *mut LeanObject = core::ptr::null_mut();
    v___x_3546_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10___redArg(v_x_3541_, v_x_3542_, v_x_3543_, v_x_3544_, v_x_3545_);
    return v___x_3546_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10___boxed(
    mut v_00_u03b2_3547_: *mut LeanObject,
    mut v_x_3548_: *mut LeanObject,
    mut v_x_3549_: *mut LeanObject,
    mut v_x_3550_: *mut LeanObject,
    mut v_x_3551_: *mut LeanObject,
    mut v_x_3552_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_17997__boxed_3553_: usize = 0;
    let mut v_x_17998__boxed_3554_: usize = 0;
    let mut v_res_3555_: *mut LeanObject = core::ptr::null_mut();
    v_x_17997__boxed_3553_ = lean_unbox_usize(v_x_3549_);
    lean_dec(v_x_3549_);
    v_x_17998__boxed_3554_ = lean_unbox_usize(v_x_3550_);
    lean_dec(v_x_3550_);
    v_res_3555_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10(v_00_u03b2_3547_, v_x_3548_, v_x_17997__boxed_3553_, v_x_17998__boxed_3554_, v_x_3551_, v_x_3552_);
    return v_res_3555_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__5_spec__15(
    mut v_00_u03b2_3556_: *mut LeanObject,
    mut v_i_3557_: *mut LeanObject,
    mut v_source_3558_: *mut LeanObject,
    mut v_target_3559_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3560_: *mut LeanObject = core::ptr::null_mut();
    v___x_3560_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__5_spec__15___redArg(v_i_3557_, v_source_3558_, v_target_3559_);
    return v___x_3560_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10_spec__20(
    mut v_00_u03b2_3561_: *mut LeanObject,
    mut v_n_3562_: *mut LeanObject,
    mut v_k_3563_: *mut LeanObject,
    mut v_v_3564_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3565_: *mut LeanObject = core::ptr::null_mut();
    v___x_3565_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10_spec__20___redArg(v_n_3562_, v_k_3563_, v_v_3564_);
    return v___x_3565_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10_spec__21(
    mut v_00_u03b2_3566_: *mut LeanObject,
    mut v_depth_3567_: usize,
    mut v_keys_3568_: *mut LeanObject,
    mut v_vals_3569_: *mut LeanObject,
    mut v_heq_3570_: *mut LeanObject,
    mut v_i_3571_: *mut LeanObject,
    mut v_entries_3572_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3573_: *mut LeanObject = core::ptr::null_mut();
    v___x_3573_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10_spec__21___redArg(v_depth_3567_, v_keys_3568_, v_vals_3569_, v_i_3571_, v_entries_3572_);
    return v___x_3573_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10_spec__21___boxed(
    mut v_00_u03b2_3574_: *mut LeanObject,
    mut v_depth_3575_: *mut LeanObject,
    mut v_keys_3576_: *mut LeanObject,
    mut v_vals_3577_: *mut LeanObject,
    mut v_heq_3578_: *mut LeanObject,
    mut v_i_3579_: *mut LeanObject,
    mut v_entries_3580_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_3581_: usize = 0;
    let mut v_res_3582_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_3581_ = lean_unbox_usize(v_depth_3575_);
    lean_dec(v_depth_3575_);
    v_res_3582_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10_spec__21(v_00_u03b2_3574_, v_depth_boxed_3581_, v_keys_3576_, v_vals_3577_, v_heq_3578_, v_i_3579_, v_entries_3580_);
    lean_dec_ref(v_vals_3577_);
    lean_dec_ref(v_keys_3576_);
    return v_res_3582_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__5_spec__15_spec__19(
    mut v_00_u03b2_3583_: *mut LeanObject,
    mut v_x_3584_: *mut LeanObject,
    mut v_x_3585_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3586_: *mut LeanObject = core::ptr::null_mut();
    v___x_3586_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__5_spec__15_spec__19___redArg(v_x_3584_, v_x_3585_);
    return v___x_3586_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10_spec__20_spec__23(
    mut v_00_u03b2_3587_: *mut LeanObject,
    mut v_x_3588_: *mut LeanObject,
    mut v_x_3589_: *mut LeanObject,
    mut v_x_3590_: *mut LeanObject,
    mut v_x_3591_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3592_: *mut LeanObject = core::ptr::null_mut();
    v___x_3592_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10_spec__20_spec__23___redArg(v_x_3588_, v_x_3589_, v_x_3590_, v_x_3591_);
    return v___x_3592_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_BVDecide_Prover_Basic(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Counterexample(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_LRAT_Cert(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_BVDecide_Prover_Basic(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_BVDecide_Prover_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_BVDecide_Reflect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_BVDecide_Counterexample(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_BVDecide_LRAT_Cert(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Prover_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_BVDecide_Prover_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_BVDecide_Prover_Basic(builtin);
}
