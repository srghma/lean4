// Lean compiler output
// Module: Lean.Meta.SplitSparseCasesOn
// Imports: Lean.Meta.Basic Lean.Meta.Tactic.Rewrite Lean.Meta.Constructions.SparseCasesOn Lean.Meta.Constructions.SparseCasesOnEq Lean.Meta.HasNotBit Lean.Meta.Tactic.Cases Lean.Meta.Tactic.Replace
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Data::Slice::Array::Iterator::l_Subarray_copy___redArg;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_mkStr3, l_Lean_replaceRef,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_instInhabitedOfMonad___redArg,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instMonadCoreM___lam__0___boxed, l_Lean_Core_instMonadCoreM___lam__1___boxed,
    l_Lean_Exception_isRuntime,
};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::PersistentArray::{
    l_Lean_PersistentArray_append___redArg, l_Lean_PersistentArray_push___redArg,
    l_Lean_PersistentArray_toArray___redArg,
};
use crate::r#gen::Lean::Environment::{
    l_Lean_AsyncConstantInfo_toConstantInfo, l_Lean_Environment_findAsync_x3f,
};
use crate::r#gen::Lean::Exception::{l_Lean_Exception_isInterrupt, l_Lean_Exception_toMessageData};
use crate::r#gen::Lean::Expr::{
    l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux, l_Lean_Expr_app___override,
    l_Lean_Expr_constLevels_x21, l_Lean_Expr_fvarId_x21, l_Lean_Expr_getAppFn,
    l_Lean_Expr_getAppNumArgs, l_Lean_Expr_isFVar, l_Lean_Expr_sort___override,
    l_Lean_instInhabitedExpr, l_Lean_mkAppN, l_Lean_mkConst, l_Lean_mkRawNatLit,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofList,
    l_Lean_indentD, l_Lean_indentExpr, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    initialize_Lean_Meta_Basic, l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp,
    l_Lean_Meta_instMonadMetaM___lam__0___boxed, l_Lean_Meta_instMonadMetaM___lam__1___boxed,
    runtime_initialize_Lean_Meta_Basic,
};
use crate::r#gen::Lean::Meta::Constructions::SparseCasesOn::{
    initialize_Lean_Meta_Constructions_SparseCasesOn, l_Lean_Meta_getSparseCasesOnInfo___redArg,
    runtime_initialize_Lean_Meta_Constructions_SparseCasesOn,
};
use crate::r#gen::Lean::Meta::Constructions::SparseCasesOnEq::{
    initialize_Lean_Meta_Constructions_SparseCasesOnEq, l_Lean_Meta_getSparseCasesOnEq,
    runtime_initialize_Lean_Meta_Constructions_SparseCasesOnEq,
};
use crate::r#gen::Lean::Meta::CtorRecognizer::l_Lean_Meta_isConstructorApp_x27_x3f;
use crate::r#gen::Lean::Meta::HasNotBit::{
    initialize_Lean_Meta_HasNotBit, l_mkHasNotBitProof, runtime_initialize_Lean_Meta_HasNotBit,
};
use crate::r#gen::Lean::Meta::MatchUtil::l_Lean_Meta_matchEqHEqLHS_x3f;
use crate::r#gen::Lean::Meta::Tactic::Cases::{
    initialize_Lean_Meta_Tactic_Cases, l_Lean_MVarId_cases,
    runtime_initialize_Lean_Meta_Tactic_Cases,
};
use crate::r#gen::Lean::Meta::Tactic::Replace::{
    initialize_Lean_Meta_Tactic_Replace, l_Lean_MVarId_modifyTargetEqLHS,
    l_Lean_MVarId_replaceTargetEq, runtime_initialize_Lean_Meta_Tactic_Replace,
};
use crate::r#gen::Lean::Meta::Tactic::Rewrite::{
    initialize_Lean_Meta_Tactic_Rewrite, l_Lean_MVarId_rewrite,
    runtime_initialize_Lean_Meta_Tactic_Rewrite,
};
use crate::r#gen::Lean::Meta::Tactic::Util::l_Lean_MVarId_getType;
use crate::r#gen::Lean::Meta::WHNF::l_Lean_Meta_unfoldDefinition___boxed;
use crate::r#gen::Lean::Util::Trace::{
    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go, l_Lean_TraceResult_toEmoji,
    l_Lean_trace_profiler, l_Lean_trace_profiler_threshold, l_Lean_trace_profiler_useHeartbeats,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_set;
use crate::lean_imports_rs::Init::Data::Float::{lean_float_decLt, lean_float_div, lean_float_sub};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get, lean_array_get_borrowed, lean_array_get_size, lean_array_push,
    lean_array_to_list, lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_dec_eq,
    lean_nat_dec_lt, lean_nat_sub, lean_panic_fn_borrowed, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::IO::{
    lean_io_get_num_heartbeats, lean_io_mono_nanos_now,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
pub static l___private_Lean_Meta_SplitSparseCasesOn_0__Lean_Meta_rewriteGoalUsingEq___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 8) as u16, other: 1, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,258 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_SplitSparseCasesOn_0__Lean_Meta_rewriteGoalUsingEq___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_SplitSparseCasesOn_0__Lean_Meta_rewriteGoalUsingEq___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__2_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__3_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__4_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__2_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 0]};
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__2_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__4_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [76, 101, 97, 110, 46, 77, 111, 110, 97, 100, 69, 110, 118, 0]};
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__5_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [76, 101, 97, 110, 46, 105, 115, 67, 116, 111, 114, 63, 0]};
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__6_value: crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__6_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__1_value: crate::leanh::LeanStringObject<48> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 48, m_capacity: 48, m_length: 47, m_data: [77, 97, 106, 111, 114, 32, 112, 114, 101, 109, 105, 115, 101, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32, 97, 112, 112, 108, 105, 99, 97, 116, 105, 111, 110, 58, 0]};
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__0_value: crate::leanh::LeanStringObject<52> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 52, m_capacity: 52, m_length: 51, m_data: [78, 111, 116, 32, 101, 110, 111, 117, 103, 104, 32, 97, 114, 103, 117, 109, 101, 110, 116, 115, 32, 102, 111, 114, 32, 115, 112, 97, 114, 115, 101, 32, 99, 97, 115, 101, 115, 79, 110, 32, 97, 112, 112, 108, 105, 99, 97, 116, 105, 111, 110, 0]};
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___closed__0_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [115, 112, 108, 105, 116, 83, 112, 97, 114, 115, 101, 67, 97, 115, 101, 115, 79, 110, 0]};
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__2: f64 = 0.0;
pub static l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__3_value: crate::leanh::LeanStringObject<54> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [60, 101, 120, 99, 101, 112, 116, 105, 111, 110, 32, 116, 104, 114, 111, 119, 110, 32, 119, 104, 105, 108, 101, 32, 112, 114, 111, 100, 117, 99, 105, 110, 103, 32, 116, 114, 97, 99, 101, 32, 110, 111, 100, 101, 32, 109, 101, 115, 115, 97, 103, 101, 62, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__5: f64 = 0.0;
pub static l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_unfoldDefinition___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__2_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__3_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [77, 97, 116, 99, 104, 0]};
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__4_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [109, 97, 116, 99, 104, 69, 113, 115, 0]};
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__4_value
) as *mut crate::leanh::LeanObject;
static l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__2_value) as *mut crate::leanh::LeanObject,142734480563613395 as *mut crate::leanh::LeanObject] };
static l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__5_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__5_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__3_value) as *mut crate::leanh::LeanObject,17634115403684839930 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__5_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__4_value) as *mut crate::leanh::LeanObject,4128573869278761614 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__6_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__6_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__7_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__7_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__7_value) as *mut crate::leanh::LeanObject,14231257465488249300 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__8_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__10_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__10: f64 =
    0.0;
pub static l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__11_value: crate::leanh::LeanStringObject<33> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [78, 111, 116, 32, 97, 32, 115, 112, 97, 114, 115, 101, 32, 99, 97, 115, 101, 115, 79, 110, 32, 97, 112, 112, 108, 105, 99, 97, 116, 105, 111, 110, 0]};
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__11_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__12_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__13_value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [78, 111, 116, 32, 97, 32, 99, 111, 110, 115, 116, 32, 97, 112, 112, 108, 105, 99, 97, 116, 105, 111, 110, 0]};
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__13_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__14_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__14:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_reduceSparseCasesOn___closed__0_value: crate::leanh::LeanStringObject<23> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 23,
        m_capacity: 23,
        m_length: 22,
        m_data: [
            84, 97, 114, 103, 101, 116, 32, 110, 111, 116, 32, 97, 110, 32, 101, 113, 117, 97, 108,
            105, 116, 121, 0,
        ],
    };
static mut l_Lean_Meta_reduceSparseCasesOn___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_reduceSparseCasesOn___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_reduceSparseCasesOn___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_reduceSparseCasesOn___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___closed__0_value: crate::leanh::LeanStringObject<51> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 51, m_capacity: 51, m_length: 50, m_data: [85, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 110, 117, 109, 98, 101, 114, 32, 111, 102, 32, 102, 105, 101, 108, 100, 115, 32, 102, 111, 114, 32, 99, 97, 116, 99, 104, 45, 97, 108, 108, 32, 98, 114, 97, 110, 99, 104, 58, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__1_value: crate::leanh::LeanStringObject<38> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 38, m_capacity: 38, m_length: 37, m_data: [77, 97, 106, 111, 114, 32, 112, 114, 101, 109, 105, 115, 101, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 102, 114, 101, 101, 32, 118, 97, 114, 105, 97, 98, 108, 101, 58, 0]};
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0___closed__0_value:
    crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__0_value: crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [115, 112, 108, 105, 116, 83, 112, 97, 114, 115, 101, 67, 97, 115, 101, 115, 79, 110, 32, 102, 97, 105, 108, 101, 100, 0]};
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__2_value: crate::leanh::LeanStringObject<31> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 31, m_capacity: 31, m_length: 30, m_data: [115, 112, 108, 105, 116, 83, 112, 97, 114, 115, 101, 67, 97, 115, 101, 115, 79, 110, 32, 114, 117, 110, 110, 105, 110, 103, 32, 111, 110, 10, 0]};
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__2_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l___private_Lean_Meta_SplitSparseCasesOn_0__Lean_Meta_rewriteGoalUsingEq(
    mut v_goal_2044_: *mut crate::leanh::LeanObject,
    mut v_eq_2045_: *mut crate::leanh::LeanObject,
    mut v_symm_2046_: u8,
    mut v_a_2047_: *mut crate::leanh::LeanObject,
    mut v_a_2048_: *mut crate::leanh::LeanObject,
    mut v_a_2049_: *mut crate::leanh::LeanObject,
    mut v_a_2050_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eNew_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eqProof_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2063_: u8 = 0;
    let mut v___x_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2067_: u8 = 0;
    let mut v_a_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2071_: u8 = 0;
    let mut v___x_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2075_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_goal_2044_);
                v___x_2052_ =
                    l_Lean_MVarId_getType(v_goal_2044_, v_a_2047_, v_a_2048_, v_a_2049_, v_a_2050_);
                if crate::leanh::lean_obj_tag(v___x_2052_) == 0 {
                    v_a_2053_ = crate::leanh::lean_ctor_get(v___x_2052_, 0);
                    crate::leanh::lean_inc(v_a_2053_);
                    crate::leanh::lean_dec_ref_known(v___x_2052_, 1);
                    v___x_2054_ = l___private_Lean_Meta_SplitSparseCasesOn_0__Lean_Meta_rewriteGoalUsingEq___closed__0;
                    crate::leanh::lean_inc(v_goal_2044_);
                    v___x_2055_ = l_Lean_MVarId_rewrite(
                        v_goal_2044_,
                        v_a_2053_,
                        v_eq_2045_,
                        v_symm_2046_,
                        v___x_2054_,
                        v_a_2047_,
                        v_a_2048_,
                        v_a_2049_,
                        v_a_2050_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2055_) == 0 {
                        v_a_2056_ = crate::leanh::lean_ctor_get(v___x_2055_, 0);
                        crate::leanh::lean_inc(v_a_2056_);
                        crate::leanh::lean_dec_ref_known(v___x_2055_, 1);
                        v_eNew_2057_ = crate::leanh::lean_ctor_get(v_a_2056_, 0);
                        crate::leanh::lean_inc_ref(v_eNew_2057_);
                        v_eqProof_2058_ = crate::leanh::lean_ctor_get(v_a_2056_, 1);
                        crate::leanh::lean_inc_ref(v_eqProof_2058_);
                        crate::leanh::lean_dec(v_a_2056_);
                        v___x_2059_ = l_Lean_MVarId_replaceTargetEq(
                            v_goal_2044_,
                            v_eNew_2057_,
                            v_eqProof_2058_,
                            v_a_2047_,
                            v_a_2048_,
                            v_a_2049_,
                            v_a_2050_,
                        );
                        return v___x_2059_;
                    } else {
                        crate::leanh::lean_dec(v_goal_2044_);
                        v_a_2060_ = crate::leanh::lean_ctor_get(v___x_2055_, 0);
                        v_isSharedCheck_2067_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2055_)) as u8;
                        if v_isSharedCheck_2067_ == 0 {
                            v___x_2062_ = v___x_2055_;
                            v_isShared_2063_ = v_isSharedCheck_2067_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2060_);
                            crate::leanh::lean_dec(v___x_2055_);
                            v___x_2062_ = crate::leanh::lean_box(0);
                            v_isShared_2063_ = v_isSharedCheck_2067_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_eq_2045_);
                    crate::leanh::lean_dec(v_goal_2044_);
                    v_a_2068_ = crate::leanh::lean_ctor_get(v___x_2052_, 0);
                    v_isSharedCheck_2075_ = (!crate::leanh::lean_is_exclusive(v___x_2052_)) as u8;
                    if v_isSharedCheck_2075_ == 0 {
                        v___x_2070_ = v___x_2052_;
                        v_isShared_2071_ = v_isSharedCheck_2075_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2068_);
                        crate::leanh::lean_dec(v___x_2052_);
                        v___x_2070_ = crate::leanh::lean_box(0);
                        v_isShared_2071_ = v_isSharedCheck_2075_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2063_ == 0 {
                    v___x_2065_ = v___x_2062_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2066_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2066_, 0, v_a_2060_);
                    v___x_2065_ = v_reuseFailAlloc_2066_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2065_;
            }
            3 => {
                if v_isShared_2071_ == 0 {
                    v___x_2073_ = v___x_2070_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2074_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2074_, 0, v_a_2068_);
                    v___x_2073_ = v_reuseFailAlloc_2074_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2073_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_SplitSparseCasesOn_0__Lean_Meta_rewriteGoalUsingEq___boxed(
    mut v_goal_2076_: *mut crate::leanh::LeanObject,
    mut v_eq_2077_: *mut crate::leanh::LeanObject,
    mut v_symm_2078_: *mut crate::leanh::LeanObject,
    mut v_a_2079_: *mut crate::leanh::LeanObject,
    mut v_a_2080_: *mut crate::leanh::LeanObject,
    mut v_a_2081_: *mut crate::leanh::LeanObject,
    mut v_a_2082_: *mut crate::leanh::LeanObject,
    mut v_a_2083_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_symm_boxed_2084_: u8 = 0;
    let mut v_res_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_symm_boxed_2084_ = (crate::leanh::lean_unbox(v_symm_2078_) as u8);
    v_res_2085_ = l___private_Lean_Meta_SplitSparseCasesOn_0__Lean_Meta_rewriteGoalUsingEq(
        v_goal_2076_,
        v_eq_2077_,
        v_symm_boxed_2084_,
        v_a_2079_,
        v_a_2080_,
        v_a_2081_,
        v_a_2082_,
    );
    crate::leanh::lean_dec(v_a_2082_);
    crate::leanh::lean_dec_ref(v_a_2081_);
    crate::leanh::lean_dec(v_a_2080_);
    crate::leanh::lean_dec_ref(v_a_2079_);
    return v_res_2085_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2086_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_2087_ = lean_mk_empty_array_with_capacity(v___x_2086_);
    v___x_2088_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2088_, 0, v___x_2087_);
    return v___x_2088_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2089_: usize = 0;
    let mut v___x_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2089_ = 5usize;
    v___x_2090_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2091_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_2092_ = lean_mk_empty_array_with_capacity(v___x_2091_);
    v___x_2093_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg___closed__0_once), _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg___closed__0);
    v___x_2094_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_2094_, 0, v___x_2093_);
    crate::leanh::lean_ctor_set(v___x_2094_, 1, v___x_2092_);
    crate::leanh::lean_ctor_set(v___x_2094_, 2, v___x_2090_);
    crate::leanh::lean_ctor_set(v___x_2094_, 3, v___x_2090_);
    crate::leanh::lean_ctor_set_usize(v___x_2094_, 4, v___x_2089_);
    return v___x_2094_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg(
    mut v___y_2095_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traces_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2112_: u8 = 0;
    let mut v_tid_2113_: u64 = 0;
    let mut v___x_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2116_: u8 = 0;
    let mut v___x_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2126_: u8 = 0;
    let mut v_unused_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2128_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2097_ = lean_st_ref_get(v___y_2095_);
                v_traceState_2098_ = crate::leanh::lean_ctor_get(v___x_2097_, 4);
                crate::leanh::lean_inc_ref(v_traceState_2098_);
                crate::leanh::lean_dec(v___x_2097_);
                v_traces_2099_ = crate::leanh::lean_ctor_get(v_traceState_2098_, 0);
                crate::leanh::lean_inc_ref(v_traces_2099_);
                crate::leanh::lean_dec_ref(v_traceState_2098_);
                v___x_2100_ = lean_st_ref_take(v___y_2095_);
                v_traceState_2101_ = crate::leanh::lean_ctor_get(v___x_2100_, 4);
                v_env_2102_ = crate::leanh::lean_ctor_get(v___x_2100_, 0);
                v_nextMacroScope_2103_ = crate::leanh::lean_ctor_get(v___x_2100_, 1);
                v_ngen_2104_ = crate::leanh::lean_ctor_get(v___x_2100_, 2);
                v_auxDeclNGen_2105_ = crate::leanh::lean_ctor_get(v___x_2100_, 3);
                v_cache_2106_ = crate::leanh::lean_ctor_get(v___x_2100_, 5);
                v_messages_2107_ = crate::leanh::lean_ctor_get(v___x_2100_, 6);
                v_infoState_2108_ = crate::leanh::lean_ctor_get(v___x_2100_, 7);
                v_snapshotTasks_2109_ = crate::leanh::lean_ctor_get(v___x_2100_, 8);
                v_isSharedCheck_2128_ = (!crate::leanh::lean_is_exclusive(v___x_2100_)) as u8;
                if v_isSharedCheck_2128_ == 0 {
                    v___x_2111_ = v___x_2100_;
                    v_isShared_2112_ = v_isSharedCheck_2128_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_2109_);
                    crate::leanh::lean_inc(v_infoState_2108_);
                    crate::leanh::lean_inc(v_messages_2107_);
                    crate::leanh::lean_inc(v_cache_2106_);
                    crate::leanh::lean_inc(v_traceState_2101_);
                    crate::leanh::lean_inc(v_auxDeclNGen_2105_);
                    crate::leanh::lean_inc(v_ngen_2104_);
                    crate::leanh::lean_inc(v_nextMacroScope_2103_);
                    crate::leanh::lean_inc(v_env_2102_);
                    crate::leanh::lean_dec(v___x_2100_);
                    v___x_2111_ = crate::leanh::lean_box(0);
                    v_isShared_2112_ = v_isSharedCheck_2128_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_tid_2113_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_2101_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_2126_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_2101_)) as u8;
                if v_isSharedCheck_2126_ == 0 {
                    v_unused_2127_ = crate::leanh::lean_ctor_get(v_traceState_2101_, 0);
                    crate::leanh::lean_dec(v_unused_2127_);
                    v___x_2115_ = v_traceState_2101_;
                    v_isShared_2116_ = v_isSharedCheck_2126_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_traceState_2101_);
                    v___x_2115_ = crate::leanh::lean_box(0);
                    v_isShared_2116_ = v_isSharedCheck_2126_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2117_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg___closed__1_once), _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg___closed__1);
                if v_isShared_2116_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2115_, 0, v___x_2117_);
                    v___x_2119_ = v___x_2115_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2125_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2125_, 0, v___x_2117_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_2125_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_2113_,
                    );
                    v___x_2119_ = v_reuseFailAlloc_2125_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2112_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2111_, 4, v___x_2119_);
                    v___x_2121_ = v___x_2111_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2124_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2124_, 0, v_env_2102_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2124_, 1, v_nextMacroScope_2103_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2124_, 2, v_ngen_2104_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2124_, 3, v_auxDeclNGen_2105_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2124_, 4, v___x_2119_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2124_, 5, v_cache_2106_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2124_, 6, v_messages_2107_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2124_, 7, v_infoState_2108_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2124_, 8, v_snapshotTasks_2109_);
                    v___x_2121_ = v_reuseFailAlloc_2124_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2122_ = lean_st_ref_set(v___y_2095_, v___x_2121_);
                v___x_2123_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2123_, 0, v_traces_2099_);
                return v___x_2123_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg___boxed(
    mut v___y_2129_: *mut crate::leanh::LeanObject,
    mut v___y_2130_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2131_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg(v___y_2129_);
    crate::leanh::lean_dec(v___y_2129_);
    return v_res_2131_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4(
    mut v___y_2132_: *mut crate::leanh::LeanObject,
    mut v___y_2133_: *mut crate::leanh::LeanObject,
    mut v___y_2134_: *mut crate::leanh::LeanObject,
    mut v___y_2135_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2137_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg(v___y_2135_);
    return v___x_2137_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___boxed(
    mut v___y_2138_: *mut crate::leanh::LeanObject,
    mut v___y_2139_: *mut crate::leanh::LeanObject,
    mut v___y_2140_: *mut crate::leanh::LeanObject,
    mut v___y_2141_: *mut crate::leanh::LeanObject,
    mut v___y_2142_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2143_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4(v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_);
    crate::leanh::lean_dec(v___y_2141_);
    crate::leanh::lean_dec_ref(v___y_2140_);
    crate::leanh::lean_dec(v___y_2139_);
    crate::leanh::lean_dec_ref(v___y_2138_);
    return v_res_2143_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__5(
    mut v_opts_2144_: *mut crate::leanh::LeanObject,
    mut v_opt_2145_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_2146_ = crate::leanh::lean_ctor_get(v_opt_2145_, 0);
    v_defValue_2147_ = crate::leanh::lean_ctor_get(v_opt_2145_, 1);
    v_map_2148_ = crate::leanh::lean_ctor_get(v_opts_2144_, 0);
    v___x_2149_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2148_,
            v_name_2146_,
        );
    if crate::leanh::lean_obj_tag(v___x_2149_) == 0 {
        let mut v___x_2150_: u8 = 0;
        v___x_2150_ = (crate::leanh::lean_unbox(v_defValue_2147_) as u8);
        return v___x_2150_;
    } else {
        let mut v_val_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2151_ = crate::leanh::lean_ctor_get(v___x_2149_, 0);
        crate::leanh::lean_inc(v_val_2151_);
        crate::leanh::lean_dec_ref_known(v___x_2149_, 1);
        if crate::leanh::lean_obj_tag(v_val_2151_) == 1 {
            let mut v_v_2152_: u8 = 0;
            v_v_2152_ = crate::leanh::lean_ctor_get_uint8(v_val_2151_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_2151_, 0);
            return v_v_2152_;
        } else {
            let mut v___x_2153_: u8 = 0;
            crate::leanh::lean_dec(v_val_2151_);
            v___x_2153_ = (crate::leanh::lean_unbox(v_defValue_2147_) as u8);
            return v___x_2153_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__5___boxed(
    mut v_opts_2154_: *mut crate::leanh::LeanObject,
    mut v_opt_2155_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2156_: u8 = 0;
    let mut v_r_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2156_ =
        l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__5(v_opts_2154_, v_opt_2155_);
    crate::leanh::lean_dec_ref(v_opt_2155_);
    crate::leanh::lean_dec_ref(v_opts_2154_);
    v_r_2157_ = crate::leanh::lean_box((v_res_2156_) as usize);
    return v_r_2157_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_reduceSparseCasesOn_spec__1_spec__2(
    mut v_a_2158_: *mut crate::leanh::LeanObject,
    mut v_as_2159_: *mut crate::leanh::LeanObject,
    mut v_i_2160_: usize,
    mut v_stop_2161_: usize,
) -> u8 {
    let mut v___x_2162_: u8 = 0;
    let mut v___x_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: u8 = 0;
    let mut v___x_2165_: usize = 0;
    let mut v___x_2166_: usize = 0;
    let mut v___x_2168_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2162_ = lean_usize_dec_eq(v_i_2160_, v_stop_2161_);
                if v___x_2162_ == 0 {
                    v___x_2163_ = lean_array_uget_borrowed(v_as_2159_, v_i_2160_);
                    v___x_2164_ = lean_name_eq(v_a_2158_, v___x_2163_);
                    if v___x_2164_ == 0 {
                        v___x_2165_ = 1usize;
                        v___x_2166_ = lean_usize_add(v_i_2160_, v___x_2165_);
                        v_i_2160_ = v___x_2166_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2164_;
                    }
                } else {
                    v___x_2168_ = 0;
                    return v___x_2168_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_reduceSparseCasesOn_spec__1_spec__2___boxed(
    mut v_a_2169_: *mut crate::leanh::LeanObject,
    mut v_as_2170_: *mut crate::leanh::LeanObject,
    mut v_i_2171_: *mut crate::leanh::LeanObject,
    mut v_stop_2172_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2173_: usize = 0;
    let mut v_stop_boxed_2174_: usize = 0;
    let mut v_res_2175_: u8 = 0;
    let mut v_r_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2173_ = crate::leanh::lean_unbox_usize(v_i_2171_);
    crate::leanh::lean_dec(v_i_2171_);
    v_stop_boxed_2174_ = crate::leanh::lean_unbox_usize(v_stop_2172_);
    crate::leanh::lean_dec(v_stop_2172_);
    v_res_2175_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_reduceSparseCasesOn_spec__1_spec__2(v_a_2169_, v_as_2170_, v_i_boxed_2173_, v_stop_boxed_2174_);
    crate::leanh::lean_dec_ref(v_as_2170_);
    crate::leanh::lean_dec(v_a_2169_);
    v_r_2176_ = crate::leanh::lean_box((v_res_2175_) as usize);
    return v_r_2176_;
}
pub unsafe fn l_Array_contains___at___00Lean_Meta_reduceSparseCasesOn_spec__1(
    mut v_as_2177_: *mut crate::leanh::LeanObject,
    mut v_a_2178_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: u8 = 0;
    v___x_2179_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2180_ = lean_array_get_size(v_as_2177_);
    v___x_2181_ = lean_nat_dec_lt(v___x_2179_, v___x_2180_);
    if v___x_2181_ == 0 {
        return v___x_2181_;
    } else {
        if v___x_2181_ == 0 {
            return v___x_2181_;
        } else {
            let mut v___x_2182_: usize = 0;
            let mut v___x_2183_: usize = 0;
            let mut v___x_2184_: u8 = 0;
            v___x_2182_ = 0usize;
            v___x_2183_ = lean_usize_of_nat(v___x_2180_);
            v___x_2184_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_reduceSparseCasesOn_spec__1_spec__2(v_a_2178_, v_as_2177_, v___x_2182_, v___x_2183_);
            return v___x_2184_;
        }
    }
}
pub unsafe fn l_Array_contains___at___00Lean_Meta_reduceSparseCasesOn_spec__1___boxed(
    mut v_as_2185_: *mut crate::leanh::LeanObject,
    mut v_a_2186_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2187_: u8 = 0;
    let mut v_r_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2187_ =
        l_Array_contains___at___00Lean_Meta_reduceSparseCasesOn_spec__1(v_as_2185_, v_a_2186_);
    crate::leanh::lean_dec(v_a_2186_);
    crate::leanh::lean_dec_ref(v_as_2185_);
    v_r_2188_ = crate::leanh::lean_box((v_res_2187_) as usize);
    return v_r_2188_;
}
pub unsafe fn _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2189_ = l_instMonadEIO(crate::leanh::lean_box(0));
    return v___x_2189_;
}
pub unsafe fn l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0(
    mut v_msg_2194_: *mut crate::leanh::LeanObject,
    mut v___y_2195_: *mut crate::leanh::LeanObject,
    mut v___y_2196_: *mut crate::leanh::LeanObject,
    mut v___y_2197_: *mut crate::leanh::LeanObject,
    mut v___y_2198_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2205_: u8 = 0;
    let mut v_toFunctor_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2212_: u8 = 0;
    let mut v___f_2213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2229_: u8 = 0;
    let mut v_toFunctor_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2236_: u8 = 0;
    let mut v___f_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10977__overap_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2255_: u8 = 0;
    let mut v_unused_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2257_: u8 = 0;
    let mut v_unused_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2261_: u8 = 0;
    let mut v_unused_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2263_: u8 = 0;
    let mut v_unused_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2200_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__0_once), _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__0);
                v___x_2201_ = l_StateRefT_x27_instMonad___redArg(v___x_2200_);
                v_toApplicative_2202_ = crate::leanh::lean_ctor_get(v___x_2201_, 0);
                v_isSharedCheck_2263_ = (!crate::leanh::lean_is_exclusive(v___x_2201_)) as u8;
                if v_isSharedCheck_2263_ == 0 {
                    v_unused_2264_ = crate::leanh::lean_ctor_get(v___x_2201_, 1);
                    crate::leanh::lean_dec(v_unused_2264_);
                    v___x_2204_ = v___x_2201_;
                    v_isShared_2205_ = v_isSharedCheck_2263_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_2202_);
                    crate::leanh::lean_dec(v___x_2201_);
                    v___x_2204_ = crate::leanh::lean_box(0);
                    v_isShared_2205_ = v_isSharedCheck_2263_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_2206_ = crate::leanh::lean_ctor_get(v_toApplicative_2202_, 0);
                v_toSeq_2207_ = crate::leanh::lean_ctor_get(v_toApplicative_2202_, 2);
                v_toSeqLeft_2208_ = crate::leanh::lean_ctor_get(v_toApplicative_2202_, 3);
                v_toSeqRight_2209_ = crate::leanh::lean_ctor_get(v_toApplicative_2202_, 4);
                v_isSharedCheck_2261_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_2202_)) as u8;
                if v_isSharedCheck_2261_ == 0 {
                    v_unused_2262_ = crate::leanh::lean_ctor_get(v_toApplicative_2202_, 1);
                    crate::leanh::lean_dec(v_unused_2262_);
                    v___x_2211_ = v_toApplicative_2202_;
                    v_isShared_2212_ = v_isSharedCheck_2261_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_2209_);
                    crate::leanh::lean_inc(v_toSeqLeft_2208_);
                    crate::leanh::lean_inc(v_toSeq_2207_);
                    crate::leanh::lean_inc(v_toFunctor_2206_);
                    crate::leanh::lean_dec(v_toApplicative_2202_);
                    v___x_2211_ = crate::leanh::lean_box(0);
                    v_isShared_2212_ = v_isSharedCheck_2261_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_2213_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__1;
                v___f_2214_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__2;
                crate::leanh::lean_inc_ref(v_toFunctor_2206_);
                v___f_2215_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2215_, 0, v_toFunctor_2206_);
                v___f_2216_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2216_, 0, v_toFunctor_2206_);
                v___x_2217_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2217_, 0, v___f_2215_);
                crate::leanh::lean_ctor_set(v___x_2217_, 1, v___f_2216_);
                v___f_2218_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2218_, 0, v_toSeqRight_2209_);
                v___f_2219_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2219_, 0, v_toSeqLeft_2208_);
                v___f_2220_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2220_, 0, v_toSeq_2207_);
                if v_isShared_2212_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2211_, 4, v___f_2218_);
                    crate::leanh::lean_ctor_set(v___x_2211_, 3, v___f_2219_);
                    crate::leanh::lean_ctor_set(v___x_2211_, 2, v___f_2220_);
                    crate::leanh::lean_ctor_set(v___x_2211_, 1, v___f_2213_);
                    crate::leanh::lean_ctor_set(v___x_2211_, 0, v___x_2217_);
                    v___x_2222_ = v___x_2211_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2260_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2260_, 0, v___x_2217_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2260_, 1, v___f_2213_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2260_, 2, v___f_2220_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2260_, 3, v___f_2219_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2260_, 4, v___f_2218_);
                    v___x_2222_ = v_reuseFailAlloc_2260_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2205_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2204_, 1, v___f_2214_);
                    crate::leanh::lean_ctor_set(v___x_2204_, 0, v___x_2222_);
                    v___x_2224_ = v___x_2204_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2259_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2259_, 0, v___x_2222_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2259_, 1, v___f_2214_);
                    v___x_2224_ = v_reuseFailAlloc_2259_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2225_ = l_StateRefT_x27_instMonad___redArg(v___x_2224_);
                v_toApplicative_2226_ = crate::leanh::lean_ctor_get(v___x_2225_, 0);
                v_isSharedCheck_2257_ = (!crate::leanh::lean_is_exclusive(v___x_2225_)) as u8;
                if v_isSharedCheck_2257_ == 0 {
                    v_unused_2258_ = crate::leanh::lean_ctor_get(v___x_2225_, 1);
                    crate::leanh::lean_dec(v_unused_2258_);
                    v___x_2228_ = v___x_2225_;
                    v_isShared_2229_ = v_isSharedCheck_2257_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_2226_);
                    crate::leanh::lean_dec(v___x_2225_);
                    v___x_2228_ = crate::leanh::lean_box(0);
                    v_isShared_2229_ = v_isSharedCheck_2257_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_2230_ = crate::leanh::lean_ctor_get(v_toApplicative_2226_, 0);
                v_toSeq_2231_ = crate::leanh::lean_ctor_get(v_toApplicative_2226_, 2);
                v_toSeqLeft_2232_ = crate::leanh::lean_ctor_get(v_toApplicative_2226_, 3);
                v_toSeqRight_2233_ = crate::leanh::lean_ctor_get(v_toApplicative_2226_, 4);
                v_isSharedCheck_2255_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_2226_)) as u8;
                if v_isSharedCheck_2255_ == 0 {
                    v_unused_2256_ = crate::leanh::lean_ctor_get(v_toApplicative_2226_, 1);
                    crate::leanh::lean_dec(v_unused_2256_);
                    v___x_2235_ = v_toApplicative_2226_;
                    v_isShared_2236_ = v_isSharedCheck_2255_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_2233_);
                    crate::leanh::lean_inc(v_toSeqLeft_2232_);
                    crate::leanh::lean_inc(v_toSeq_2231_);
                    crate::leanh::lean_inc(v_toFunctor_2230_);
                    crate::leanh::lean_dec(v_toApplicative_2226_);
                    v___x_2235_ = crate::leanh::lean_box(0);
                    v_isShared_2236_ = v_isSharedCheck_2255_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_2237_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__3;
                v___f_2238_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__4;
                crate::leanh::lean_inc_ref(v_toFunctor_2230_);
                v___f_2239_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2239_, 0, v_toFunctor_2230_);
                v___f_2240_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2240_, 0, v_toFunctor_2230_);
                v___x_2241_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2241_, 0, v___f_2239_);
                crate::leanh::lean_ctor_set(v___x_2241_, 1, v___f_2240_);
                v___f_2242_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2242_, 0, v_toSeqRight_2233_);
                v___f_2243_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2243_, 0, v_toSeqLeft_2232_);
                v___f_2244_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2244_, 0, v_toSeq_2231_);
                if v_isShared_2236_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2235_, 4, v___f_2242_);
                    crate::leanh::lean_ctor_set(v___x_2235_, 3, v___f_2243_);
                    crate::leanh::lean_ctor_set(v___x_2235_, 2, v___f_2244_);
                    crate::leanh::lean_ctor_set(v___x_2235_, 1, v___f_2237_);
                    crate::leanh::lean_ctor_set(v___x_2235_, 0, v___x_2241_);
                    v___x_2246_ = v___x_2235_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2254_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2254_, 0, v___x_2241_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2254_, 1, v___f_2237_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2254_, 2, v___f_2244_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2254_, 3, v___f_2243_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2254_, 4, v___f_2242_);
                    v___x_2246_ = v_reuseFailAlloc_2254_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2229_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2228_, 1, v___f_2238_);
                    crate::leanh::lean_ctor_set(v___x_2228_, 0, v___x_2246_);
                    v___x_2248_ = v___x_2228_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2253_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2253_, 0, v___x_2246_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2253_, 1, v___f_2238_);
                    v___x_2248_ = v_reuseFailAlloc_2253_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2249_ = crate::leanh::lean_box(0);
                v___x_2250_ = l_instInhabitedOfMonad___redArg(v___x_2248_, v___x_2249_);
                v___x_10977__overap_2251_ = lean_panic_fn_borrowed(v___x_2250_, v_msg_2194_);
                crate::leanh::lean_dec(v___x_2250_);
                crate::leanh::lean_inc(v___y_2198_);
                crate::leanh::lean_inc_ref(v___y_2197_);
                crate::leanh::lean_inc(v___y_2196_);
                crate::leanh::lean_inc_ref(v___y_2195_);
                v___x_2252_ = crate::leanh::lean_apply_5(
                    v___x_10977__overap_2251_,
                    v___y_2195_,
                    v___y_2196_,
                    v___y_2197_,
                    v___y_2198_,
                    crate::leanh::lean_box(0),
                );
                return v___x_2252_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___boxed(
    mut v_msg_2265_: *mut crate::leanh::LeanObject,
    mut v___y_2266_: *mut crate::leanh::LeanObject,
    mut v___y_2267_: *mut crate::leanh::LeanObject,
    mut v___y_2268_: *mut crate::leanh::LeanObject,
    mut v___y_2269_: *mut crate::leanh::LeanObject,
    mut v___y_2270_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2271_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0(v_msg_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_);
    crate::leanh::lean_dec(v___y_2269_);
    crate::leanh::lean_dec_ref(v___y_2268_);
    crate::leanh::lean_dec(v___y_2267_);
    crate::leanh::lean_dec_ref(v___y_2266_);
    return v_res_2271_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3_spec__5(
    mut v_msgData_2272_: *mut crate::leanh::LeanObject,
    mut v___y_2273_: *mut crate::leanh::LeanObject,
    mut v___y_2274_: *mut crate::leanh::LeanObject,
    mut v___y_2275_: *mut crate::leanh::LeanObject,
    mut v___y_2276_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2278_ = lean_st_ref_get(v___y_2276_);
    v_env_2279_ = crate::leanh::lean_ctor_get(v___x_2278_, 0);
    crate::leanh::lean_inc_ref(v_env_2279_);
    crate::leanh::lean_dec(v___x_2278_);
    v___x_2280_ = lean_st_ref_get(v___y_2274_);
    v_mctx_2281_ = crate::leanh::lean_ctor_get(v___x_2280_, 0);
    crate::leanh::lean_inc_ref(v_mctx_2281_);
    crate::leanh::lean_dec(v___x_2280_);
    v_lctx_2282_ = crate::leanh::lean_ctor_get(v___y_2273_, 2);
    v_options_2283_ = crate::leanh::lean_ctor_get(v___y_2275_, 2);
    crate::leanh::lean_inc_ref(v_options_2283_);
    crate::leanh::lean_inc_ref(v_lctx_2282_);
    v___x_2284_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2284_, 0, v_env_2279_);
    crate::leanh::lean_ctor_set(v___x_2284_, 1, v_mctx_2281_);
    crate::leanh::lean_ctor_set(v___x_2284_, 2, v_lctx_2282_);
    crate::leanh::lean_ctor_set(v___x_2284_, 3, v_options_2283_);
    v___x_2285_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2285_, 0, v___x_2284_);
    crate::leanh::lean_ctor_set(v___x_2285_, 1, v_msgData_2272_);
    v___x_2286_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2286_, 0, v___x_2285_);
    return v___x_2286_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3_spec__5___boxed(
    mut v_msgData_2287_: *mut crate::leanh::LeanObject,
    mut v___y_2288_: *mut crate::leanh::LeanObject,
    mut v___y_2289_: *mut crate::leanh::LeanObject,
    mut v___y_2290_: *mut crate::leanh::LeanObject,
    mut v___y_2291_: *mut crate::leanh::LeanObject,
    mut v___y_2292_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2293_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3_spec__5(v_msgData_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_);
    crate::leanh::lean_dec(v___y_2291_);
    crate::leanh::lean_dec_ref(v___y_2290_);
    crate::leanh::lean_dec(v___y_2289_);
    crate::leanh::lean_dec_ref(v___y_2288_);
    return v_res_2293_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(
    mut v_msg_2294_: *mut crate::leanh::LeanObject,
    mut v___y_2295_: *mut crate::leanh::LeanObject,
    mut v___y_2296_: *mut crate::leanh::LeanObject,
    mut v___y_2297_: *mut crate::leanh::LeanObject,
    mut v___y_2298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2305_: u8 = 0;
    let mut v___x_2306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2310_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2300_ = crate::leanh::lean_ctor_get(v___y_2297_, 5);
                v___x_2301_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3_spec__5(v_msg_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_);
                v_a_2302_ = crate::leanh::lean_ctor_get(v___x_2301_, 0);
                v_isSharedCheck_2310_ = (!crate::leanh::lean_is_exclusive(v___x_2301_)) as u8;
                if v_isSharedCheck_2310_ == 0 {
                    v___x_2304_ = v___x_2301_;
                    v_isShared_2305_ = v_isSharedCheck_2310_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_2302_);
                    crate::leanh::lean_dec(v___x_2301_);
                    v___x_2304_ = crate::leanh::lean_box(0);
                    v_isShared_2305_ = v_isSharedCheck_2310_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_2300_);
                v___x_2306_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2306_, 0, v_ref_2300_);
                crate::leanh::lean_ctor_set(v___x_2306_, 1, v_a_2302_);
                if v_isShared_2305_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2304_, 1);
                    crate::leanh::lean_ctor_set(v___x_2304_, 0, v___x_2306_);
                    v___x_2308_ = v___x_2304_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2309_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2309_, 0, v___x_2306_);
                    v___x_2308_ = v_reuseFailAlloc_2309_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2308_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg___boxed(
    mut v_msg_2311_: *mut crate::leanh::LeanObject,
    mut v___y_2312_: *mut crate::leanh::LeanObject,
    mut v___y_2313_: *mut crate::leanh::LeanObject,
    mut v___y_2314_: *mut crate::leanh::LeanObject,
    mut v___y_2315_: *mut crate::leanh::LeanObject,
    mut v___y_2316_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2317_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(
        v_msg_2311_,
        v___y_2312_,
        v___y_2313_,
        v___y_2314_,
        v___y_2315_,
    );
    crate::leanh::lean_dec(v___y_2315_);
    crate::leanh::lean_dec_ref(v___y_2314_);
    crate::leanh::lean_dec(v___y_2313_);
    crate::leanh::lean_dec_ref(v___y_2312_);
    return v_res_2317_;
}
pub unsafe fn _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2319_ =
        l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__0;
    v___x_2320_ = l_Lean_stringToMessageData(v___x_2319_);
    return v___x_2320_;
}
pub unsafe fn _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2322_ =
        l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__2;
    v___x_2323_ = l_Lean_stringToMessageData(v___x_2322_);
    return v___x_2323_;
}
pub unsafe fn _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2327_ =
        l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__6;
    v___x_2328_ = crate::leanh::lean_unsigned_to_nat(11);
    v___x_2329_ = crate::leanh::lean_unsigned_to_nat(122);
    v___x_2330_ =
        l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__5;
    v___x_2331_ =
        l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__4;
    v___x_2332_ = l_mkPanicMessageWithDecl(
        v___x_2331_,
        v___x_2330_,
        v___x_2329_,
        v___x_2328_,
        v___x_2327_,
    );
    return v___x_2332_;
}
pub unsafe fn l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0(
    mut v_constName_2333_: *mut crate::leanh::LeanObject,
    mut v___y_2334_: *mut crate::leanh::LeanObject,
    mut v___y_2335_: *mut crate::leanh::LeanObject,
    mut v___y_2336_: *mut crate::leanh::LeanObject,
    mut v___y_2337_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: u8 = 0;
    let mut v___x_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2349_: u8 = 0;
    let mut v___x_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_2352_: u8 = 0;
    let mut v___x_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2357_: u8 = 0;
    let mut v___x_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2361_: u8 = 0;
    let mut v___x_2362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2367_: u8 = 0;
    let mut v_val_2368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2372_: u8 = 0;
    let mut v_a_2373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2376_: u8 = 0;
    let mut v___x_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2380_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2347_ = lean_st_ref_get(v___y_2337_);
                v_env_2348_ = crate::leanh::lean_ctor_get(v___x_2347_, 0);
                crate::leanh::lean_inc_ref(v_env_2348_);
                crate::leanh::lean_dec(v___x_2347_);
                v___x_2349_ = 0;
                crate::leanh::lean_inc(v_constName_2333_);
                v___x_2350_ =
                    l_Lean_Environment_findAsync_x3f(v_env_2348_, v_constName_2333_, v___x_2349_);
                if crate::leanh::lean_obj_tag(v___x_2350_) == 1 {
                    v_val_2351_ = crate::leanh::lean_ctor_get(v___x_2350_, 0);
                    crate::leanh::lean_inc(v_val_2351_);
                    crate::leanh::lean_dec_ref_known(v___x_2350_, 1);
                    v_kind_2352_ = crate::leanh::lean_ctor_get_uint8(
                        v_val_2351_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    );
                    if v_kind_2352_ == 6 {
                        v___x_2353_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_2351_);
                        if crate::leanh::lean_obj_tag(v___x_2353_) == 6 {
                            crate::leanh::lean_dec(v_constName_2333_);
                            v_val_2354_ = crate::leanh::lean_ctor_get(v___x_2353_, 0);
                            v_isSharedCheck_2361_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2353_)) as u8;
                            if v_isSharedCheck_2361_ == 0 {
                                v___x_2356_ = v___x_2353_;
                                v_isShared_2357_ = v_isSharedCheck_2361_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_val_2354_);
                                crate::leanh::lean_dec(v___x_2353_);
                                v___x_2356_ = crate::leanh::lean_box(0);
                                v_isShared_2357_ = v_isSharedCheck_2361_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_2353_);
                            v___x_2362_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__7), core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__7_once), _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__7);
                            v___x_2363_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0(v___x_2362_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_);
                            if crate::leanh::lean_obj_tag(v___x_2363_) == 0 {
                                v_a_2364_ = crate::leanh::lean_ctor_get(v___x_2363_, 0);
                                v_isSharedCheck_2372_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2363_)) as u8;
                                if v_isSharedCheck_2372_ == 0 {
                                    v___x_2366_ = v___x_2363_;
                                    v_isShared_2367_ = v_isSharedCheck_2372_;
                                    state = 4;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2364_);
                                    crate::leanh::lean_dec(v___x_2363_);
                                    v___x_2366_ = crate::leanh::lean_box(0);
                                    v_isShared_2367_ = v_isSharedCheck_2372_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_constName_2333_);
                                v_a_2373_ = crate::leanh::lean_ctor_get(v___x_2363_, 0);
                                v_isSharedCheck_2380_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2363_)) as u8;
                                if v_isSharedCheck_2380_ == 0 {
                                    v___x_2375_ = v___x_2363_;
                                    v_isShared_2376_ = v_isSharedCheck_2380_;
                                    state = 6;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2373_);
                                    crate::leanh::lean_dec(v___x_2363_);
                                    v___x_2375_ = crate::leanh::lean_box(0);
                                    v_isShared_2376_ = v_isSharedCheck_2380_;
                                    state = 6;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_2351_);
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2350_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2340_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__1_once), _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__1);
                v___x_2341_ = 0;
                v___x_2342_ = l_Lean_MessageData_ofConstName(v_constName_2333_, v___x_2341_);
                v___x_2343_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2343_, 0, v___x_2340_);
                crate::leanh::lean_ctor_set(v___x_2343_, 1, v___x_2342_);
                v___x_2344_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__3_once), _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__3);
                v___x_2345_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2345_, 0, v___x_2343_);
                crate::leanh::lean_ctor_set(v___x_2345_, 1, v___x_2344_);
                v___x_2346_ =
                    l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(
                        v___x_2345_,
                        v___y_2334_,
                        v___y_2335_,
                        v___y_2336_,
                        v___y_2337_,
                    );
                return v___x_2346_;
            }
            2 => {
                if v_isShared_2357_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2356_, 0);
                    v___x_2359_ = v___x_2356_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2360_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2360_, 0, v_val_2354_);
                    v___x_2359_ = v_reuseFailAlloc_2360_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2359_;
            }
            4 => {
                if crate::leanh::lean_obj_tag(v_a_2364_) == 0 {
                    crate::leanh::lean_del_object(v___x_2366_);
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_constName_2333_);
                    v_val_2368_ = crate::leanh::lean_ctor_get(v_a_2364_, 0);
                    crate::leanh::lean_inc(v_val_2368_);
                    crate::leanh::lean_dec_ref_known(v_a_2364_, 1);
                    if v_isShared_2367_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2366_, 0, v_val_2368_);
                        v___x_2370_ = v___x_2366_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2371_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2371_, 0, v_val_2368_);
                        v___x_2370_ = v_reuseFailAlloc_2371_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_2370_;
            }
            6 => {
                if v_isShared_2376_ == 0 {
                    v___x_2378_ = v___x_2375_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2379_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2379_, 0, v_a_2373_);
                    v___x_2378_ = v_reuseFailAlloc_2379_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2378_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___boxed(
    mut v_constName_2381_: *mut crate::leanh::LeanObject,
    mut v___y_2382_: *mut crate::leanh::LeanObject,
    mut v___y_2383_: *mut crate::leanh::LeanObject,
    mut v___y_2384_: *mut crate::leanh::LeanObject,
    mut v___y_2385_: *mut crate::leanh::LeanObject,
    mut v___y_2386_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2387_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0(
        v_constName_2381_,
        v___y_2382_,
        v___y_2383_,
        v___y_2384_,
        v___y_2385_,
    );
    crate::leanh::lean_dec(v___y_2385_);
    crate::leanh::lean_dec_ref(v___y_2384_);
    crate::leanh::lean_dec(v___y_2383_);
    crate::leanh::lean_dec_ref(v___y_2382_);
    return v_res_2387_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_reduceSparseCasesOn_spec__2(
    mut v_sz_2388_: usize,
    mut v_i_2389_: usize,
    mut v_bs_2390_: *mut crate::leanh::LeanObject,
    mut v___y_2391_: *mut crate::leanh::LeanObject,
    mut v___y_2392_: *mut crate::leanh::LeanObject,
    mut v___y_2393_: *mut crate::leanh::LeanObject,
    mut v___y_2394_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2396_: u8 = 0;
    let mut v___x_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cidx_2401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: usize = 0;
    let mut v___x_2405_: usize = 0;
    let mut v___x_2406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2411_: u8 = 0;
    let mut v___x_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2415_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2396_ = lean_usize_dec_lt(v_i_2389_, v_sz_2388_);
                if v___x_2396_ == 0 {
                    v___x_2397_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2397_, 0, v_bs_2390_);
                    return v___x_2397_;
                } else {
                    v_v_2398_ = lean_array_uget_borrowed(v_bs_2390_, v_i_2389_);
                    crate::leanh::lean_inc(v_v_2398_);
                    v___x_2399_ =
                        l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0(
                            v_v_2398_,
                            v___y_2391_,
                            v___y_2392_,
                            v___y_2393_,
                            v___y_2394_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_2399_) == 0 {
                        v_a_2400_ = crate::leanh::lean_ctor_get(v___x_2399_, 0);
                        crate::leanh::lean_inc(v_a_2400_);
                        crate::leanh::lean_dec_ref_known(v___x_2399_, 1);
                        v_cidx_2401_ = crate::leanh::lean_ctor_get(v_a_2400_, 2);
                        crate::leanh::lean_inc(v_cidx_2401_);
                        crate::leanh::lean_dec(v_a_2400_);
                        v___x_2402_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_2403_ = lean_array_uset(v_bs_2390_, v_i_2389_, v___x_2402_);
                        v___x_2404_ = 1usize;
                        v___x_2405_ = lean_usize_add(v_i_2389_, v___x_2404_);
                        v___x_2406_ = lean_array_uset(v_bs_x27_2403_, v_i_2389_, v_cidx_2401_);
                        v_i_2389_ = v___x_2405_;
                        v_bs_2390_ = v___x_2406_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_bs_2390_);
                        v_a_2408_ = crate::leanh::lean_ctor_get(v___x_2399_, 0);
                        v_isSharedCheck_2415_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2399_)) as u8;
                        if v_isSharedCheck_2415_ == 0 {
                            v___x_2410_ = v___x_2399_;
                            v_isShared_2411_ = v_isSharedCheck_2415_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2408_);
                            crate::leanh::lean_dec(v___x_2399_);
                            v___x_2410_ = crate::leanh::lean_box(0);
                            v_isShared_2411_ = v_isSharedCheck_2415_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_2411_ == 0 {
                    v___x_2413_ = v___x_2410_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2414_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2414_, 0, v_a_2408_);
                    v___x_2413_ = v_reuseFailAlloc_2414_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2413_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_reduceSparseCasesOn_spec__2___boxed(
    mut v_sz_2416_: *mut crate::leanh::LeanObject,
    mut v_i_2417_: *mut crate::leanh::LeanObject,
    mut v_bs_2418_: *mut crate::leanh::LeanObject,
    mut v___y_2419_: *mut crate::leanh::LeanObject,
    mut v___y_2420_: *mut crate::leanh::LeanObject,
    mut v___y_2421_: *mut crate::leanh::LeanObject,
    mut v___y_2422_: *mut crate::leanh::LeanObject,
    mut v___y_2423_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2424_: usize = 0;
    let mut v_i_boxed_2425_: usize = 0;
    let mut v_res_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2424_ = crate::leanh::lean_unbox_usize(v_sz_2416_);
    crate::leanh::lean_dec(v_sz_2416_);
    v_i_boxed_2425_ = crate::leanh::lean_unbox_usize(v_i_2417_);
    crate::leanh::lean_dec(v_i_2417_);
    v_res_2426_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_reduceSparseCasesOn_spec__2(v_sz_boxed_2424_, v_i_boxed_2425_, v_bs_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_);
    crate::leanh::lean_dec(v___y_2422_);
    crate::leanh::lean_dec_ref(v___y_2421_);
    crate::leanh::lean_dec(v___y_2420_);
    crate::leanh::lean_dec_ref(v___y_2419_);
    return v_res_2426_;
}
pub unsafe fn _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_2428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2427_ = crate::leanh::lean_box(0);
    v_dummy_2428_ = l_Lean_Expr_sort___override(v___x_2427_);
    return v_dummy_2428_;
}
pub unsafe fn _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2430_ =
        l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__1;
    v___x_2431_ = l_Lean_stringToMessageData(v___x_2430_);
    return v___x_2431_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0(
    mut v___x_2432_: *mut crate::leanh::LeanObject,
    mut v_x_2433_: *mut crate::leanh::LeanObject,
    mut v_majorPos_2434_: *mut crate::leanh::LeanObject,
    mut v_insterestingCtors_2435_: *mut crate::leanh::LeanObject,
    mut v_declName_2436_: *mut crate::leanh::LeanObject,
    mut v_snd_2437_: *mut crate::leanh::LeanObject,
    mut v_arity_2438_: *mut crate::leanh::LeanObject,
    mut v_mvarId_2439_: *mut crate::leanh::LeanObject,
    mut v___f_2440_: *mut crate::leanh::LeanObject,
    mut v_____r_2441_: *mut crate::leanh::LeanObject,
    mut v___y_2442_: *mut crate::leanh::LeanObject,
    mut v___y_2443_: *mut crate::leanh::LeanObject,
    mut v___y_2444_: *mut crate::leanh::LeanObject,
    mut v___y_2445_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_2451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cidx_2452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: u8 = 0;
    let mut v___x_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2457_: usize = 0;
    let mut v___x_2458_: usize = 0;
    let mut v___x_2459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_2465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2482_: u8 = 0;
    let mut v___x_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2488_: u8 = 0;
    let mut v_a_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2492_: u8 = 0;
    let mut v___x_2494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2496_: u8 = 0;
    let mut v_a_2497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2500_: u8 = 0;
    let mut v___x_2502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2504_: u8 = 0;
    let mut v_a_2505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2508_: u8 = 0;
    let mut v___x_2510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2512_: u8 = 0;
    let mut v_a_2513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2516_: u8 = 0;
    let mut v___x_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2520_: u8 = 0;
    let mut v___x_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2525_: u8 = 0;
    let mut v___x_2526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2532_: u8 = 0;
    let mut v_a_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2536_: u8 = 0;
    let mut v___x_2538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2540_: u8 = 0;
    let mut v___x_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2548_: u8 = 0;
    let mut v___x_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2552_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2447_ = lean_array_get_borrowed(v___x_2432_, v_x_2433_, v_majorPos_2434_);
                crate::leanh::lean_inc(v___x_2447_);
                v___x_2448_ = l_Lean_Meta_isConstructorApp_x27_x3f(
                    v___x_2447_,
                    v___y_2442_,
                    v___y_2443_,
                    v___y_2444_,
                    v___y_2445_,
                );
                if crate::leanh::lean_obj_tag(v___x_2448_) == 0 {
                    v_a_2449_ = crate::leanh::lean_ctor_get(v___x_2448_, 0);
                    crate::leanh::lean_inc(v_a_2449_);
                    crate::leanh::lean_dec_ref_known(v___x_2448_, 1);
                    if crate::leanh::lean_obj_tag(v_a_2449_) == 1 {
                        v_val_2450_ = crate::leanh::lean_ctor_get(v_a_2449_, 0);
                        crate::leanh::lean_inc(v_val_2450_);
                        crate::leanh::lean_dec_ref_known(v_a_2449_, 1);
                        v_toConstantVal_2451_ = crate::leanh::lean_ctor_get(v_val_2450_, 0);
                        crate::leanh::lean_inc_ref(v_toConstantVal_2451_);
                        v_cidx_2452_ = crate::leanh::lean_ctor_get(v_val_2450_, 2);
                        crate::leanh::lean_inc(v_cidx_2452_);
                        crate::leanh::lean_dec(v_val_2450_);
                        v_name_2453_ = crate::leanh::lean_ctor_get(v_toConstantVal_2451_, 0);
                        crate::leanh::lean_inc(v_name_2453_);
                        crate::leanh::lean_dec_ref(v_toConstantVal_2451_);
                        v___x_2454_ =
                            l_Array_contains___at___00Lean_Meta_reduceSparseCasesOn_spec__1(
                                v_insterestingCtors_2435_,
                                v_name_2453_,
                            );
                        crate::leanh::lean_dec(v_name_2453_);
                        if v___x_2454_ == 0 {
                            crate::leanh::lean_dec_ref(v___f_2440_);
                            v___x_2455_ = l_Lean_Meta_getSparseCasesOnEq(
                                v_declName_2436_,
                                v___y_2442_,
                                v___y_2443_,
                                v___y_2444_,
                                v___y_2445_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_2455_) == 0 {
                                v_a_2456_ = crate::leanh::lean_ctor_get(v___x_2455_, 0);
                                crate::leanh::lean_inc(v_a_2456_);
                                crate::leanh::lean_dec_ref_known(v___x_2455_, 1);
                                v_sz_2457_ = lean_array_size(v_insterestingCtors_2435_);
                                v___x_2458_ = 0usize;
                                v___x_2459_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_reduceSparseCasesOn_spec__2(v_sz_2457_, v___x_2458_, v_insterestingCtors_2435_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_);
                                if crate::leanh::lean_obj_tag(v___x_2459_) == 0 {
                                    v_a_2460_ = crate::leanh::lean_ctor_get(v___x_2459_, 0);
                                    crate::leanh::lean_inc(v_a_2460_);
                                    crate::leanh::lean_dec_ref_known(v___x_2459_, 1);
                                    v___x_2461_ = l_Lean_mkRawNatLit(v_cidx_2452_);
                                    v___x_2462_ = l_mkHasNotBitProof(
                                        v___x_2461_,
                                        v_a_2460_,
                                        v___y_2442_,
                                        v___y_2443_,
                                        v___y_2444_,
                                        v___y_2445_,
                                    );
                                    crate::leanh::lean_dec(v_a_2460_);
                                    if crate::leanh::lean_obj_tag(v___x_2462_) == 0 {
                                        v_a_2463_ = crate::leanh::lean_ctor_get(v___x_2462_, 0);
                                        crate::leanh::lean_inc(v_a_2463_);
                                        crate::leanh::lean_dec_ref_known(v___x_2462_, 1);
                                        v___x_2464_ = l_Lean_Expr_getAppFn(v_snd_2437_);
                                        v_nargs_2465_ = l_Lean_Expr_getAppNumArgs(v_snd_2437_);
                                        v___x_2466_ = l_Lean_Expr_constLevels_x21(v___x_2464_);
                                        crate::leanh::lean_dec_ref(v___x_2464_);
                                        v___x_2467_ = l_Lean_mkConst(v_a_2456_, v___x_2466_);
                                        v_dummy_2468_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0), core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0_once), _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0);
                                        crate::leanh::lean_inc(v_nargs_2465_);
                                        v___x_2469_ = lean_mk_array(v_nargs_2465_, v_dummy_2468_);
                                        v___x_2470_ = crate::leanh::lean_unsigned_to_nat(1);
                                        v___x_2471_ = lean_nat_sub(v_nargs_2465_, v___x_2470_);
                                        crate::leanh::lean_dec(v_nargs_2465_);
                                        v___x_2472_ =
                                            l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                                                v_snd_2437_,
                                                v___x_2469_,
                                                v___x_2471_,
                                            );
                                        v___x_2473_ = crate::leanh::lean_unsigned_to_nat(0);
                                        v___x_2474_ = l_Array_toSubarray___redArg(
                                            v___x_2472_,
                                            v___x_2473_,
                                            v_arity_2438_,
                                        );
                                        v___x_2475_ = l_Subarray_copy___redArg(v___x_2474_);
                                        v___x_2476_ = l_Lean_mkAppN(v___x_2467_, v___x_2475_);
                                        crate::leanh::lean_dec_ref(v___x_2475_);
                                        v___x_2477_ =
                                            l_Lean_Expr_app___override(v___x_2476_, v_a_2463_);
                                        v___x_2478_ = l___private_Lean_Meta_SplitSparseCasesOn_0__Lean_Meta_rewriteGoalUsingEq(v_mvarId_2439_, v___x_2477_, v___x_2454_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_);
                                        if crate::leanh::lean_obj_tag(v___x_2478_) == 0 {
                                            v_a_2479_ = crate::leanh::lean_ctor_get(v___x_2478_, 0);
                                            v_isSharedCheck_2488_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_2478_))
                                                    as u8;
                                            if v_isSharedCheck_2488_ == 0 {
                                                v___x_2481_ = v___x_2478_;
                                                v_isShared_2482_ = v_isSharedCheck_2488_;
                                                state = 1;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_2479_);
                                                crate::leanh::lean_dec(v___x_2478_);
                                                v___x_2481_ = crate::leanh::lean_box(0);
                                                v_isShared_2482_ = v_isSharedCheck_2488_;
                                                state = 1;
                                                continue;
                                            }
                                        } else {
                                            v_a_2489_ = crate::leanh::lean_ctor_get(v___x_2478_, 0);
                                            v_isSharedCheck_2496_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_2478_))
                                                    as u8;
                                            if v_isSharedCheck_2496_ == 0 {
                                                v___x_2491_ = v___x_2478_;
                                                v_isShared_2492_ = v_isSharedCheck_2496_;
                                                state = 3;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_2489_);
                                                crate::leanh::lean_dec(v___x_2478_);
                                                v___x_2491_ = crate::leanh::lean_box(0);
                                                v_isShared_2492_ = v_isSharedCheck_2496_;
                                                state = 3;
                                                continue;
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_a_2456_);
                                        crate::leanh::lean_dec(v_mvarId_2439_);
                                        crate::leanh::lean_dec(v_arity_2438_);
                                        crate::leanh::lean_dec_ref(v_snd_2437_);
                                        v_a_2497_ = crate::leanh::lean_ctor_get(v___x_2462_, 0);
                                        v_isSharedCheck_2504_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2462_)) as u8;
                                        if v_isSharedCheck_2504_ == 0 {
                                            v___x_2499_ = v___x_2462_;
                                            v_isShared_2500_ = v_isSharedCheck_2504_;
                                            state = 5;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_2497_);
                                            crate::leanh::lean_dec(v___x_2462_);
                                            v___x_2499_ = crate::leanh::lean_box(0);
                                            v_isShared_2500_ = v_isSharedCheck_2504_;
                                            state = 5;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_2456_);
                                    crate::leanh::lean_dec(v_cidx_2452_);
                                    crate::leanh::lean_dec(v_mvarId_2439_);
                                    crate::leanh::lean_dec(v_arity_2438_);
                                    crate::leanh::lean_dec_ref(v_snd_2437_);
                                    v_a_2505_ = crate::leanh::lean_ctor_get(v___x_2459_, 0);
                                    v_isSharedCheck_2512_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2459_)) as u8;
                                    if v_isSharedCheck_2512_ == 0 {
                                        v___x_2507_ = v___x_2459_;
                                        v_isShared_2508_ = v_isSharedCheck_2512_;
                                        state = 7;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_2505_);
                                        crate::leanh::lean_dec(v___x_2459_);
                                        v___x_2507_ = crate::leanh::lean_box(0);
                                        v_isShared_2508_ = v_isSharedCheck_2512_;
                                        state = 7;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_cidx_2452_);
                                crate::leanh::lean_dec(v_mvarId_2439_);
                                crate::leanh::lean_dec(v_arity_2438_);
                                crate::leanh::lean_dec_ref(v_snd_2437_);
                                crate::leanh::lean_dec_ref(v_insterestingCtors_2435_);
                                v_a_2513_ = crate::leanh::lean_ctor_get(v___x_2455_, 0);
                                v_isSharedCheck_2520_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2455_)) as u8;
                                if v_isSharedCheck_2520_ == 0 {
                                    v___x_2515_ = v___x_2455_;
                                    v_isShared_2516_ = v_isSharedCheck_2520_;
                                    state = 9;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2513_);
                                    crate::leanh::lean_dec(v___x_2455_);
                                    v___x_2515_ = crate::leanh::lean_box(0);
                                    v_isShared_2516_ = v_isSharedCheck_2520_;
                                    state = 9;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_cidx_2452_);
                            crate::leanh::lean_dec(v_arity_2438_);
                            crate::leanh::lean_dec_ref(v_snd_2437_);
                            crate::leanh::lean_dec(v_declName_2436_);
                            crate::leanh::lean_dec_ref(v_insterestingCtors_2435_);
                            v___x_2521_ = l_Lean_MVarId_modifyTargetEqLHS(
                                v_mvarId_2439_,
                                v___f_2440_,
                                v___y_2442_,
                                v___y_2443_,
                                v___y_2444_,
                                v___y_2445_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_2521_) == 0 {
                                v_a_2522_ = crate::leanh::lean_ctor_get(v___x_2521_, 0);
                                v_isSharedCheck_2532_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2521_)) as u8;
                                if v_isSharedCheck_2532_ == 0 {
                                    v___x_2524_ = v___x_2521_;
                                    v_isShared_2525_ = v_isSharedCheck_2532_;
                                    state = 11;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2522_);
                                    crate::leanh::lean_dec(v___x_2521_);
                                    v___x_2524_ = crate::leanh::lean_box(0);
                                    v_isShared_2525_ = v_isSharedCheck_2532_;
                                    state = 11;
                                    continue;
                                }
                            } else {
                                v_a_2533_ = crate::leanh::lean_ctor_get(v___x_2521_, 0);
                                v_isSharedCheck_2540_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2521_)) as u8;
                                if v_isSharedCheck_2540_ == 0 {
                                    v___x_2535_ = v___x_2521_;
                                    v_isShared_2536_ = v_isSharedCheck_2540_;
                                    state = 13;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2533_);
                                    crate::leanh::lean_dec(v___x_2521_);
                                    v___x_2535_ = crate::leanh::lean_box(0);
                                    v_isShared_2536_ = v_isSharedCheck_2540_;
                                    state = 13;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2449_);
                        crate::leanh::lean_dec_ref(v___f_2440_);
                        crate::leanh::lean_dec(v_mvarId_2439_);
                        crate::leanh::lean_dec(v_arity_2438_);
                        crate::leanh::lean_dec_ref(v_snd_2437_);
                        crate::leanh::lean_dec(v_declName_2436_);
                        crate::leanh::lean_dec_ref(v_insterestingCtors_2435_);
                        v___x_2541_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__2), core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__2_once), _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__2);
                        crate::leanh::lean_inc(v___x_2447_);
                        v___x_2542_ = l_Lean_indentExpr(v___x_2447_);
                        v___x_2543_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2543_, 0, v___x_2541_);
                        crate::leanh::lean_ctor_set(v___x_2543_, 1, v___x_2542_);
                        v___x_2544_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_2543_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_);
                        return v___x_2544_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___f_2440_);
                    crate::leanh::lean_dec(v_mvarId_2439_);
                    crate::leanh::lean_dec(v_arity_2438_);
                    crate::leanh::lean_dec_ref(v_snd_2437_);
                    crate::leanh::lean_dec(v_declName_2436_);
                    crate::leanh::lean_dec_ref(v_insterestingCtors_2435_);
                    v_a_2545_ = crate::leanh::lean_ctor_get(v___x_2448_, 0);
                    v_isSharedCheck_2552_ = (!crate::leanh::lean_is_exclusive(v___x_2448_)) as u8;
                    if v_isSharedCheck_2552_ == 0 {
                        v___x_2547_ = v___x_2448_;
                        v_isShared_2548_ = v_isSharedCheck_2552_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2545_);
                        crate::leanh::lean_dec(v___x_2448_);
                        v___x_2547_ = crate::leanh::lean_box(0);
                        v_isShared_2548_ = v_isSharedCheck_2552_;
                        state = 15;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2483_ = lean_mk_empty_array_with_capacity(v___x_2470_);
                v___x_2484_ = lean_array_push(v___x_2483_, v_a_2479_);
                if v_isShared_2482_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2481_, 0, v___x_2484_);
                    v___x_2486_ = v___x_2481_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2487_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2487_, 0, v___x_2484_);
                    v___x_2486_ = v_reuseFailAlloc_2487_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2486_;
            }
            3 => {
                if v_isShared_2492_ == 0 {
                    v___x_2494_ = v___x_2491_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2495_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2495_, 0, v_a_2489_);
                    v___x_2494_ = v_reuseFailAlloc_2495_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2494_;
            }
            5 => {
                if v_isShared_2500_ == 0 {
                    v___x_2502_ = v___x_2499_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2503_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2503_, 0, v_a_2497_);
                    v___x_2502_ = v_reuseFailAlloc_2503_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2502_;
            }
            7 => {
                if v_isShared_2508_ == 0 {
                    v___x_2510_ = v___x_2507_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2511_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2511_, 0, v_a_2505_);
                    v___x_2510_ = v_reuseFailAlloc_2511_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2510_;
            }
            9 => {
                if v_isShared_2516_ == 0 {
                    v___x_2518_ = v___x_2515_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2519_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2519_, 0, v_a_2513_);
                    v___x_2518_ = v_reuseFailAlloc_2519_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2518_;
            }
            11 => {
                v___x_2526_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2527_ = lean_mk_empty_array_with_capacity(v___x_2526_);
                v___x_2528_ = lean_array_push(v___x_2527_, v_a_2522_);
                if v_isShared_2525_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2524_, 0, v___x_2528_);
                    v___x_2530_ = v___x_2524_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2531_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2531_, 0, v___x_2528_);
                    v___x_2530_ = v_reuseFailAlloc_2531_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2530_;
            }
            13 => {
                if v_isShared_2536_ == 0 {
                    v___x_2538_ = v___x_2535_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2539_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2539_, 0, v_a_2533_);
                    v___x_2538_ = v_reuseFailAlloc_2539_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_2538_;
            }
            15 => {
                if v_isShared_2548_ == 0 {
                    v___x_2550_ = v___x_2547_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2551_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2551_, 0, v_a_2545_);
                    v___x_2550_ = v_reuseFailAlloc_2551_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_2550_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___boxed(
    mut v___x_2553_: *mut crate::leanh::LeanObject,
    mut v_x_2554_: *mut crate::leanh::LeanObject,
    mut v_majorPos_2555_: *mut crate::leanh::LeanObject,
    mut v_insterestingCtors_2556_: *mut crate::leanh::LeanObject,
    mut v_declName_2557_: *mut crate::leanh::LeanObject,
    mut v_snd_2558_: *mut crate::leanh::LeanObject,
    mut v_arity_2559_: *mut crate::leanh::LeanObject,
    mut v_mvarId_2560_: *mut crate::leanh::LeanObject,
    mut v___f_2561_: *mut crate::leanh::LeanObject,
    mut v_____r_2562_: *mut crate::leanh::LeanObject,
    mut v___y_2563_: *mut crate::leanh::LeanObject,
    mut v___y_2564_: *mut crate::leanh::LeanObject,
    mut v___y_2565_: *mut crate::leanh::LeanObject,
    mut v___y_2566_: *mut crate::leanh::LeanObject,
    mut v___y_2567_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2568_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0(
        v___x_2553_,
        v_x_2554_,
        v_majorPos_2555_,
        v_insterestingCtors_2556_,
        v_declName_2557_,
        v_snd_2558_,
        v_arity_2559_,
        v_mvarId_2560_,
        v___f_2561_,
        v_____r_2562_,
        v___y_2563_,
        v___y_2564_,
        v___y_2565_,
        v___y_2566_,
    );
    crate::leanh::lean_dec(v___y_2566_);
    crate::leanh::lean_dec_ref(v___y_2565_);
    crate::leanh::lean_dec(v___y_2564_);
    crate::leanh::lean_dec_ref(v___y_2563_);
    crate::leanh::lean_dec(v_majorPos_2555_);
    crate::leanh::lean_dec_ref(v_x_2554_);
    crate::leanh::lean_dec_ref(v___x_2553_);
    return v_res_2568_;
}
pub unsafe fn _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2570_ =
        l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__0;
    v___x_2571_ = l_Lean_stringToMessageData(v___x_2570_);
    return v___x_2571_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1(
    mut v___x_2572_: u8,
    mut v___f_2573_: *mut crate::leanh::LeanObject,
    mut v___y_2574_: *mut crate::leanh::LeanObject,
    mut v___y_2575_: *mut crate::leanh::LeanObject,
    mut v___y_2576_: *mut crate::leanh::LeanObject,
    mut v___y_2577_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2586_: u8 = 0;
    let mut v___x_2588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2590_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v___x_2572_ == 0 {
                    v___x_2579_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc(v___y_2577_);
                    crate::leanh::lean_inc_ref(v___y_2576_);
                    crate::leanh::lean_inc(v___y_2575_);
                    crate::leanh::lean_inc_ref(v___y_2574_);
                    v___x_2580_ = crate::leanh::lean_apply_6(
                        v___f_2573_,
                        v___x_2579_,
                        v___y_2574_,
                        v___y_2575_,
                        v___y_2576_,
                        v___y_2577_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_2580_;
                } else {
                    crate::leanh::lean_dec_ref(v___f_2573_);
                    v___x_2581_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1), core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1_once), _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1);
                    v___x_2582_ =
                        l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(
                            v___x_2581_,
                            v___y_2574_,
                            v___y_2575_,
                            v___y_2576_,
                            v___y_2577_,
                        );
                    v_a_2583_ = crate::leanh::lean_ctor_get(v___x_2582_, 0);
                    v_isSharedCheck_2590_ = (!crate::leanh::lean_is_exclusive(v___x_2582_)) as u8;
                    if v_isSharedCheck_2590_ == 0 {
                        v___x_2585_ = v___x_2582_;
                        v_isShared_2586_ = v_isSharedCheck_2590_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2583_);
                        crate::leanh::lean_dec(v___x_2582_);
                        v___x_2585_ = crate::leanh::lean_box(0);
                        v_isShared_2586_ = v_isSharedCheck_2590_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2586_ == 0 {
                    v___x_2588_ = v___x_2585_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2589_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2589_, 0, v_a_2583_);
                    v___x_2588_ = v_reuseFailAlloc_2589_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2588_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___boxed(
    mut v___x_2591_: *mut crate::leanh::LeanObject,
    mut v___f_2592_: *mut crate::leanh::LeanObject,
    mut v___y_2593_: *mut crate::leanh::LeanObject,
    mut v___y_2594_: *mut crate::leanh::LeanObject,
    mut v___y_2595_: *mut crate::leanh::LeanObject,
    mut v___y_2596_: *mut crate::leanh::LeanObject,
    mut v___y_2597_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_14794__boxed_2598_: u8 = 0;
    let mut v_res_2599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_14794__boxed_2598_ = (crate::leanh::lean_unbox(v___x_2591_) as u8);
    v_res_2599_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1(
        v___x_14794__boxed_2598_,
        v___f_2592_,
        v___y_2593_,
        v___y_2594_,
        v___y_2595_,
        v___y_2596_,
    );
    crate::leanh::lean_dec(v___y_2596_);
    crate::leanh::lean_dec_ref(v___y_2595_);
    crate::leanh::lean_dec(v___y_2594_);
    crate::leanh::lean_dec_ref(v___y_2593_);
    return v_res_2599_;
}
pub unsafe fn _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2601_ =
        l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___closed__0;
    v___x_2602_ = l_Lean_stringToMessageData(v___x_2601_);
    return v___x_2602_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2(
    mut v_x_2603_: *mut crate::leanh::LeanObject,
    mut v___y_2604_: *mut crate::leanh::LeanObject,
    mut v___y_2605_: *mut crate::leanh::LeanObject,
    mut v___y_2606_: *mut crate::leanh::LeanObject,
    mut v___y_2607_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2609_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___closed__1), core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___closed__1_once), _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___closed__1);
    v___x_2610_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2610_, 0, v___x_2609_);
    return v___x_2610_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___boxed(
    mut v_x_2611_: *mut crate::leanh::LeanObject,
    mut v___y_2612_: *mut crate::leanh::LeanObject,
    mut v___y_2613_: *mut crate::leanh::LeanObject,
    mut v___y_2614_: *mut crate::leanh::LeanObject,
    mut v___y_2615_: *mut crate::leanh::LeanObject,
    mut v___y_2616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2617_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2(
        v_x_2611_,
        v___y_2612_,
        v___y_2613_,
        v___y_2614_,
        v___y_2615_,
    );
    crate::leanh::lean_dec(v___y_2615_);
    crate::leanh::lean_dec_ref(v___y_2614_);
    crate::leanh::lean_dec(v___y_2613_);
    crate::leanh::lean_dec_ref(v___y_2612_);
    crate::leanh::lean_dec_ref(v_x_2611_);
    return v_res_2617_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10_spec__11(
    mut v_sz_2618_: usize,
    mut v_i_2619_: usize,
    mut v_bs_2620_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2621_: u8 = 0;
    let mut v_v_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_2623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2626_: usize = 0;
    let mut v___x_2627_: usize = 0;
    let mut v___x_2628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2621_ = lean_usize_dec_lt(v_i_2619_, v_sz_2618_);
                if v___x_2621_ == 0 {
                    return v_bs_2620_;
                } else {
                    v_v_2622_ = lean_array_uget_borrowed(v_bs_2620_, v_i_2619_);
                    v_msg_2623_ = crate::leanh::lean_ctor_get(v_v_2622_, 1);
                    crate::leanh::lean_inc_ref(v_msg_2623_);
                    v___x_2624_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_2625_ = lean_array_uset(v_bs_2620_, v_i_2619_, v___x_2624_);
                    v___x_2626_ = 1usize;
                    v___x_2627_ = lean_usize_add(v_i_2619_, v___x_2626_);
                    v___x_2628_ = lean_array_uset(v_bs_x27_2625_, v_i_2619_, v_msg_2623_);
                    v_i_2619_ = v___x_2627_;
                    v_bs_2620_ = v___x_2628_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10_spec__11___boxed(
    mut v_sz_2630_: *mut crate::leanh::LeanObject,
    mut v_i_2631_: *mut crate::leanh::LeanObject,
    mut v_bs_2632_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2633_: usize = 0;
    let mut v_i_boxed_2634_: usize = 0;
    let mut v_res_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2633_ = crate::leanh::lean_unbox_usize(v_sz_2630_);
    crate::leanh::lean_dec(v_sz_2630_);
    v_i_boxed_2634_ = crate::leanh::lean_unbox_usize(v_i_2631_);
    crate::leanh::lean_dec(v_i_2631_);
    v_res_2635_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10_spec__11(v_sz_boxed_2633_, v_i_boxed_2634_, v_bs_2632_);
    return v_res_2635_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10(
    mut v_oldTraces_2636_: *mut crate::leanh::LeanObject,
    mut v_data_2637_: *mut crate::leanh::LeanObject,
    mut v_ref_2638_: *mut crate::leanh::LeanObject,
    mut v_msg_2639_: *mut crate::leanh::LeanObject,
    mut v___y_2640_: *mut crate::leanh::LeanObject,
    mut v___y_2641_: *mut crate::leanh::LeanObject,
    mut v___y_2642_: *mut crate::leanh::LeanObject,
    mut v___y_2643_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_2653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_2654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2657_: u8 = 0;
    let mut v_cancelTk_x3f_2658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2659_: u8 = 0;
    let mut v_inheritedTraceOptions_2660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traces_2663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2667_: usize = 0;
    let mut v___x_2668_: usize = 0;
    let mut v___x_2669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2675_: u8 = 0;
    let mut v___x_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2688_: u8 = 0;
    let mut v_tid_2689_: u64 = 0;
    let mut v___x_2691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2692_: u8 = 0;
    let mut v___x_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2706_: u8 = 0;
    let mut v_unused_2707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2708_: u8 = 0;
    let mut v_isSharedCheck_2709_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_2645_ = crate::leanh::lean_ctor_get(v___y_2642_, 0);
                v_fileMap_2646_ = crate::leanh::lean_ctor_get(v___y_2642_, 1);
                v_options_2647_ = crate::leanh::lean_ctor_get(v___y_2642_, 2);
                v_currRecDepth_2648_ = crate::leanh::lean_ctor_get(v___y_2642_, 3);
                v_maxRecDepth_2649_ = crate::leanh::lean_ctor_get(v___y_2642_, 4);
                v_ref_2650_ = crate::leanh::lean_ctor_get(v___y_2642_, 5);
                v_currNamespace_2651_ = crate::leanh::lean_ctor_get(v___y_2642_, 6);
                v_openDecls_2652_ = crate::leanh::lean_ctor_get(v___y_2642_, 7);
                v_initHeartbeats_2653_ = crate::leanh::lean_ctor_get(v___y_2642_, 8);
                v_maxHeartbeats_2654_ = crate::leanh::lean_ctor_get(v___y_2642_, 9);
                v_quotContext_2655_ = crate::leanh::lean_ctor_get(v___y_2642_, 10);
                v_currMacroScope_2656_ = crate::leanh::lean_ctor_get(v___y_2642_, 11);
                v_diag_2657_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_2642_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_2658_ = crate::leanh::lean_ctor_get(v___y_2642_, 12);
                v_suppressElabErrors_2659_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_2642_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_2660_ = crate::leanh::lean_ctor_get(v___y_2642_, 13);
                v___x_2661_ = lean_st_ref_get(v___y_2643_);
                v_traceState_2662_ = crate::leanh::lean_ctor_get(v___x_2661_, 4);
                crate::leanh::lean_inc_ref(v_traceState_2662_);
                crate::leanh::lean_dec(v___x_2661_);
                v_traces_2663_ = crate::leanh::lean_ctor_get(v_traceState_2662_, 0);
                crate::leanh::lean_inc_ref(v_traces_2663_);
                crate::leanh::lean_dec_ref(v_traceState_2662_);
                v_ref_2664_ = l_Lean_replaceRef(v_ref_2638_, v_ref_2650_);
                crate::leanh::lean_inc_ref(v_inheritedTraceOptions_2660_);
                crate::leanh::lean_inc(v_cancelTk_x3f_2658_);
                crate::leanh::lean_inc(v_currMacroScope_2656_);
                crate::leanh::lean_inc(v_quotContext_2655_);
                crate::leanh::lean_inc(v_maxHeartbeats_2654_);
                crate::leanh::lean_inc(v_initHeartbeats_2653_);
                crate::leanh::lean_inc(v_openDecls_2652_);
                crate::leanh::lean_inc(v_currNamespace_2651_);
                crate::leanh::lean_inc(v_maxRecDepth_2649_);
                crate::leanh::lean_inc(v_currRecDepth_2648_);
                crate::leanh::lean_inc_ref(v_options_2647_);
                crate::leanh::lean_inc_ref(v_fileMap_2646_);
                crate::leanh::lean_inc_ref(v_fileName_2645_);
                v___x_2665_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_2665_, 0, v_fileName_2645_);
                crate::leanh::lean_ctor_set(v___x_2665_, 1, v_fileMap_2646_);
                crate::leanh::lean_ctor_set(v___x_2665_, 2, v_options_2647_);
                crate::leanh::lean_ctor_set(v___x_2665_, 3, v_currRecDepth_2648_);
                crate::leanh::lean_ctor_set(v___x_2665_, 4, v_maxRecDepth_2649_);
                crate::leanh::lean_ctor_set(v___x_2665_, 5, v_ref_2664_);
                crate::leanh::lean_ctor_set(v___x_2665_, 6, v_currNamespace_2651_);
                crate::leanh::lean_ctor_set(v___x_2665_, 7, v_openDecls_2652_);
                crate::leanh::lean_ctor_set(v___x_2665_, 8, v_initHeartbeats_2653_);
                crate::leanh::lean_ctor_set(v___x_2665_, 9, v_maxHeartbeats_2654_);
                crate::leanh::lean_ctor_set(v___x_2665_, 10, v_quotContext_2655_);
                crate::leanh::lean_ctor_set(v___x_2665_, 11, v_currMacroScope_2656_);
                crate::leanh::lean_ctor_set(v___x_2665_, 12, v_cancelTk_x3f_2658_);
                crate::leanh::lean_ctor_set(v___x_2665_, 13, v_inheritedTraceOptions_2660_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2665_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                    v_diag_2657_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2665_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_2659_,
                );
                v___x_2666_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2663_);
                crate::leanh::lean_dec_ref(v_traces_2663_);
                v_sz_2667_ = lean_array_size(v___x_2666_);
                v___x_2668_ = 0usize;
                v___x_2669_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10_spec__11(v_sz_2667_, v___x_2668_, v___x_2666_);
                v_msg_2670_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v_msg_2670_, 0, v_data_2637_);
                crate::leanh::lean_ctor_set(v_msg_2670_, 1, v_msg_2639_);
                crate::leanh::lean_ctor_set(v_msg_2670_, 2, v___x_2669_);
                v___x_2671_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3_spec__5(v_msg_2670_, v___y_2640_, v___y_2641_, v___x_2665_, v___y_2643_);
                crate::leanh::lean_dec_ref_known(v___x_2665_, 14);
                v_a_2672_ = crate::leanh::lean_ctor_get(v___x_2671_, 0);
                v_isSharedCheck_2709_ = (!crate::leanh::lean_is_exclusive(v___x_2671_)) as u8;
                if v_isSharedCheck_2709_ == 0 {
                    v___x_2674_ = v___x_2671_;
                    v_isShared_2675_ = v_isSharedCheck_2709_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_2672_);
                    crate::leanh::lean_dec(v___x_2671_);
                    v___x_2674_ = crate::leanh::lean_box(0);
                    v_isShared_2675_ = v_isSharedCheck_2709_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2676_ = lean_st_ref_take(v___y_2643_);
                v_traceState_2677_ = crate::leanh::lean_ctor_get(v___x_2676_, 4);
                v_env_2678_ = crate::leanh::lean_ctor_get(v___x_2676_, 0);
                v_nextMacroScope_2679_ = crate::leanh::lean_ctor_get(v___x_2676_, 1);
                v_ngen_2680_ = crate::leanh::lean_ctor_get(v___x_2676_, 2);
                v_auxDeclNGen_2681_ = crate::leanh::lean_ctor_get(v___x_2676_, 3);
                v_cache_2682_ = crate::leanh::lean_ctor_get(v___x_2676_, 5);
                v_messages_2683_ = crate::leanh::lean_ctor_get(v___x_2676_, 6);
                v_infoState_2684_ = crate::leanh::lean_ctor_get(v___x_2676_, 7);
                v_snapshotTasks_2685_ = crate::leanh::lean_ctor_get(v___x_2676_, 8);
                v_isSharedCheck_2708_ = (!crate::leanh::lean_is_exclusive(v___x_2676_)) as u8;
                if v_isSharedCheck_2708_ == 0 {
                    v___x_2687_ = v___x_2676_;
                    v_isShared_2688_ = v_isSharedCheck_2708_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_2685_);
                    crate::leanh::lean_inc(v_infoState_2684_);
                    crate::leanh::lean_inc(v_messages_2683_);
                    crate::leanh::lean_inc(v_cache_2682_);
                    crate::leanh::lean_inc(v_traceState_2677_);
                    crate::leanh::lean_inc(v_auxDeclNGen_2681_);
                    crate::leanh::lean_inc(v_ngen_2680_);
                    crate::leanh::lean_inc(v_nextMacroScope_2679_);
                    crate::leanh::lean_inc(v_env_2678_);
                    crate::leanh::lean_dec(v___x_2676_);
                    v___x_2687_ = crate::leanh::lean_box(0);
                    v_isShared_2688_ = v_isSharedCheck_2708_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_2689_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_2677_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_2706_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_2677_)) as u8;
                if v_isSharedCheck_2706_ == 0 {
                    v_unused_2707_ = crate::leanh::lean_ctor_get(v_traceState_2677_, 0);
                    crate::leanh::lean_dec(v_unused_2707_);
                    v___x_2691_ = v_traceState_2677_;
                    v_isShared_2692_ = v_isSharedCheck_2706_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_traceState_2677_);
                    v___x_2691_ = crate::leanh::lean_box(0);
                    v_isShared_2692_ = v_isSharedCheck_2706_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2693_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2693_, 0, v_ref_2638_);
                crate::leanh::lean_ctor_set(v___x_2693_, 1, v_a_2672_);
                v___x_2694_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2636_, v___x_2693_);
                if v_isShared_2692_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2691_, 0, v___x_2694_);
                    v___x_2696_ = v___x_2691_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2705_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2705_, 0, v___x_2694_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_2705_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_2689_,
                    );
                    v___x_2696_ = v_reuseFailAlloc_2705_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2688_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2687_, 4, v___x_2696_);
                    v___x_2698_ = v___x_2687_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2704_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2704_, 0, v_env_2678_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2704_, 1, v_nextMacroScope_2679_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2704_, 2, v_ngen_2680_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2704_, 3, v_auxDeclNGen_2681_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2704_, 4, v___x_2696_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2704_, 5, v_cache_2682_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2704_, 6, v_messages_2683_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2704_, 7, v_infoState_2684_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2704_, 8, v_snapshotTasks_2685_);
                    v___x_2698_ = v_reuseFailAlloc_2704_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2699_ = lean_st_ref_set(v___y_2643_, v___x_2698_);
                v___x_2700_ = crate::leanh::lean_box(0);
                if v_isShared_2675_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2674_, 0, v___x_2700_);
                    v___x_2702_ = v___x_2674_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2703_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2703_, 0, v___x_2700_);
                    v___x_2702_ = v_reuseFailAlloc_2703_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2702_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10___boxed(
    mut v_oldTraces_2710_: *mut crate::leanh::LeanObject,
    mut v_data_2711_: *mut crate::leanh::LeanObject,
    mut v_ref_2712_: *mut crate::leanh::LeanObject,
    mut v_msg_2713_: *mut crate::leanh::LeanObject,
    mut v___y_2714_: *mut crate::leanh::LeanObject,
    mut v___y_2715_: *mut crate::leanh::LeanObject,
    mut v___y_2716_: *mut crate::leanh::LeanObject,
    mut v___y_2717_: *mut crate::leanh::LeanObject,
    mut v___y_2718_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2719_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10(v_oldTraces_2710_, v_data_2711_, v_ref_2712_, v_msg_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_);
    crate::leanh::lean_dec(v___y_2717_);
    crate::leanh::lean_dec_ref(v___y_2716_);
    crate::leanh::lean_dec(v___y_2715_);
    crate::leanh::lean_dec_ref(v___y_2714_);
    return v_res_2719_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__11___redArg(
    mut v_x_2720_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2725_: u8 = 0;
    let mut v___x_2727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2729_: u8 = 0;
    let mut v_a_2730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2733_: u8 = 0;
    let mut v___x_2735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2737_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2720_) == 0 {
                    v_a_2722_ = crate::leanh::lean_ctor_get(v_x_2720_, 0);
                    v_isSharedCheck_2729_ = (!crate::leanh::lean_is_exclusive(v_x_2720_)) as u8;
                    if v_isSharedCheck_2729_ == 0 {
                        v___x_2724_ = v_x_2720_;
                        v_isShared_2725_ = v_isSharedCheck_2729_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2722_);
                        crate::leanh::lean_dec(v_x_2720_);
                        v___x_2724_ = crate::leanh::lean_box(0);
                        v_isShared_2725_ = v_isSharedCheck_2729_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2730_ = crate::leanh::lean_ctor_get(v_x_2720_, 0);
                    v_isSharedCheck_2737_ = (!crate::leanh::lean_is_exclusive(v_x_2720_)) as u8;
                    if v_isSharedCheck_2737_ == 0 {
                        v___x_2732_ = v_x_2720_;
                        v_isShared_2733_ = v_isSharedCheck_2737_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2730_);
                        crate::leanh::lean_dec(v_x_2720_);
                        v___x_2732_ = crate::leanh::lean_box(0);
                        v_isShared_2733_ = v_isSharedCheck_2737_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2725_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2724_, 1);
                    v___x_2727_ = v___x_2724_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2728_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2728_, 0, v_a_2722_);
                    v___x_2727_ = v_reuseFailAlloc_2728_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2727_;
            }
            3 => {
                if v_isShared_2733_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2732_, 0);
                    v___x_2735_ = v___x_2732_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2736_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2736_, 0, v_a_2730_);
                    v___x_2735_ = v_reuseFailAlloc_2736_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2735_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__11___redArg___boxed(
    mut v_x_2738_: *mut crate::leanh::LeanObject,
    mut v___y_2739_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2740_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__11___redArg(v_x_2738_);
    return v_res_2740_;
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__12(
    mut v_opts_2741_: *mut crate::leanh::LeanObject,
    mut v_opt_2742_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_2743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_2744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_2743_ = crate::leanh::lean_ctor_get(v_opt_2742_, 0);
    v_defValue_2744_ = crate::leanh::lean_ctor_get(v_opt_2742_, 1);
    v_map_2745_ = crate::leanh::lean_ctor_get(v_opts_2741_, 0);
    v___x_2746_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2745_,
            v_name_2743_,
        );
    if crate::leanh::lean_obj_tag(v___x_2746_) == 0 {
        crate::leanh::lean_inc(v_defValue_2744_);
        return v_defValue_2744_;
    } else {
        let mut v_val_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2747_ = crate::leanh::lean_ctor_get(v___x_2746_, 0);
        crate::leanh::lean_inc(v_val_2747_);
        crate::leanh::lean_dec_ref_known(v___x_2746_, 1);
        if crate::leanh::lean_obj_tag(v_val_2747_) == 3 {
            let mut v_v_2748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_v_2748_ = crate::leanh::lean_ctor_get(v_val_2747_, 0);
            crate::leanh::lean_inc(v_v_2748_);
            crate::leanh::lean_dec_ref_known(v_val_2747_, 1);
            return v_v_2748_;
        } else {
            crate::leanh::lean_dec(v_val_2747_);
            crate::leanh::lean_inc(v_defValue_2744_);
            return v_defValue_2744_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__12___boxed(
    mut v_opts_2749_: *mut crate::leanh::LeanObject,
    mut v_opt_2750_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2751_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__12(v_opts_2749_, v_opt_2750_);
    crate::leanh::lean_dec_ref(v_opt_2750_);
    crate::leanh::lean_dec_ref(v_opts_2749_);
    return v_res_2751_;
}
pub unsafe fn l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__9(
    mut v_e_2752_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_e_2752_) == 0 {
        let mut v___x_2753_: u8 = 0;
        v___x_2753_ = 2;
        return v___x_2753_;
    } else {
        let mut v___x_2754_: u8 = 0;
        v___x_2754_ = 0;
        return v___x_2754_;
    }
}
pub unsafe fn l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__9___boxed(
    mut v_e_2755_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2756_: u8 = 0;
    let mut v_r_2757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2756_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__9(v_e_2755_);
    crate::leanh::lean_dec_ref(v_e_2755_);
    v_r_2757_ = crate::leanh::lean_box((v_res_2756_) as usize);
    return v_r_2757_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2759_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__0;
    v___x_2760_ = l_Lean_stringToMessageData(v___x_2759_);
    return v___x_2760_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__2()
-> f64 {
    let mut v___x_2761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: f64 = 0.0;
    v___x_2761_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2762_ = lean_float_of_nat(v___x_2761_);
    return v___x_2762_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2764_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__3;
    v___x_2765_ = l_Lean_stringToMessageData(v___x_2764_);
    return v___x_2765_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__5()
-> f64 {
    let mut v___x_2766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: f64 = 0.0;
    v___x_2766_ = crate::leanh::lean_unsigned_to_nat(1000);
    v___x_2767_ = lean_float_of_nat(v___x_2766_);
    return v___x_2767_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6(
    mut v_cls_2768_: *mut crate::leanh::LeanObject,
    mut v_collapsed_2769_: u8,
    mut v_tag_2770_: *mut crate::leanh::LeanObject,
    mut v_opts_2771_: *mut crate::leanh::LeanObject,
    mut v_clsEnabled_2772_: u8,
    mut v_oldTraces_2773_: *mut crate::leanh::LeanObject,
    mut v_msg_2774_: *mut crate::leanh::LeanObject,
    mut v_resStartStop_2775_: *mut crate::leanh::LeanObject,
    mut v___y_2776_: *mut crate::leanh::LeanObject,
    mut v___y_2777_: *mut crate::leanh::LeanObject,
    mut v___y_2778_: *mut crate::leanh::LeanObject,
    mut v___y_2779_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_2781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2785_: u8 = 0;
    let mut v___y_2787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_2789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2795_: u8 = 0;
    let mut v___x_2797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2799_: u8 = 0;
    let mut v_fst_2800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2804_: u8 = 0;
    let mut v___x_2805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: u8 = 0;
    let mut v___y_2808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_2810_: u8 = 0;
    let mut v___x_2811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_2817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: f64 = 0.0;
    let mut v_data_2821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_2822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: f64 = 0.0;
    let mut v___x_2824_: f64 = 0.0;
    let mut v_reuseFailAlloc_2825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2833_: u8 = 0;
    let mut v___x_2834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2846_: u8 = 0;
    let mut v_tid_2847_: u64 = 0;
    let mut v_traces_2848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2851_: u8 = 0;
    let mut v___x_2852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2861_: u8 = 0;
    let mut v_isSharedCheck_2862_: u8 = 0;
    let mut v___y_2864_: f64 = 0.0;
    let mut v___x_2865_: f64 = 0.0;
    let mut v___x_2866_: f64 = 0.0;
    let mut v___x_2867_: f64 = 0.0;
    let mut v___x_2868_: u8 = 0;
    let mut v___x_2869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: u8 = 0;
    let mut v___x_2871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: f64 = 0.0;
    let mut v___x_2874_: f64 = 0.0;
    let mut v___x_2875_: f64 = 0.0;
    let mut v___x_2876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: f64 = 0.0;
    let mut v_isSharedCheck_2879_: u8 = 0;
    let mut v_isSharedCheck_2880_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2781_ = crate::leanh::lean_ctor_get(v_resStartStop_2775_, 0);
                v_snd_2782_ = crate::leanh::lean_ctor_get(v_resStartStop_2775_, 1);
                v_isSharedCheck_2880_ =
                    (!crate::leanh::lean_is_exclusive(v_resStartStop_2775_)) as u8;
                if v_isSharedCheck_2880_ == 0 {
                    v___x_2784_ = v_resStartStop_2775_;
                    v_isShared_2785_ = v_isSharedCheck_2880_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2782_);
                    crate::leanh::lean_inc(v_fst_2781_);
                    crate::leanh::lean_dec(v_resStartStop_2775_);
                    v___x_2784_ = crate::leanh::lean_box(0);
                    v_isShared_2785_ = v_isSharedCheck_2880_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_2800_ = crate::leanh::lean_ctor_get(v_snd_2782_, 0);
                v_snd_2801_ = crate::leanh::lean_ctor_get(v_snd_2782_, 1);
                v_isSharedCheck_2879_ = (!crate::leanh::lean_is_exclusive(v_snd_2782_)) as u8;
                if v_isSharedCheck_2879_ == 0 {
                    v___x_2803_ = v_snd_2782_;
                    v_isShared_2804_ = v_isSharedCheck_2879_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2801_);
                    crate::leanh::lean_inc(v_fst_2800_);
                    crate::leanh::lean_dec(v_snd_2782_);
                    v___x_2803_ = crate::leanh::lean_box(0);
                    v_isShared_2804_ = v_isSharedCheck_2879_;
                    state = 5;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v___y_2787_);
                v___x_2790_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10(v_oldTraces_2773_, v_data_2789_, v___y_2787_, v___y_2788_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_);
                if crate::leanh::lean_obj_tag(v___x_2790_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_2790_, 1);
                    v___x_2791_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__11___redArg(v_fst_2781_);
                    return v___x_2791_;
                } else {
                    crate::leanh::lean_dec(v_fst_2781_);
                    v_a_2792_ = crate::leanh::lean_ctor_get(v___x_2790_, 0);
                    v_isSharedCheck_2799_ = (!crate::leanh::lean_is_exclusive(v___x_2790_)) as u8;
                    if v_isSharedCheck_2799_ == 0 {
                        v___x_2794_ = v___x_2790_;
                        v_isShared_2795_ = v_isSharedCheck_2799_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2792_);
                        crate::leanh::lean_dec(v___x_2790_);
                        v___x_2794_ = crate::leanh::lean_box(0);
                        v_isShared_2795_ = v_isSharedCheck_2799_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_2795_ == 0 {
                    v___x_2797_ = v___x_2794_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2798_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2798_, 0, v_a_2792_);
                    v___x_2797_ = v_reuseFailAlloc_2798_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2797_;
            }
            5 => {
                v___x_2805_ = l_Lean_trace_profiler;
                v___x_2806_ = l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__5(
                    v_opts_2771_,
                    v___x_2805_,
                );
                if v___x_2806_ == 0 {
                    v___y_2833_ = v___x_2806_;
                    state = 10;
                    continue;
                } else {
                    v___x_2869_ = l_Lean_trace_profiler_useHeartbeats;
                    v___x_2870_ = l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__5(
                        v_opts_2771_,
                        v___x_2869_,
                    );
                    if v___x_2870_ == 0 {
                        v___x_2871_ = l_Lean_trace_profiler_threshold;
                        v___x_2872_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__12(v_opts_2771_, v___x_2871_);
                        v___x_2873_ = lean_float_of_nat(v___x_2872_);
                        v___x_2874_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__5_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__5);
                        v___x_2875_ = lean_float_div(v___x_2873_, v___x_2874_);
                        v___y_2864_ = v___x_2875_;
                        state = 15;
                        continue;
                    } else {
                        v___x_2876_ = l_Lean_trace_profiler_threshold;
                        v___x_2877_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__12(v_opts_2771_, v___x_2876_);
                        v___x_2878_ = lean_float_of_nat(v___x_2877_);
                        v___y_2864_ = v___x_2878_;
                        state = 15;
                        continue;
                    }
                }
            }
            6 => {
                v_result_2810_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__9(v_fst_2781_);
                v___x_2811_ = l_Lean_TraceResult_toEmoji(v_result_2810_);
                v___x_2812_ = l_Lean_stringToMessageData(v___x_2811_);
                v___x_2813_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__1_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__1);
                if v_isShared_2804_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2803_, 7);
                    crate::leanh::lean_ctor_set(v___x_2803_, 1, v___x_2813_);
                    crate::leanh::lean_ctor_set(v___x_2803_, 0, v___x_2812_);
                    v___x_2815_ = v___x_2803_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2826_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2826_, 0, v___x_2812_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2826_, 1, v___x_2813_);
                    v___x_2815_ = v_reuseFailAlloc_2826_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2785_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2784_, 7);
                    crate::leanh::lean_ctor_set(v___x_2784_, 1, v_a_2809_);
                    crate::leanh::lean_ctor_set(v___x_2784_, 0, v___x_2815_);
                    v_m_2817_ = v___x_2784_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2825_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2825_, 0, v___x_2815_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2825_, 1, v_a_2809_);
                    v_m_2817_ = v_reuseFailAlloc_2825_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2818_ = crate::leanh::lean_box((v_result_2810_) as usize);
                v___x_2819_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2819_, 0, v___x_2818_);
                v___x_2820_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__2_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__2);
                crate::leanh::lean_inc_ref(v_tag_2770_);
                crate::leanh::lean_inc_ref(v___x_2819_);
                crate::leanh::lean_inc(v_cls_2768_);
                v_data_2821_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v_data_2821_, 0, v_cls_2768_);
                crate::leanh::lean_ctor_set(v_data_2821_, 1, v___x_2819_);
                crate::leanh::lean_ctor_set(v_data_2821_, 2, v_tag_2770_);
                crate::leanh::lean_ctor_set_float(
                    v_data_2821_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_2820_,
                );
                crate::leanh::lean_ctor_set_float(
                    v_data_2821_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_2820_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v_data_2821_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v_collapsed_2769_,
                );
                if v___x_2806_ == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_2819_, 1);
                    crate::leanh::lean_dec(v_snd_2801_);
                    crate::leanh::lean_dec(v_fst_2800_);
                    crate::leanh::lean_dec_ref(v_tag_2770_);
                    crate::leanh::lean_dec(v_cls_2768_);
                    v___y_2787_ = v___y_2808_;
                    v___y_2788_ = v_m_2817_;
                    v_data_2789_ = v_data_2821_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref_known(v_data_2821_, 3);
                    v_data_2822_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                    crate::leanh::lean_ctor_set(v_data_2822_, 0, v_cls_2768_);
                    crate::leanh::lean_ctor_set(v_data_2822_, 1, v___x_2819_);
                    crate::leanh::lean_ctor_set(v_data_2822_, 2, v_tag_2770_);
                    v___x_2823_ = crate::leanh::lean_unbox_float(v_fst_2800_);
                    crate::leanh::lean_dec(v_fst_2800_);
                    crate::leanh::lean_ctor_set_float(
                        v_data_2822_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v___x_2823_,
                    );
                    v___x_2824_ = crate::leanh::lean_unbox_float(v_snd_2801_);
                    crate::leanh::lean_dec(v_snd_2801_);
                    crate::leanh::lean_ctor_set_float(
                        v_data_2822_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                        v___x_2824_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_data_2822_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                        v_collapsed_2769_,
                    );
                    v___y_2787_ = v___y_2808_;
                    v___y_2788_ = v_m_2817_;
                    v_data_2789_ = v_data_2822_;
                    state = 2;
                    continue;
                }
            }
            9 => {
                v_ref_2828_ = crate::leanh::lean_ctor_get(v___y_2778_, 5);
                crate::leanh::lean_inc(v___y_2779_);
                crate::leanh::lean_inc_ref(v___y_2778_);
                crate::leanh::lean_inc(v___y_2777_);
                crate::leanh::lean_inc_ref(v___y_2776_);
                crate::leanh::lean_inc(v_fst_2781_);
                v___x_2829_ = crate::leanh::lean_apply_6(
                    v_msg_2774_,
                    v_fst_2781_,
                    v___y_2776_,
                    v___y_2777_,
                    v___y_2778_,
                    v___y_2779_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_2829_) == 0 {
                    v_a_2830_ = crate::leanh::lean_ctor_get(v___x_2829_, 0);
                    crate::leanh::lean_inc(v_a_2830_);
                    crate::leanh::lean_dec_ref_known(v___x_2829_, 1);
                    v___y_2808_ = v_ref_2828_;
                    v_a_2809_ = v_a_2830_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_2829_, 1);
                    v___x_2831_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__4_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__4);
                    v___y_2808_ = v_ref_2828_;
                    v_a_2809_ = v___x_2831_;
                    state = 6;
                    continue;
                }
            }
            10 => {
                if v_clsEnabled_2772_ == 0 {
                    if v___y_2833_ == 0 {
                        crate::leanh::lean_del_object(v___x_2803_);
                        crate::leanh::lean_dec(v_snd_2801_);
                        crate::leanh::lean_dec(v_fst_2800_);
                        crate::leanh::lean_del_object(v___x_2784_);
                        crate::leanh::lean_dec_ref(v_msg_2774_);
                        crate::leanh::lean_dec_ref(v_tag_2770_);
                        crate::leanh::lean_dec(v_cls_2768_);
                        v___x_2834_ = lean_st_ref_take(v___y_2779_);
                        v_traceState_2835_ = crate::leanh::lean_ctor_get(v___x_2834_, 4);
                        v_env_2836_ = crate::leanh::lean_ctor_get(v___x_2834_, 0);
                        v_nextMacroScope_2837_ = crate::leanh::lean_ctor_get(v___x_2834_, 1);
                        v_ngen_2838_ = crate::leanh::lean_ctor_get(v___x_2834_, 2);
                        v_auxDeclNGen_2839_ = crate::leanh::lean_ctor_get(v___x_2834_, 3);
                        v_cache_2840_ = crate::leanh::lean_ctor_get(v___x_2834_, 5);
                        v_messages_2841_ = crate::leanh::lean_ctor_get(v___x_2834_, 6);
                        v_infoState_2842_ = crate::leanh::lean_ctor_get(v___x_2834_, 7);
                        v_snapshotTasks_2843_ = crate::leanh::lean_ctor_get(v___x_2834_, 8);
                        v_isSharedCheck_2862_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2834_)) as u8;
                        if v_isSharedCheck_2862_ == 0 {
                            v___x_2845_ = v___x_2834_;
                            v_isShared_2846_ = v_isSharedCheck_2862_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snapshotTasks_2843_);
                            crate::leanh::lean_inc(v_infoState_2842_);
                            crate::leanh::lean_inc(v_messages_2841_);
                            crate::leanh::lean_inc(v_cache_2840_);
                            crate::leanh::lean_inc(v_traceState_2835_);
                            crate::leanh::lean_inc(v_auxDeclNGen_2839_);
                            crate::leanh::lean_inc(v_ngen_2838_);
                            crate::leanh::lean_inc(v_nextMacroScope_2837_);
                            crate::leanh::lean_inc(v_env_2836_);
                            crate::leanh::lean_dec(v___x_2834_);
                            v___x_2845_ = crate::leanh::lean_box(0);
                            v_isShared_2846_ = v_isSharedCheck_2862_;
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
                v_tid_2847_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_2835_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_2848_ = crate::leanh::lean_ctor_get(v_traceState_2835_, 0);
                v_isSharedCheck_2861_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_2835_)) as u8;
                if v_isSharedCheck_2861_ == 0 {
                    v___x_2850_ = v_traceState_2835_;
                    v_isShared_2851_ = v_isSharedCheck_2861_;
                    state = 12;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_2848_);
                    crate::leanh::lean_dec(v_traceState_2835_);
                    v___x_2850_ = crate::leanh::lean_box(0);
                    v_isShared_2851_ = v_isSharedCheck_2861_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_2852_ =
                    l_Lean_PersistentArray_append___redArg(v_oldTraces_2773_, v_traces_2848_);
                crate::leanh::lean_dec_ref(v_traces_2848_);
                if v_isShared_2851_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2850_, 0, v___x_2852_);
                    v___x_2854_ = v___x_2850_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2860_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2860_, 0, v___x_2852_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_2860_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_2847_,
                    );
                    v___x_2854_ = v_reuseFailAlloc_2860_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_2846_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2845_, 4, v___x_2854_);
                    v___x_2856_ = v___x_2845_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2859_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2859_, 0, v_env_2836_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2859_, 1, v_nextMacroScope_2837_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2859_, 2, v_ngen_2838_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2859_, 3, v_auxDeclNGen_2839_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2859_, 4, v___x_2854_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2859_, 5, v_cache_2840_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2859_, 6, v_messages_2841_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2859_, 7, v_infoState_2842_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2859_, 8, v_snapshotTasks_2843_);
                    v___x_2856_ = v_reuseFailAlloc_2859_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_2857_ = lean_st_ref_set(v___y_2779_, v___x_2856_);
                v___x_2858_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__11___redArg(v_fst_2781_);
                return v___x_2858_;
            }
            15 => {
                v___x_2865_ = crate::leanh::lean_unbox_float(v_snd_2801_);
                v___x_2866_ = crate::leanh::lean_unbox_float(v_fst_2800_);
                v___x_2867_ = lean_float_sub(v___x_2865_, v___x_2866_);
                v___x_2868_ = lean_float_decLt(v___y_2864_, v___x_2867_);
                v___y_2833_ = v___x_2868_;
                state = 10;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___boxed(
    mut v_cls_2881_: *mut crate::leanh::LeanObject,
    mut v_collapsed_2882_: *mut crate::leanh::LeanObject,
    mut v_tag_2883_: *mut crate::leanh::LeanObject,
    mut v_opts_2884_: *mut crate::leanh::LeanObject,
    mut v_clsEnabled_2885_: *mut crate::leanh::LeanObject,
    mut v_oldTraces_2886_: *mut crate::leanh::LeanObject,
    mut v_msg_2887_: *mut crate::leanh::LeanObject,
    mut v_resStartStop_2888_: *mut crate::leanh::LeanObject,
    mut v___y_2889_: *mut crate::leanh::LeanObject,
    mut v___y_2890_: *mut crate::leanh::LeanObject,
    mut v___y_2891_: *mut crate::leanh::LeanObject,
    mut v___y_2892_: *mut crate::leanh::LeanObject,
    mut v___y_2893_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_collapsed_boxed_2894_: u8 = 0;
    let mut v_clsEnabled_boxed_2895_: u8 = 0;
    let mut v_res_2896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_2894_ = (crate::leanh::lean_unbox(v_collapsed_2882_) as u8);
    v_clsEnabled_boxed_2895_ = (crate::leanh::lean_unbox(v_clsEnabled_2885_) as u8);
    v_res_2896_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6(v_cls_2881_, v_collapsed_boxed_2894_, v_tag_2883_, v_opts_2884_, v_clsEnabled_boxed_2895_, v_oldTraces_2886_, v_msg_2887_, v_resStartStop_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_);
    crate::leanh::lean_dec(v___y_2892_);
    crate::leanh::lean_dec_ref(v___y_2891_);
    crate::leanh::lean_dec(v___y_2890_);
    crate::leanh::lean_dec_ref(v___y_2889_);
    crate::leanh::lean_dec_ref(v_opts_2884_);
    return v_res_2896_;
}
pub unsafe fn _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2910_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__5;
    v___x_2911_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__8;
    v___x_2912_ = l_Lean_Name_append(v___x_2911_, v___x_2910_);
    return v___x_2912_;
}
pub unsafe fn _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__10()
-> f64 {
    let mut v___x_2913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2914_: f64 = 0.0;
    v___x_2913_ = crate::leanh::lean_unsigned_to_nat(1000000000);
    v___x_2914_ = lean_float_of_nat(v___x_2913_);
    return v___x_2914_;
}
pub unsafe fn _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2916_ =
        l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__11;
    v___x_2917_ = l_Lean_stringToMessageData(v___x_2916_);
    return v___x_2917_;
}
pub unsafe fn _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2919_ =
        l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__13;
    v___x_2920_ = l_Lean_stringToMessageData(v___x_2919_);
    return v___x_2920_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7(
    mut v_snd_2921_: *mut crate::leanh::LeanObject,
    mut v_mvarId_2922_: *mut crate::leanh::LeanObject,
    mut v_x_2923_: *mut crate::leanh::LeanObject,
    mut v_x_2924_: *mut crate::leanh::LeanObject,
    mut v_x_2925_: *mut crate::leanh::LeanObject,
    mut v___y_2926_: *mut crate::leanh::LeanObject,
    mut v___y_2927_: *mut crate::leanh::LeanObject,
    mut v___y_2928_: *mut crate::leanh::LeanObject,
    mut v___y_2929_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fn_2931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_2932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_2937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_majorPos_2942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arity_2943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_insterestingCtors_2944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_2945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_2946_: u8 = 0;
    let mut v___f_2947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2951_: u8 = 0;
    let mut v___x_2952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: u8 = 0;
    let mut v___y_2959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: f64 = 0.0;
    let mut v___x_2964_: f64 = 0.0;
    let mut v___x_2965_: f64 = 0.0;
    let mut v___x_2966_: f64 = 0.0;
    let mut v___x_2967_: f64 = 0.0;
    let mut v___x_2968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: f64 = 0.0;
    let mut v___x_2979_: f64 = 0.0;
    let mut v___x_2980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: u8 = 0;
    let mut v___x_2990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2995_: u8 = 0;
    let mut v___x_2997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2999_: u8 = 0;
    let mut v_a_3000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3003_: u8 = 0;
    let mut v___x_3005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3007_: u8 = 0;
    let mut v___x_3008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3013_: u8 = 0;
    let mut v___x_3015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3017_: u8 = 0;
    let mut v_a_3018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3021_: u8 = 0;
    let mut v___x_3023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3025_: u8 = 0;
    let mut v___x_3026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: u8 = 0;
    let mut v___x_3028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3034_: u8 = 0;
    let mut v___x_3036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3038_: u8 = 0;
    let mut v___x_3039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2923_) == 5 {
                    v_fn_2931_ = crate::leanh::lean_ctor_get(v_x_2923_, 0);
                    crate::leanh::lean_inc_ref(v_fn_2931_);
                    v_arg_2932_ = crate::leanh::lean_ctor_get(v_x_2923_, 1);
                    crate::leanh::lean_inc_ref(v_arg_2932_);
                    crate::leanh::lean_dec_ref_known(v_x_2923_, 2);
                    v___x_2933_ = lean_array_set(v_x_2924_, v_x_2925_, v_arg_2932_);
                    v___x_2934_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2935_ = lean_nat_sub(v_x_2925_, v___x_2934_);
                    crate::leanh::lean_dec(v_x_2925_);
                    v_x_2923_ = v_fn_2931_;
                    v_x_2924_ = v___x_2933_;
                    v_x_2925_ = v___x_2935_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_x_2925_);
                    if crate::leanh::lean_obj_tag(v_x_2923_) == 4 {
                        v_declName_2937_ = crate::leanh::lean_ctor_get(v_x_2923_, 0);
                        crate::leanh::lean_inc_n(v_declName_2937_, 2);
                        crate::leanh::lean_dec_ref_known(v_x_2923_, 2);
                        v___x_2938_ = l_Lean_Meta_getSparseCasesOnInfo___redArg(
                            v_declName_2937_,
                            v___y_2929_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2938_) == 0 {
                            v_a_2939_ = crate::leanh::lean_ctor_get(v___x_2938_, 0);
                            crate::leanh::lean_inc(v_a_2939_);
                            crate::leanh::lean_dec_ref_known(v___x_2938_, 1);
                            if crate::leanh::lean_obj_tag(v_a_2939_) == 1 {
                                v_val_2940_ = crate::leanh::lean_ctor_get(v_a_2939_, 0);
                                crate::leanh::lean_inc(v_val_2940_);
                                crate::leanh::lean_dec_ref_known(v_a_2939_, 1);
                                v_options_2941_ = crate::leanh::lean_ctor_get(v___y_2928_, 2);
                                v_majorPos_2942_ = crate::leanh::lean_ctor_get(v_val_2940_, 1);
                                crate::leanh::lean_inc(v_majorPos_2942_);
                                v_arity_2943_ = crate::leanh::lean_ctor_get(v_val_2940_, 2);
                                crate::leanh::lean_inc_n(v_arity_2943_, 2);
                                v_insterestingCtors_2944_ =
                                    crate::leanh::lean_ctor_get(v_val_2940_, 3);
                                crate::leanh::lean_inc_ref(v_insterestingCtors_2944_);
                                crate::leanh::lean_dec(v_val_2940_);
                                v_inheritedTraceOptions_2945_ =
                                    crate::leanh::lean_ctor_get(v___y_2928_, 13);
                                v_hasTrace_2946_ = crate::leanh::lean_ctor_get_uint8(
                                    v_options_2941_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                                        as u32,
                                );
                                v___f_2947_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__0;
                                v___x_2948_ = l_Lean_instInhabitedExpr;
                                crate::leanh::lean_inc_ref(v_x_2924_);
                                v___f_2949_ = crate::leanh::lean_alloc_closure(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___boxed as *mut core::ffi::c_void, 15, 9);
                                crate::leanh::lean_closure_set(v___f_2949_, 0, v___x_2948_);
                                crate::leanh::lean_closure_set(v___f_2949_, 1, v_x_2924_);
                                crate::leanh::lean_closure_set(v___f_2949_, 2, v_majorPos_2942_);
                                crate::leanh::lean_closure_set(
                                    v___f_2949_,
                                    3,
                                    v_insterestingCtors_2944_,
                                );
                                crate::leanh::lean_closure_set(v___f_2949_, 4, v_declName_2937_);
                                crate::leanh::lean_closure_set(v___f_2949_, 5, v_snd_2921_);
                                crate::leanh::lean_closure_set(v___f_2949_, 6, v_arity_2943_);
                                crate::leanh::lean_closure_set(v___f_2949_, 7, v_mvarId_2922_);
                                crate::leanh::lean_closure_set(v___f_2949_, 8, v___f_2947_);
                                v___x_2950_ = lean_array_get_size(v_x_2924_);
                                crate::leanh::lean_dec_ref(v_x_2924_);
                                v___x_2951_ = lean_nat_dec_lt(v___x_2950_, v_arity_2943_);
                                crate::leanh::lean_dec(v_arity_2943_);
                                if v_hasTrace_2946_ == 0 {
                                    v___x_2952_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1(v___x_2951_, v___f_2949_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_);
                                    return v___x_2952_;
                                } else {
                                    v___f_2953_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__1;
                                    v___x_2954_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__5;
                                    v___x_2955_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__6;
                                    v___x_2956_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__9), core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__9_once), _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__9);
                                    v___x_2957_ =
                                        l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                            v_inheritedTraceOptions_2945_,
                                            v_options_2941_,
                                            v___x_2956_,
                                        );
                                    if v___x_2957_ == 0 {
                                        v___x_3026_ = l_Lean_trace_profiler;
                                        v___x_3027_ = l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__5(v_options_2941_, v___x_3026_);
                                        if v___x_3027_ == 0 {
                                            v___x_3028_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1(v___x_2951_, v___f_2949_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_);
                                            return v___x_3028_;
                                        } else {
                                            state = 3;
                                            continue;
                                        }
                                    } else {
                                        state = 3;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_2939_);
                                crate::leanh::lean_dec(v_declName_2937_);
                                crate::leanh::lean_dec_ref(v_x_2924_);
                                crate::leanh::lean_dec(v_mvarId_2922_);
                                crate::leanh::lean_dec_ref(v_snd_2921_);
                                v___x_3029_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__12), core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__12_once), _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__12);
                                v___x_3030_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_3029_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_);
                                return v___x_3030_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_declName_2937_);
                            crate::leanh::lean_dec_ref(v_x_2924_);
                            crate::leanh::lean_dec(v_mvarId_2922_);
                            crate::leanh::lean_dec_ref(v_snd_2921_);
                            v_a_3031_ = crate::leanh::lean_ctor_get(v___x_2938_, 0);
                            v_isSharedCheck_3038_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2938_)) as u8;
                            if v_isSharedCheck_3038_ == 0 {
                                v___x_3033_ = v___x_2938_;
                                v_isShared_3034_ = v_isSharedCheck_3038_;
                                state = 12;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3031_);
                                crate::leanh::lean_dec(v___x_2938_);
                                v___x_3033_ = crate::leanh::lean_box(0);
                                v_isShared_3034_ = v_isSharedCheck_3038_;
                                state = 12;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_x_2924_);
                        crate::leanh::lean_dec_ref(v_x_2923_);
                        crate::leanh::lean_dec(v_mvarId_2922_);
                        crate::leanh::lean_dec_ref(v_snd_2921_);
                        v___x_3039_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__14), core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__14_once), _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__14);
                        v___x_3040_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_3039_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_);
                        return v___x_3040_;
                    }
                }
            }
            1 => {
                v___x_2962_ = lean_io_mono_nanos_now();
                v___x_2963_ = lean_float_of_nat(v___y_2960_);
                v___x_2964_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__10), core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__10_once), _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__10);
                v___x_2965_ = lean_float_div(v___x_2963_, v___x_2964_);
                v___x_2966_ = lean_float_of_nat(v___x_2962_);
                v___x_2967_ = lean_float_div(v___x_2966_, v___x_2964_);
                v___x_2968_ = crate::leanh::lean_box_float(v___x_2965_);
                v___x_2969_ = crate::leanh::lean_box_float(v___x_2967_);
                v___x_2970_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2970_, 0, v___x_2968_);
                crate::leanh::lean_ctor_set(v___x_2970_, 1, v___x_2969_);
                v___x_2971_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2971_, 0, v_a_2961_);
                crate::leanh::lean_ctor_set(v___x_2971_, 1, v___x_2970_);
                v___x_2972_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6(v___x_2954_, v_hasTrace_2946_, v___x_2955_, v_options_2941_, v___x_2957_, v___y_2959_, v___f_2953_, v___x_2971_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_);
                return v___x_2972_;
            }
            2 => {
                v___x_2977_ = lean_io_get_num_heartbeats();
                v___x_2978_ = lean_float_of_nat(v___y_2975_);
                v___x_2979_ = lean_float_of_nat(v___x_2977_);
                v___x_2980_ = crate::leanh::lean_box_float(v___x_2978_);
                v___x_2981_ = crate::leanh::lean_box_float(v___x_2979_);
                v___x_2982_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2982_, 0, v___x_2980_);
                crate::leanh::lean_ctor_set(v___x_2982_, 1, v___x_2981_);
                v___x_2983_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2983_, 0, v_a_2976_);
                crate::leanh::lean_ctor_set(v___x_2983_, 1, v___x_2982_);
                v___x_2984_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6(v___x_2954_, v_hasTrace_2946_, v___x_2955_, v_options_2941_, v___x_2957_, v___y_2974_, v___f_2953_, v___x_2983_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_);
                return v___x_2984_;
            }
            3 => {
                v___x_2986_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg(v___y_2929_);
                v_a_2987_ = crate::leanh::lean_ctor_get(v___x_2986_, 0);
                crate::leanh::lean_inc(v_a_2987_);
                crate::leanh::lean_dec_ref(v___x_2986_);
                v___x_2988_ = l_Lean_trace_profiler_useHeartbeats;
                v___x_2989_ = l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__5(
                    v_options_2941_,
                    v___x_2988_,
                );
                if v___x_2989_ == 0 {
                    v___x_2990_ = lean_io_mono_nanos_now();
                    v___x_2991_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1(v___x_2951_, v___f_2949_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_);
                    if crate::leanh::lean_obj_tag(v___x_2991_) == 0 {
                        v_a_2992_ = crate::leanh::lean_ctor_get(v___x_2991_, 0);
                        v_isSharedCheck_2999_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2991_)) as u8;
                        if v_isSharedCheck_2999_ == 0 {
                            v___x_2994_ = v___x_2991_;
                            v_isShared_2995_ = v_isSharedCheck_2999_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2992_);
                            crate::leanh::lean_dec(v___x_2991_);
                            v___x_2994_ = crate::leanh::lean_box(0);
                            v_isShared_2995_ = v_isSharedCheck_2999_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v_a_3000_ = crate::leanh::lean_ctor_get(v___x_2991_, 0);
                        v_isSharedCheck_3007_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2991_)) as u8;
                        if v_isSharedCheck_3007_ == 0 {
                            v___x_3002_ = v___x_2991_;
                            v_isShared_3003_ = v_isSharedCheck_3007_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3000_);
                            crate::leanh::lean_dec(v___x_2991_);
                            v___x_3002_ = crate::leanh::lean_box(0);
                            v_isShared_3003_ = v_isSharedCheck_3007_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    v___x_3008_ = lean_io_get_num_heartbeats();
                    v___x_3009_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1(v___x_2951_, v___f_2949_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_);
                    if crate::leanh::lean_obj_tag(v___x_3009_) == 0 {
                        v_a_3010_ = crate::leanh::lean_ctor_get(v___x_3009_, 0);
                        v_isSharedCheck_3017_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3009_)) as u8;
                        if v_isSharedCheck_3017_ == 0 {
                            v___x_3012_ = v___x_3009_;
                            v_isShared_3013_ = v_isSharedCheck_3017_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3010_);
                            crate::leanh::lean_dec(v___x_3009_);
                            v___x_3012_ = crate::leanh::lean_box(0);
                            v_isShared_3013_ = v_isSharedCheck_3017_;
                            state = 8;
                            continue;
                        }
                    } else {
                        v_a_3018_ = crate::leanh::lean_ctor_get(v___x_3009_, 0);
                        v_isSharedCheck_3025_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3009_)) as u8;
                        if v_isSharedCheck_3025_ == 0 {
                            v___x_3020_ = v___x_3009_;
                            v_isShared_3021_ = v_isSharedCheck_3025_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3018_);
                            crate::leanh::lean_dec(v___x_3009_);
                            v___x_3020_ = crate::leanh::lean_box(0);
                            v_isShared_3021_ = v_isSharedCheck_3025_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            4 => {
                if v_isShared_2995_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2994_, 1);
                    v___x_2997_ = v___x_2994_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2998_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2998_, 0, v_a_2992_);
                    v___x_2997_ = v_reuseFailAlloc_2998_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___y_2959_ = v_a_2987_;
                v___y_2960_ = v___x_2990_;
                v_a_2961_ = v___x_2997_;
                state = 1;
                continue;
            }
            6 => {
                if v_isShared_3003_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3002_, 0);
                    v___x_3005_ = v___x_3002_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3006_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3006_, 0, v_a_3000_);
                    v___x_3005_ = v_reuseFailAlloc_3006_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_2959_ = v_a_2987_;
                v___y_2960_ = v___x_2990_;
                v_a_2961_ = v___x_3005_;
                state = 1;
                continue;
            }
            8 => {
                if v_isShared_3013_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3012_, 1);
                    v___x_3015_ = v___x_3012_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3016_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3016_, 0, v_a_3010_);
                    v___x_3015_ = v_reuseFailAlloc_3016_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___y_2974_ = v_a_2987_;
                v___y_2975_ = v___x_3008_;
                v_a_2976_ = v___x_3015_;
                state = 2;
                continue;
            }
            10 => {
                if v_isShared_3021_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3020_, 0);
                    v___x_3023_ = v___x_3020_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3024_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3024_, 0, v_a_3018_);
                    v___x_3023_ = v_reuseFailAlloc_3024_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___y_2974_ = v_a_2987_;
                v___y_2975_ = v___x_3008_;
                v_a_2976_ = v___x_3023_;
                state = 2;
                continue;
            }
            12 => {
                if v_isShared_3034_ == 0 {
                    v___x_3036_ = v___x_3033_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3037_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3037_, 0, v_a_3031_);
                    v___x_3036_ = v_reuseFailAlloc_3037_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3036_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___boxed(
    mut v_snd_3041_: *mut crate::leanh::LeanObject,
    mut v_mvarId_3042_: *mut crate::leanh::LeanObject,
    mut v_x_3043_: *mut crate::leanh::LeanObject,
    mut v_x_3044_: *mut crate::leanh::LeanObject,
    mut v_x_3045_: *mut crate::leanh::LeanObject,
    mut v___y_3046_: *mut crate::leanh::LeanObject,
    mut v___y_3047_: *mut crate::leanh::LeanObject,
    mut v___y_3048_: *mut crate::leanh::LeanObject,
    mut v___y_3049_: *mut crate::leanh::LeanObject,
    mut v___y_3050_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3051_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7(
        v_snd_3041_,
        v_mvarId_3042_,
        v_x_3043_,
        v_x_3044_,
        v_x_3045_,
        v___y_3046_,
        v___y_3047_,
        v___y_3048_,
        v___y_3049_,
    );
    crate::leanh::lean_dec(v___y_3049_);
    crate::leanh::lean_dec_ref(v___y_3048_);
    crate::leanh::lean_dec(v___y_3047_);
    crate::leanh::lean_dec_ref(v___y_3046_);
    return v_res_3051_;
}
pub unsafe fn _init_l_Lean_Meta_reduceSparseCasesOn___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_3053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3053_ = l_Lean_Meta_reduceSparseCasesOn___closed__0;
    v___x_3054_ = l_Lean_stringToMessageData(v___x_3053_);
    return v___x_3054_;
}
pub unsafe fn l_Lean_Meta_reduceSparseCasesOn(
    mut v_mvarId_3055_: *mut crate::leanh::LeanObject,
    mut v_a_3056_: *mut crate::leanh::LeanObject,
    mut v_a_3057_: *mut crate::leanh::LeanObject,
    mut v_a_3058_: *mut crate::leanh::LeanObject,
    mut v_a_3059_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_3067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_3068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3078_: u8 = 0;
    let mut v___x_3080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3082_: u8 = 0;
    let mut v_a_3083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3086_: u8 = 0;
    let mut v___x_3088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3090_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_mvarId_3055_);
                v___x_3061_ = l_Lean_MVarId_getType(
                    v_mvarId_3055_,
                    v_a_3056_,
                    v_a_3057_,
                    v_a_3058_,
                    v_a_3059_,
                );
                if crate::leanh::lean_obj_tag(v___x_3061_) == 0 {
                    v_a_3062_ = crate::leanh::lean_ctor_get(v___x_3061_, 0);
                    crate::leanh::lean_inc(v_a_3062_);
                    crate::leanh::lean_dec_ref_known(v___x_3061_, 1);
                    v___x_3063_ = l_Lean_Meta_matchEqHEqLHS_x3f(
                        v_a_3062_, v_a_3056_, v_a_3057_, v_a_3058_, v_a_3059_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3063_) == 0 {
                        v_a_3064_ = crate::leanh::lean_ctor_get(v___x_3063_, 0);
                        crate::leanh::lean_inc(v_a_3064_);
                        crate::leanh::lean_dec_ref_known(v___x_3063_, 1);
                        if crate::leanh::lean_obj_tag(v_a_3064_) == 1 {
                            v_val_3065_ = crate::leanh::lean_ctor_get(v_a_3064_, 0);
                            crate::leanh::lean_inc(v_val_3065_);
                            crate::leanh::lean_dec_ref_known(v_a_3064_, 1);
                            v_snd_3066_ = crate::leanh::lean_ctor_get(v_val_3065_, 1);
                            crate::leanh::lean_inc_n(v_snd_3066_, 2);
                            crate::leanh::lean_dec(v_val_3065_);
                            v_dummy_3067_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0), core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0_once), _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0);
                            v_nargs_3068_ = l_Lean_Expr_getAppNumArgs(v_snd_3066_);
                            crate::leanh::lean_inc(v_nargs_3068_);
                            v___x_3069_ = lean_mk_array(v_nargs_3068_, v_dummy_3067_);
                            v___x_3070_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_3071_ = lean_nat_sub(v_nargs_3068_, v___x_3070_);
                            crate::leanh::lean_dec(v_nargs_3068_);
                            v___x_3072_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7(v_snd_3066_, v_mvarId_3055_, v_snd_3066_, v___x_3069_, v___x_3071_, v_a_3056_, v_a_3057_, v_a_3058_, v_a_3059_);
                            return v___x_3072_;
                        } else {
                            crate::leanh::lean_dec(v_a_3064_);
                            crate::leanh::lean_dec(v_mvarId_3055_);
                            v___x_3073_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_reduceSparseCasesOn___closed__1
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_reduceSparseCasesOn___closed__1_once
                                ),
                                _init_l_Lean_Meta_reduceSparseCasesOn___closed__1,
                            );
                            v___x_3074_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_3073_, v_a_3056_, v_a_3057_, v_a_3058_, v_a_3059_);
                            return v___x_3074_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_mvarId_3055_);
                        v_a_3075_ = crate::leanh::lean_ctor_get(v___x_3063_, 0);
                        v_isSharedCheck_3082_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3063_)) as u8;
                        if v_isSharedCheck_3082_ == 0 {
                            v___x_3077_ = v___x_3063_;
                            v_isShared_3078_ = v_isSharedCheck_3082_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3075_);
                            crate::leanh::lean_dec(v___x_3063_);
                            v___x_3077_ = crate::leanh::lean_box(0);
                            v_isShared_3078_ = v_isSharedCheck_3082_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_mvarId_3055_);
                    v_a_3083_ = crate::leanh::lean_ctor_get(v___x_3061_, 0);
                    v_isSharedCheck_3090_ = (!crate::leanh::lean_is_exclusive(v___x_3061_)) as u8;
                    if v_isSharedCheck_3090_ == 0 {
                        v___x_3085_ = v___x_3061_;
                        v_isShared_3086_ = v_isSharedCheck_3090_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3083_);
                        crate::leanh::lean_dec(v___x_3061_);
                        v___x_3085_ = crate::leanh::lean_box(0);
                        v_isShared_3086_ = v_isSharedCheck_3090_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3078_ == 0 {
                    v___x_3080_ = v___x_3077_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3081_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3081_, 0, v_a_3075_);
                    v___x_3080_ = v_reuseFailAlloc_3081_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3080_;
            }
            3 => {
                if v_isShared_3086_ == 0 {
                    v___x_3088_ = v___x_3085_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3089_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3089_, 0, v_a_3083_);
                    v___x_3088_ = v_reuseFailAlloc_3089_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3088_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_reduceSparseCasesOn___boxed(
    mut v_mvarId_3091_: *mut crate::leanh::LeanObject,
    mut v_a_3092_: *mut crate::leanh::LeanObject,
    mut v_a_3093_: *mut crate::leanh::LeanObject,
    mut v_a_3094_: *mut crate::leanh::LeanObject,
    mut v_a_3095_: *mut crate::leanh::LeanObject,
    mut v_a_3096_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3097_ =
        l_Lean_Meta_reduceSparseCasesOn(v_mvarId_3091_, v_a_3092_, v_a_3093_, v_a_3094_, v_a_3095_);
    crate::leanh::lean_dec(v_a_3095_);
    crate::leanh::lean_dec_ref(v_a_3094_);
    crate::leanh::lean_dec(v_a_3093_);
    crate::leanh::lean_dec_ref(v_a_3092_);
    return v_res_3097_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3(
    mut v_00_u03b1_3098_: *mut crate::leanh::LeanObject,
    mut v_msg_3099_: *mut crate::leanh::LeanObject,
    mut v___y_3100_: *mut crate::leanh::LeanObject,
    mut v___y_3101_: *mut crate::leanh::LeanObject,
    mut v___y_3102_: *mut crate::leanh::LeanObject,
    mut v___y_3103_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3105_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(
        v_msg_3099_,
        v___y_3100_,
        v___y_3101_,
        v___y_3102_,
        v___y_3103_,
    );
    return v___x_3105_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___boxed(
    mut v_00_u03b1_3106_: *mut crate::leanh::LeanObject,
    mut v_msg_3107_: *mut crate::leanh::LeanObject,
    mut v___y_3108_: *mut crate::leanh::LeanObject,
    mut v___y_3109_: *mut crate::leanh::LeanObject,
    mut v___y_3110_: *mut crate::leanh::LeanObject,
    mut v___y_3111_: *mut crate::leanh::LeanObject,
    mut v___y_3112_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3113_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3(
        v_00_u03b1_3106_,
        v_msg_3107_,
        v___y_3108_,
        v___y_3109_,
        v___y_3110_,
        v___y_3111_,
    );
    crate::leanh::lean_dec(v___y_3111_);
    crate::leanh::lean_dec_ref(v___y_3110_);
    crate::leanh::lean_dec(v___y_3109_);
    crate::leanh::lean_dec_ref(v___y_3108_);
    return v_res_3113_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__11(
    mut v_00_u03b1_3114_: *mut crate::leanh::LeanObject,
    mut v_x_3115_: *mut crate::leanh::LeanObject,
    mut v___y_3116_: *mut crate::leanh::LeanObject,
    mut v___y_3117_: *mut crate::leanh::LeanObject,
    mut v___y_3118_: *mut crate::leanh::LeanObject,
    mut v___y_3119_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3121_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__11___redArg(v_x_3115_);
    return v___x_3121_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__11___boxed(
    mut v_00_u03b1_3122_: *mut crate::leanh::LeanObject,
    mut v_x_3123_: *mut crate::leanh::LeanObject,
    mut v___y_3124_: *mut crate::leanh::LeanObject,
    mut v___y_3125_: *mut crate::leanh::LeanObject,
    mut v___y_3126_: *mut crate::leanh::LeanObject,
    mut v___y_3127_: *mut crate::leanh::LeanObject,
    mut v___y_3128_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3129_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__11(v_00_u03b1_3122_, v_x_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_);
    crate::leanh::lean_dec(v___y_3127_);
    crate::leanh::lean_dec_ref(v___y_3126_);
    crate::leanh::lean_dec(v___y_3125_);
    crate::leanh::lean_dec_ref(v___y_3124_);
    return v_res_3129_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___redArg(
    mut v_mvarId_3130_: *mut crate::leanh::LeanObject,
    mut v_x_3131_: *mut crate::leanh::LeanObject,
    mut v___y_3132_: *mut crate::leanh::LeanObject,
    mut v___y_3133_: *mut crate::leanh::LeanObject,
    mut v___y_3134_: *mut crate::leanh::LeanObject,
    mut v___y_3135_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3141_: u8 = 0;
    let mut v___x_3143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3145_: u8 = 0;
    let mut v_a_3146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3149_: u8 = 0;
    let mut v___x_3151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3153_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3137_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    crate::leanh::lean_box(0),
                    v_mvarId_3130_,
                    v_x_3131_,
                    v___y_3132_,
                    v___y_3133_,
                    v___y_3134_,
                    v___y_3135_,
                );
                if crate::leanh::lean_obj_tag(v___x_3137_) == 0 {
                    v_a_3138_ = crate::leanh::lean_ctor_get(v___x_3137_, 0);
                    v_isSharedCheck_3145_ = (!crate::leanh::lean_is_exclusive(v___x_3137_)) as u8;
                    if v_isSharedCheck_3145_ == 0 {
                        v___x_3140_ = v___x_3137_;
                        v_isShared_3141_ = v_isSharedCheck_3145_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3138_);
                        crate::leanh::lean_dec(v___x_3137_);
                        v___x_3140_ = crate::leanh::lean_box(0);
                        v_isShared_3141_ = v_isSharedCheck_3145_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3146_ = crate::leanh::lean_ctor_get(v___x_3137_, 0);
                    v_isSharedCheck_3153_ = (!crate::leanh::lean_is_exclusive(v___x_3137_)) as u8;
                    if v_isSharedCheck_3153_ == 0 {
                        v___x_3148_ = v___x_3137_;
                        v_isShared_3149_ = v_isSharedCheck_3153_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3146_);
                        crate::leanh::lean_dec(v___x_3137_);
                        v___x_3148_ = crate::leanh::lean_box(0);
                        v_isShared_3149_ = v_isSharedCheck_3153_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3141_ == 0 {
                    v___x_3143_ = v___x_3140_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3144_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3144_, 0, v_a_3138_);
                    v___x_3143_ = v_reuseFailAlloc_3144_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3143_;
            }
            3 => {
                if v_isShared_3149_ == 0 {
                    v___x_3151_ = v___x_3148_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3152_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3152_, 0, v_a_3146_);
                    v___x_3151_ = v_reuseFailAlloc_3152_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3151_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___redArg___boxed(
    mut v_mvarId_3154_: *mut crate::leanh::LeanObject,
    mut v_x_3155_: *mut crate::leanh::LeanObject,
    mut v___y_3156_: *mut crate::leanh::LeanObject,
    mut v___y_3157_: *mut crate::leanh::LeanObject,
    mut v___y_3158_: *mut crate::leanh::LeanObject,
    mut v___y_3159_: *mut crate::leanh::LeanObject,
    mut v___y_3160_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3161_ = l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___redArg(
        v_mvarId_3154_,
        v_x_3155_,
        v___y_3156_,
        v___y_3157_,
        v___y_3158_,
        v___y_3159_,
    );
    crate::leanh::lean_dec(v___y_3159_);
    crate::leanh::lean_dec_ref(v___y_3158_);
    crate::leanh::lean_dec(v___y_3157_);
    crate::leanh::lean_dec_ref(v___y_3156_);
    return v_res_3161_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2(
    mut v_00_u03b1_3162_: *mut crate::leanh::LeanObject,
    mut v_mvarId_3163_: *mut crate::leanh::LeanObject,
    mut v_x_3164_: *mut crate::leanh::LeanObject,
    mut v___y_3165_: *mut crate::leanh::LeanObject,
    mut v___y_3166_: *mut crate::leanh::LeanObject,
    mut v___y_3167_: *mut crate::leanh::LeanObject,
    mut v___y_3168_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3170_ = l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___redArg(
        v_mvarId_3163_,
        v_x_3164_,
        v___y_3165_,
        v___y_3166_,
        v___y_3167_,
        v___y_3168_,
    );
    return v___x_3170_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___boxed(
    mut v_00_u03b1_3171_: *mut crate::leanh::LeanObject,
    mut v_mvarId_3172_: *mut crate::leanh::LeanObject,
    mut v_x_3173_: *mut crate::leanh::LeanObject,
    mut v___y_3174_: *mut crate::leanh::LeanObject,
    mut v___y_3175_: *mut crate::leanh::LeanObject,
    mut v___y_3176_: *mut crate::leanh::LeanObject,
    mut v___y_3177_: *mut crate::leanh::LeanObject,
    mut v___y_3178_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3179_ = l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2(
        v_00_u03b1_3171_,
        v_mvarId_3172_,
        v_x_3173_,
        v___y_3174_,
        v___y_3175_,
        v___y_3176_,
        v___y_3177_,
    );
    crate::leanh::lean_dec(v___y_3177_);
    crate::leanh::lean_dec_ref(v___y_3176_);
    crate::leanh::lean_dec(v___y_3175_);
    crate::leanh::lean_dec_ref(v___y_3174_);
    return v_res_3179_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_splitSparseCasesOn_spec__1(
    mut v_a_3180_: *mut crate::leanh::LeanObject,
    mut v_a_3181_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3187_: u8 = 0;
    let mut v___x_3188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3193_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_3180_) == 0 {
                    v___x_3182_ = l_List_reverse___redArg(v_a_3181_);
                    return v___x_3182_;
                } else {
                    v_head_3183_ = crate::leanh::lean_ctor_get(v_a_3180_, 0);
                    v_tail_3184_ = crate::leanh::lean_ctor_get(v_a_3180_, 1);
                    v_isSharedCheck_3193_ = (!crate::leanh::lean_is_exclusive(v_a_3180_)) as u8;
                    if v_isSharedCheck_3193_ == 0 {
                        v___x_3186_ = v_a_3180_;
                        v_isShared_3187_ = v_isSharedCheck_3193_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3184_);
                        crate::leanh::lean_inc(v_head_3183_);
                        crate::leanh::lean_dec(v_a_3180_);
                        v___x_3186_ = crate::leanh::lean_box(0);
                        v_isShared_3187_ = v_isSharedCheck_3193_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3188_ = l_Lean_MessageData_ofExpr(v_head_3183_);
                if v_isShared_3187_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3186_, 1, v_a_3181_);
                    crate::leanh::lean_ctor_set(v___x_3186_, 0, v___x_3188_);
                    v___x_3190_ = v___x_3186_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3192_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3192_, 0, v___x_3188_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3192_, 1, v_a_3181_);
                    v___x_3190_ = v_reuseFailAlloc_3192_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_3180_ = v_tail_3184_;
                v_a_3181_ = v___x_3190_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3195_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___closed__0;
    v___x_3196_ = l_Lean_stringToMessageData(v___x_3195_);
    return v___x_3196_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0(
    mut v___y_3197_: u8,
    mut v_mvarId_3198_: *mut crate::leanh::LeanObject,
    mut v___f_3199_: *mut crate::leanh::LeanObject,
    mut v_declName_3200_: *mut crate::leanh::LeanObject,
    mut v_val_3201_: *mut crate::leanh::LeanObject,
    mut v___x_3202_: *mut crate::leanh::LeanObject,
    mut v_fields_3203_: *mut crate::leanh::LeanObject,
    mut v___x_3204_: u8,
    mut v___y_3205_: *mut crate::leanh::LeanObject,
    mut v___y_3206_: *mut crate::leanh::LeanObject,
    mut v___y_3207_: *mut crate::leanh::LeanObject,
    mut v___y_3208_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arity_3223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_3225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_3228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3245_: u8 = 0;
    let mut v___x_3247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3249_: u8 = 0;
    let mut v_a_3250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3253_: u8 = 0;
    let mut v___x_3255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3257_: u8 = 0;
    let mut v_a_3258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3261_: u8 = 0;
    let mut v___x_3263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3265_: u8 = 0;
    let mut v___x_3266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: u8 = 0;
    let mut v___x_3270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3280_: u8 = 0;
    let mut v___x_3282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3284_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v___y_3197_ == 0 {
                    crate::leanh::lean_dec_ref(v_fields_3203_);
                    crate::leanh::lean_dec_ref(v_val_3201_);
                    crate::leanh::lean_dec(v_declName_3200_);
                    v___x_3266_ = l_Lean_MVarId_modifyTargetEqLHS(
                        v_mvarId_3198_,
                        v___f_3199_,
                        v___y_3205_,
                        v___y_3206_,
                        v___y_3207_,
                        v___y_3208_,
                    );
                    return v___x_3266_;
                } else {
                    crate::leanh::lean_dec_ref(v___f_3199_);
                    v___x_3267_ = lean_array_get_size(v_fields_3203_);
                    v___x_3268_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3269_ = lean_nat_dec_eq(v___x_3267_, v___x_3268_);
                    if v___x_3269_ == 0 {
                        v___x_3270_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___closed__1);
                        crate::leanh::lean_inc_ref(v_fields_3203_);
                        v___x_3271_ = lean_array_to_list(v_fields_3203_);
                        v___x_3272_ = crate::leanh::lean_box(0);
                        v___x_3273_ =
                            l_List_mapTR_loop___at___00Lean_Meta_splitSparseCasesOn_spec__1(
                                v___x_3271_,
                                v___x_3272_,
                            );
                        v___x_3274_ = l_Lean_MessageData_ofList(v___x_3273_);
                        v___x_3275_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3275_, 0, v___x_3270_);
                        crate::leanh::lean_ctor_set(v___x_3275_, 1, v___x_3274_);
                        v___x_3276_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_3275_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_);
                        if crate::leanh::lean_obj_tag(v___x_3276_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_3276_, 1);
                            v___y_3211_ = v___y_3205_;
                            v___y_3212_ = v___y_3206_;
                            v___y_3213_ = v___y_3207_;
                            v___y_3214_ = v___y_3208_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_fields_3203_);
                            crate::leanh::lean_dec_ref(v_val_3201_);
                            crate::leanh::lean_dec(v_declName_3200_);
                            crate::leanh::lean_dec(v_mvarId_3198_);
                            v_a_3277_ = crate::leanh::lean_ctor_get(v___x_3276_, 0);
                            v_isSharedCheck_3284_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3276_)) as u8;
                            if v_isSharedCheck_3284_ == 0 {
                                v___x_3279_ = v___x_3276_;
                                v_isShared_3280_ = v_isSharedCheck_3284_;
                                state = 8;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3277_);
                                crate::leanh::lean_dec(v___x_3276_);
                                v___x_3279_ = crate::leanh::lean_box(0);
                                v_isShared_3280_ = v_isSharedCheck_3284_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        v___y_3211_ = v___y_3205_;
                        v___y_3212_ = v___y_3206_;
                        v___y_3213_ = v___y_3207_;
                        v___y_3214_ = v___y_3208_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3215_ = l_Lean_Meta_getSparseCasesOnEq(
                    v_declName_3200_,
                    v___y_3211_,
                    v___y_3212_,
                    v___y_3213_,
                    v___y_3214_,
                );
                if crate::leanh::lean_obj_tag(v___x_3215_) == 0 {
                    v_a_3216_ = crate::leanh::lean_ctor_get(v___x_3215_, 0);
                    crate::leanh::lean_inc(v_a_3216_);
                    crate::leanh::lean_dec_ref_known(v___x_3215_, 1);
                    crate::leanh::lean_inc(v_mvarId_3198_);
                    v___x_3217_ = l_Lean_MVarId_getType(
                        v_mvarId_3198_,
                        v___y_3211_,
                        v___y_3212_,
                        v___y_3213_,
                        v___y_3214_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3217_) == 0 {
                        v_a_3218_ = crate::leanh::lean_ctor_get(v___x_3217_, 0);
                        crate::leanh::lean_inc(v_a_3218_);
                        crate::leanh::lean_dec_ref_known(v___x_3217_, 1);
                        v___x_3219_ = l_Lean_Meta_matchEqHEqLHS_x3f(
                            v_a_3218_,
                            v___y_3211_,
                            v___y_3212_,
                            v___y_3213_,
                            v___y_3214_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3219_) == 0 {
                            v_a_3220_ = crate::leanh::lean_ctor_get(v___x_3219_, 0);
                            crate::leanh::lean_inc(v_a_3220_);
                            crate::leanh::lean_dec_ref_known(v___x_3219_, 1);
                            if crate::leanh::lean_obj_tag(v_a_3220_) == 1 {
                                v_val_3221_ = crate::leanh::lean_ctor_get(v_a_3220_, 0);
                                crate::leanh::lean_inc(v_val_3221_);
                                crate::leanh::lean_dec_ref_known(v_a_3220_, 1);
                                v_snd_3222_ = crate::leanh::lean_ctor_get(v_val_3221_, 1);
                                crate::leanh::lean_inc(v_snd_3222_);
                                crate::leanh::lean_dec(v_val_3221_);
                                v_arity_3223_ = crate::leanh::lean_ctor_get(v_val_3201_, 2);
                                crate::leanh::lean_inc(v_arity_3223_);
                                crate::leanh::lean_dec_ref(v_val_3201_);
                                v___x_3224_ = l_Lean_Expr_getAppFn(v_snd_3222_);
                                v_nargs_3225_ = l_Lean_Expr_getAppNumArgs(v_snd_3222_);
                                v___x_3226_ = l_Lean_Expr_constLevels_x21(v___x_3224_);
                                crate::leanh::lean_dec_ref(v___x_3224_);
                                v___x_3227_ = l_Lean_mkConst(v_a_3216_, v___x_3226_);
                                v_dummy_3228_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0), core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0_once), _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0);
                                crate::leanh::lean_inc(v_nargs_3225_);
                                v___x_3229_ = lean_mk_array(v_nargs_3225_, v_dummy_3228_);
                                v___x_3230_ = crate::leanh::lean_unsigned_to_nat(1);
                                v___x_3231_ = lean_nat_sub(v_nargs_3225_, v___x_3230_);
                                crate::leanh::lean_dec(v_nargs_3225_);
                                v___x_3232_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                                    v_snd_3222_,
                                    v___x_3229_,
                                    v___x_3231_,
                                );
                                v___x_3233_ = crate::leanh::lean_unsigned_to_nat(0);
                                v___x_3234_ = l_Array_toSubarray___redArg(
                                    v___x_3232_,
                                    v___x_3233_,
                                    v_arity_3223_,
                                );
                                v___x_3235_ = l_Subarray_copy___redArg(v___x_3234_);
                                v___x_3236_ = l_Lean_mkAppN(v___x_3227_, v___x_3235_);
                                crate::leanh::lean_dec_ref(v___x_3235_);
                                v___x_3237_ =
                                    lean_array_get(v___x_3202_, v_fields_3203_, v___x_3233_);
                                crate::leanh::lean_dec_ref(v_fields_3203_);
                                v___x_3238_ = l_Lean_Expr_app___override(v___x_3236_, v___x_3237_);
                                v___x_3239_ = l___private_Lean_Meta_SplitSparseCasesOn_0__Lean_Meta_rewriteGoalUsingEq(v_mvarId_3198_, v___x_3238_, v___x_3204_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_);
                                return v___x_3239_;
                            } else {
                                crate::leanh::lean_dec(v_a_3220_);
                                crate::leanh::lean_dec(v_a_3216_);
                                crate::leanh::lean_dec_ref(v_fields_3203_);
                                crate::leanh::lean_dec_ref(v_val_3201_);
                                crate::leanh::lean_dec(v_mvarId_3198_);
                                v___x_3240_ = crate::leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_reduceSparseCasesOn___closed__1
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_reduceSparseCasesOn___closed__1_once
                                    ),
                                    _init_l_Lean_Meta_reduceSparseCasesOn___closed__1,
                                );
                                v___x_3241_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_3240_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_);
                                return v___x_3241_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3216_);
                            crate::leanh::lean_dec_ref(v_fields_3203_);
                            crate::leanh::lean_dec_ref(v_val_3201_);
                            crate::leanh::lean_dec(v_mvarId_3198_);
                            v_a_3242_ = crate::leanh::lean_ctor_get(v___x_3219_, 0);
                            v_isSharedCheck_3249_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3219_)) as u8;
                            if v_isSharedCheck_3249_ == 0 {
                                v___x_3244_ = v___x_3219_;
                                v_isShared_3245_ = v_isSharedCheck_3249_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3242_);
                                crate::leanh::lean_dec(v___x_3219_);
                                v___x_3244_ = crate::leanh::lean_box(0);
                                v_isShared_3245_ = v_isSharedCheck_3249_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3216_);
                        crate::leanh::lean_dec_ref(v_fields_3203_);
                        crate::leanh::lean_dec_ref(v_val_3201_);
                        crate::leanh::lean_dec(v_mvarId_3198_);
                        v_a_3250_ = crate::leanh::lean_ctor_get(v___x_3217_, 0);
                        v_isSharedCheck_3257_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3217_)) as u8;
                        if v_isSharedCheck_3257_ == 0 {
                            v___x_3252_ = v___x_3217_;
                            v_isShared_3253_ = v_isSharedCheck_3257_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3250_);
                            crate::leanh::lean_dec(v___x_3217_);
                            v___x_3252_ = crate::leanh::lean_box(0);
                            v_isShared_3253_ = v_isSharedCheck_3257_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_fields_3203_);
                    crate::leanh::lean_dec_ref(v_val_3201_);
                    crate::leanh::lean_dec(v_mvarId_3198_);
                    v_a_3258_ = crate::leanh::lean_ctor_get(v___x_3215_, 0);
                    v_isSharedCheck_3265_ = (!crate::leanh::lean_is_exclusive(v___x_3215_)) as u8;
                    if v_isSharedCheck_3265_ == 0 {
                        v___x_3260_ = v___x_3215_;
                        v_isShared_3261_ = v_isSharedCheck_3265_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3258_);
                        crate::leanh::lean_dec(v___x_3215_);
                        v___x_3260_ = crate::leanh::lean_box(0);
                        v_isShared_3261_ = v_isSharedCheck_3265_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3245_ == 0 {
                    v___x_3247_ = v___x_3244_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3248_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3248_, 0, v_a_3242_);
                    v___x_3247_ = v_reuseFailAlloc_3248_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3247_;
            }
            4 => {
                if v_isShared_3253_ == 0 {
                    v___x_3255_ = v___x_3252_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3256_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3256_, 0, v_a_3250_);
                    v___x_3255_ = v_reuseFailAlloc_3256_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3255_;
            }
            6 => {
                if v_isShared_3261_ == 0 {
                    v___x_3263_ = v___x_3260_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3264_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3264_, 0, v_a_3258_);
                    v___x_3263_ = v_reuseFailAlloc_3264_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3263_;
            }
            8 => {
                if v_isShared_3280_ == 0 {
                    v___x_3282_ = v___x_3279_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3283_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3283_, 0, v_a_3277_);
                    v___x_3282_ = v_reuseFailAlloc_3283_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3282_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___boxed(
    mut v___y_3285_: *mut crate::leanh::LeanObject,
    mut v_mvarId_3286_: *mut crate::leanh::LeanObject,
    mut v___f_3287_: *mut crate::leanh::LeanObject,
    mut v_declName_3288_: *mut crate::leanh::LeanObject,
    mut v_val_3289_: *mut crate::leanh::LeanObject,
    mut v___x_3290_: *mut crate::leanh::LeanObject,
    mut v_fields_3291_: *mut crate::leanh::LeanObject,
    mut v___x_3292_: *mut crate::leanh::LeanObject,
    mut v___y_3293_: *mut crate::leanh::LeanObject,
    mut v___y_3294_: *mut crate::leanh::LeanObject,
    mut v___y_3295_: *mut crate::leanh::LeanObject,
    mut v___y_3296_: *mut crate::leanh::LeanObject,
    mut v___y_3297_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_33602__boxed_3298_: u8 = 0;
    let mut v___x_33607__boxed_3299_: u8 = 0;
    let mut v_res_3300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_33602__boxed_3298_ = (crate::leanh::lean_unbox(v___y_3285_) as u8);
    v___x_33607__boxed_3299_ = (crate::leanh::lean_unbox(v___x_3292_) as u8);
    v_res_3300_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0(v___y_33602__boxed_3298_, v_mvarId_3286_, v___f_3287_, v_declName_3288_, v_val_3289_, v___x_3290_, v_fields_3291_, v___x_33607__boxed_3299_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_);
    crate::leanh::lean_dec(v___y_3296_);
    crate::leanh::lean_dec_ref(v___y_3295_);
    crate::leanh::lean_dec(v___y_3294_);
    crate::leanh::lean_dec_ref(v___y_3293_);
    crate::leanh::lean_dec_ref(v___x_3290_);
    return v_res_3300_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3(
    mut v_declName_3301_: *mut crate::leanh::LeanObject,
    mut v_val_3302_: *mut crate::leanh::LeanObject,
    mut v___x_3303_: u8,
    mut v_sz_3304_: usize,
    mut v_i_3305_: usize,
    mut v_bs_3306_: *mut crate::leanh::LeanObject,
    mut v___y_3307_: *mut crate::leanh::LeanObject,
    mut v___y_3308_: *mut crate::leanh::LeanObject,
    mut v___y_3309_: *mut crate::leanh::LeanObject,
    mut v___y_3310_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3312_: u8 = 0;
    let mut v___x_3313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toInductionSubgoal_3315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctorName_3316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_3317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fields_3318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3324_: u8 = 0;
    let mut v___x_3325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3330_: usize = 0;
    let mut v___x_3331_: usize = 0;
    let mut v___x_3332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3337_: u8 = 0;
    let mut v___x_3339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3341_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3312_ = lean_usize_dec_lt(v_i_3305_, v_sz_3304_);
                if v___x_3312_ == 0 {
                    crate::leanh::lean_dec_ref(v_val_3302_);
                    crate::leanh::lean_dec(v_declName_3301_);
                    v___x_3313_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3313_, 0, v_bs_3306_);
                    return v___x_3313_;
                } else {
                    v_v_3314_ = lean_array_uget_borrowed(v_bs_3306_, v_i_3305_);
                    v_toInductionSubgoal_3315_ = crate::leanh::lean_ctor_get(v_v_3314_, 0);
                    v_ctorName_3316_ = crate::leanh::lean_ctor_get(v_v_3314_, 1);
                    crate::leanh::lean_inc(v_ctorName_3316_);
                    v_mvarId_3317_ = crate::leanh::lean_ctor_get(v_toInductionSubgoal_3315_, 0);
                    crate::leanh::lean_inc(v_mvarId_3317_);
                    v_fields_3318_ = crate::leanh::lean_ctor_get(v_toInductionSubgoal_3315_, 1);
                    crate::leanh::lean_inc_ref(v_fields_3318_);
                    v___f_3319_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__0;
                    v___x_3320_ = l_Lean_instInhabitedExpr;
                    v___x_3321_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_3322_ = lean_array_uset(v_bs_3306_, v_i_3305_, v___x_3321_);
                    if crate::leanh::lean_obj_tag(v_ctorName_3316_) == 0 {
                        v___y_3324_ = v___x_3312_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref_known(v_ctorName_3316_, 1);
                        if v___x_3303_ == 0 {
                            v___y_3324_ = v___x_3303_;
                            state = 1;
                            continue;
                        } else {
                            v___y_3324_ = v___x_3312_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3325_ = crate::leanh::lean_box((v___y_3324_) as usize);
                v___x_3326_ = crate::leanh::lean_box((v___x_3303_) as usize);
                crate::leanh::lean_inc_ref(v_val_3302_);
                crate::leanh::lean_inc(v_declName_3301_);
                crate::leanh::lean_inc(v_mvarId_3317_);
                v___y_3327_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___boxed as *mut core::ffi::c_void, 13, 8);
                crate::leanh::lean_closure_set(v___y_3327_, 0, v___x_3325_);
                crate::leanh::lean_closure_set(v___y_3327_, 1, v_mvarId_3317_);
                crate::leanh::lean_closure_set(v___y_3327_, 2, v___f_3319_);
                crate::leanh::lean_closure_set(v___y_3327_, 3, v_declName_3301_);
                crate::leanh::lean_closure_set(v___y_3327_, 4, v_val_3302_);
                crate::leanh::lean_closure_set(v___y_3327_, 5, v___x_3320_);
                crate::leanh::lean_closure_set(v___y_3327_, 6, v_fields_3318_);
                crate::leanh::lean_closure_set(v___y_3327_, 7, v___x_3326_);
                v___x_3328_ = l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___redArg(v_mvarId_3317_, v___y_3327_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3310_);
                if crate::leanh::lean_obj_tag(v___x_3328_) == 0 {
                    v_a_3329_ = crate::leanh::lean_ctor_get(v___x_3328_, 0);
                    crate::leanh::lean_inc(v_a_3329_);
                    crate::leanh::lean_dec_ref_known(v___x_3328_, 1);
                    v___x_3330_ = 1usize;
                    v___x_3331_ = lean_usize_add(v_i_3305_, v___x_3330_);
                    v___x_3332_ = lean_array_uset(v_bs_x27_3322_, v_i_3305_, v_a_3329_);
                    v_i_3305_ = v___x_3331_;
                    v_bs_3306_ = v___x_3332_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_bs_x27_3322_);
                    crate::leanh::lean_dec_ref(v_val_3302_);
                    crate::leanh::lean_dec(v_declName_3301_);
                    v_a_3334_ = crate::leanh::lean_ctor_get(v___x_3328_, 0);
                    v_isSharedCheck_3341_ = (!crate::leanh::lean_is_exclusive(v___x_3328_)) as u8;
                    if v_isSharedCheck_3341_ == 0 {
                        v___x_3336_ = v___x_3328_;
                        v_isShared_3337_ = v_isSharedCheck_3341_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3334_);
                        crate::leanh::lean_dec(v___x_3328_);
                        v___x_3336_ = crate::leanh::lean_box(0);
                        v_isShared_3337_ = v_isSharedCheck_3341_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3337_ == 0 {
                    v___x_3339_ = v___x_3336_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3340_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3340_, 0, v_a_3334_);
                    v___x_3339_ = v_reuseFailAlloc_3340_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3339_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___boxed(
    mut v_declName_3342_: *mut crate::leanh::LeanObject,
    mut v_val_3343_: *mut crate::leanh::LeanObject,
    mut v___x_3344_: *mut crate::leanh::LeanObject,
    mut v_sz_3345_: *mut crate::leanh::LeanObject,
    mut v_i_3346_: *mut crate::leanh::LeanObject,
    mut v_bs_3347_: *mut crate::leanh::LeanObject,
    mut v___y_3348_: *mut crate::leanh::LeanObject,
    mut v___y_3349_: *mut crate::leanh::LeanObject,
    mut v___y_3350_: *mut crate::leanh::LeanObject,
    mut v___y_3351_: *mut crate::leanh::LeanObject,
    mut v___y_3352_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_33786__boxed_3353_: u8 = 0;
    let mut v_sz_boxed_3354_: usize = 0;
    let mut v_i_boxed_3355_: usize = 0;
    let mut v_res_3356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_33786__boxed_3353_ = (crate::leanh::lean_unbox(v___x_3344_) as u8);
    v_sz_boxed_3354_ = crate::leanh::lean_unbox_usize(v_sz_3345_);
    crate::leanh::lean_dec(v_sz_3345_);
    v_i_boxed_3355_ = crate::leanh::lean_unbox_usize(v_i_3346_);
    crate::leanh::lean_dec(v_i_3346_);
    v_res_3356_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3(v_declName_3342_, v_val_3343_, v___x_33786__boxed_3353_, v_sz_boxed_3354_, v_i_boxed_3355_, v_bs_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_);
    crate::leanh::lean_dec(v___y_3351_);
    crate::leanh::lean_dec_ref(v___y_3350_);
    crate::leanh::lean_dec(v___y_3349_);
    crate::leanh::lean_dec_ref(v___y_3348_);
    return v_res_3356_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__4(
    mut v_declName_3357_: *mut crate::leanh::LeanObject,
    mut v_val_3358_: *mut crate::leanh::LeanObject,
    mut v___x_3359_: u8,
    mut v_sz_3360_: usize,
    mut v_i_3361_: usize,
    mut v_bs_3362_: *mut crate::leanh::LeanObject,
    mut v___y_3363_: *mut crate::leanh::LeanObject,
    mut v___y_3364_: *mut crate::leanh::LeanObject,
    mut v___y_3365_: *mut crate::leanh::LeanObject,
    mut v___y_3366_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3368_: u8 = 0;
    let mut v___x_3369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toInductionSubgoal_3371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctorName_3372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fields_3374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: u8 = 0;
    let mut v___x_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3381_: u8 = 0;
    let mut v___x_3382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3387_: usize = 0;
    let mut v___x_3388_: usize = 0;
    let mut v___x_3389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3394_: u8 = 0;
    let mut v___x_3396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3398_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3368_ = lean_usize_dec_lt(v_i_3361_, v_sz_3360_);
                if v___x_3368_ == 0 {
                    crate::leanh::lean_dec_ref(v_val_3358_);
                    crate::leanh::lean_dec(v_declName_3357_);
                    v___x_3369_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3369_, 0, v_bs_3362_);
                    return v___x_3369_;
                } else {
                    v_v_3370_ = lean_array_uget_borrowed(v_bs_3362_, v_i_3361_);
                    v_toInductionSubgoal_3371_ = crate::leanh::lean_ctor_get(v_v_3370_, 0);
                    v_ctorName_3372_ = crate::leanh::lean_ctor_get(v_v_3370_, 1);
                    crate::leanh::lean_inc(v_ctorName_3372_);
                    v_mvarId_3373_ = crate::leanh::lean_ctor_get(v_toInductionSubgoal_3371_, 0);
                    crate::leanh::lean_inc(v_mvarId_3373_);
                    v_fields_3374_ = crate::leanh::lean_ctor_get(v_toInductionSubgoal_3371_, 1);
                    crate::leanh::lean_inc_ref(v_fields_3374_);
                    v___f_3375_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__0;
                    v___x_3376_ = l_Lean_instInhabitedExpr;
                    v___x_3377_ = 0;
                    v___x_3378_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_3379_ = lean_array_uset(v_bs_3362_, v_i_3361_, v___x_3378_);
                    if crate::leanh::lean_obj_tag(v_ctorName_3372_) == 0 {
                        if v___x_3359_ == 0 {
                            state = 4;
                            continue;
                        } else {
                            v___y_3381_ = v___x_3359_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_ctorName_3372_, 1);
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3382_ = crate::leanh::lean_box((v___y_3381_) as usize);
                v___x_3383_ = crate::leanh::lean_box((v___x_3377_) as usize);
                crate::leanh::lean_inc_ref(v_val_3358_);
                crate::leanh::lean_inc(v_declName_3357_);
                crate::leanh::lean_inc(v_mvarId_3373_);
                v___y_3384_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___boxed as *mut core::ffi::c_void, 13, 8);
                crate::leanh::lean_closure_set(v___y_3384_, 0, v___x_3382_);
                crate::leanh::lean_closure_set(v___y_3384_, 1, v_mvarId_3373_);
                crate::leanh::lean_closure_set(v___y_3384_, 2, v___f_3375_);
                crate::leanh::lean_closure_set(v___y_3384_, 3, v_declName_3357_);
                crate::leanh::lean_closure_set(v___y_3384_, 4, v_val_3358_);
                crate::leanh::lean_closure_set(v___y_3384_, 5, v___x_3376_);
                crate::leanh::lean_closure_set(v___y_3384_, 6, v_fields_3374_);
                crate::leanh::lean_closure_set(v___y_3384_, 7, v___x_3383_);
                v___x_3385_ = l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___redArg(v_mvarId_3373_, v___y_3384_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_);
                if crate::leanh::lean_obj_tag(v___x_3385_) == 0 {
                    v_a_3386_ = crate::leanh::lean_ctor_get(v___x_3385_, 0);
                    crate::leanh::lean_inc(v_a_3386_);
                    crate::leanh::lean_dec_ref_known(v___x_3385_, 1);
                    v___x_3387_ = 1usize;
                    v___x_3388_ = lean_usize_add(v_i_3361_, v___x_3387_);
                    v___x_3389_ = lean_array_uset(v_bs_x27_3379_, v_i_3361_, v_a_3386_);
                    v_i_3361_ = v___x_3388_;
                    v_bs_3362_ = v___x_3389_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_bs_x27_3379_);
                    crate::leanh::lean_dec_ref(v_val_3358_);
                    crate::leanh::lean_dec(v_declName_3357_);
                    v_a_3391_ = crate::leanh::lean_ctor_get(v___x_3385_, 0);
                    v_isSharedCheck_3398_ = (!crate::leanh::lean_is_exclusive(v___x_3385_)) as u8;
                    if v_isSharedCheck_3398_ == 0 {
                        v___x_3393_ = v___x_3385_;
                        v_isShared_3394_ = v_isSharedCheck_3398_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3391_);
                        crate::leanh::lean_dec(v___x_3385_);
                        v___x_3393_ = crate::leanh::lean_box(0);
                        v_isShared_3394_ = v_isSharedCheck_3398_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3394_ == 0 {
                    v___x_3396_ = v___x_3393_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3397_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3397_, 0, v_a_3391_);
                    v___x_3396_ = v_reuseFailAlloc_3397_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3396_;
            }
            4 => {
                v___y_3381_ = v___x_3377_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__4___boxed(
    mut v_declName_3400_: *mut crate::leanh::LeanObject,
    mut v_val_3401_: *mut crate::leanh::LeanObject,
    mut v___x_3402_: *mut crate::leanh::LeanObject,
    mut v_sz_3403_: *mut crate::leanh::LeanObject,
    mut v_i_3404_: *mut crate::leanh::LeanObject,
    mut v_bs_3405_: *mut crate::leanh::LeanObject,
    mut v___y_3406_: *mut crate::leanh::LeanObject,
    mut v___y_3407_: *mut crate::leanh::LeanObject,
    mut v___y_3408_: *mut crate::leanh::LeanObject,
    mut v___y_3409_: *mut crate::leanh::LeanObject,
    mut v___y_3410_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_33859__boxed_3411_: u8 = 0;
    let mut v_sz_boxed_3412_: usize = 0;
    let mut v_i_boxed_3413_: usize = 0;
    let mut v_res_3414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_33859__boxed_3411_ = (crate::leanh::lean_unbox(v___x_3402_) as u8);
    v_sz_boxed_3412_ = crate::leanh::lean_unbox_usize(v_sz_3403_);
    crate::leanh::lean_dec(v_sz_3403_);
    v_i_boxed_3413_ = crate::leanh::lean_unbox_usize(v_i_3404_);
    crate::leanh::lean_dec(v_i_3404_);
    v_res_3414_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__4(v_declName_3400_, v_val_3401_, v___x_33859__boxed_3411_, v_sz_boxed_3412_, v_i_boxed_3413_, v_bs_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_);
    crate::leanh::lean_dec(v___y_3409_);
    crate::leanh::lean_dec_ref(v___y_3408_);
    crate::leanh::lean_dec(v___y_3407_);
    crate::leanh::lean_dec_ref(v___y_3406_);
    return v_res_3414_;
}
pub unsafe fn _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3418_ =
        l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__1;
    v___x_3419_ = l_Lean_stringToMessageData(v___x_3418_);
    return v___x_3419_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1(
    mut v_val_3420_: *mut crate::leanh::LeanObject,
    mut v___x_3421_: *mut crate::leanh::LeanObject,
    mut v_x_3422_: *mut crate::leanh::LeanObject,
    mut v_mvarId_3423_: *mut crate::leanh::LeanObject,
    mut v_declName_3424_: *mut crate::leanh::LeanObject,
    mut v___x_3425_: u8,
    mut v_____r_3426_: *mut crate::leanh::LeanObject,
    mut v___y_3427_: *mut crate::leanh::LeanObject,
    mut v___y_3428_: *mut crate::leanh::LeanObject,
    mut v___y_3429_: *mut crate::leanh::LeanObject,
    mut v___y_3430_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: u8 = 0;
    let mut v___x_3443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3446_: usize = 0;
    let mut v___x_3447_: usize = 0;
    let mut v___x_3448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3452_: u8 = 0;
    let mut v___x_3454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3456_: u8 = 0;
    let mut v_majorPos_3457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arity_3458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_insterestingCtors_3459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3466_: u8 = 0;
    let mut v___x_3467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3474_: u8 = 0;
    let mut v___x_3476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3478_: u8 = 0;
    let mut v___x_3479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: u8 = 0;
    let mut v___x_3481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3486_: u8 = 0;
    let mut v___x_3488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3490_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_majorPos_3457_ = crate::leanh::lean_ctor_get(v_val_3420_, 1);
                v_arity_3458_ = crate::leanh::lean_ctor_get(v_val_3420_, 2);
                v_insterestingCtors_3459_ = crate::leanh::lean_ctor_get(v_val_3420_, 3);
                v___x_3479_ = lean_array_get_size(v_x_3422_);
                v___x_3480_ = lean_nat_dec_lt(v___x_3479_, v_arity_3458_);
                if v___x_3480_ == 0 {
                    v___y_3461_ = v___y_3427_;
                    v___y_3462_ = v___y_3428_;
                    v___y_3463_ = v___y_3429_;
                    v___y_3464_ = v___y_3430_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_declName_3424_);
                    crate::leanh::lean_dec(v_mvarId_3423_);
                    crate::leanh::lean_dec_ref(v_val_3420_);
                    v___x_3481_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1), core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1_once), _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1);
                    v___x_3482_ =
                        l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(
                            v___x_3481_,
                            v___y_3427_,
                            v___y_3428_,
                            v___y_3429_,
                            v___y_3430_,
                        );
                    v_a_3483_ = crate::leanh::lean_ctor_get(v___x_3482_, 0);
                    v_isSharedCheck_3490_ = (!crate::leanh::lean_is_exclusive(v___x_3482_)) as u8;
                    if v_isSharedCheck_3490_ == 0 {
                        v___x_3485_ = v___x_3482_;
                        v_isShared_3486_ = v_isSharedCheck_3490_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3483_);
                        crate::leanh::lean_dec(v___x_3482_);
                        v___x_3485_ = crate::leanh::lean_box(0);
                        v_isShared_3486_ = v_isSharedCheck_3490_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3439_ = lean_array_get_borrowed(v___x_3421_, v_x_3422_, v___y_3433_);
                crate::leanh::lean_dec(v___y_3433_);
                v___x_3440_ = l_Lean_Expr_fvarId_x21(v___x_3439_);
                v___x_3441_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__0;
                v___x_3442_ = 0;
                v___x_3443_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3443_, 0, v___y_3434_);
                v___x_3444_ = l_Lean_MVarId_cases(
                    v_mvarId_3423_,
                    v___x_3440_,
                    v___x_3441_,
                    v___x_3442_,
                    v___x_3443_,
                    v___y_3435_,
                    v___y_3436_,
                    v___y_3437_,
                    v___y_3438_,
                );
                if crate::leanh::lean_obj_tag(v___x_3444_) == 0 {
                    v_a_3445_ = crate::leanh::lean_ctor_get(v___x_3444_, 0);
                    crate::leanh::lean_inc(v_a_3445_);
                    crate::leanh::lean_dec_ref_known(v___x_3444_, 1);
                    v_sz_3446_ = lean_array_size(v_a_3445_);
                    v___x_3447_ = 0usize;
                    v___x_3448_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__4(v_declName_3424_, v_val_3420_, v___x_3425_, v_sz_3446_, v___x_3447_, v_a_3445_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_);
                    return v___x_3448_;
                } else {
                    crate::leanh::lean_dec(v_declName_3424_);
                    crate::leanh::lean_dec_ref(v_val_3420_);
                    v_a_3449_ = crate::leanh::lean_ctor_get(v___x_3444_, 0);
                    v_isSharedCheck_3456_ = (!crate::leanh::lean_is_exclusive(v___x_3444_)) as u8;
                    if v_isSharedCheck_3456_ == 0 {
                        v___x_3451_ = v___x_3444_;
                        v_isShared_3452_ = v_isSharedCheck_3456_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3449_);
                        crate::leanh::lean_dec(v___x_3444_);
                        v___x_3451_ = crate::leanh::lean_box(0);
                        v_isShared_3452_ = v_isSharedCheck_3456_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3452_ == 0 {
                    v___x_3454_ = v___x_3451_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3455_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3455_, 0, v_a_3449_);
                    v___x_3454_ = v_reuseFailAlloc_3455_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3454_;
            }
            4 => {
                v___x_3465_ = lean_array_get_borrowed(v___x_3421_, v_x_3422_, v_majorPos_3457_);
                v___x_3466_ = l_Lean_Expr_isFVar(v___x_3465_);
                if v___x_3466_ == 0 {
                    crate::leanh::lean_dec(v_declName_3424_);
                    crate::leanh::lean_dec(v_mvarId_3423_);
                    crate::leanh::lean_dec_ref(v_val_3420_);
                    v___x_3467_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__2), core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__2_once), _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__2);
                    crate::leanh::lean_inc(v___x_3465_);
                    v___x_3468_ = l_Lean_indentExpr(v___x_3465_);
                    v___x_3469_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3469_, 0, v___x_3467_);
                    crate::leanh::lean_ctor_set(v___x_3469_, 1, v___x_3468_);
                    v___x_3470_ =
                        l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(
                            v___x_3469_,
                            v___y_3461_,
                            v___y_3462_,
                            v___y_3463_,
                            v___y_3464_,
                        );
                    v_a_3471_ = crate::leanh::lean_ctor_get(v___x_3470_, 0);
                    v_isSharedCheck_3478_ = (!crate::leanh::lean_is_exclusive(v___x_3470_)) as u8;
                    if v_isSharedCheck_3478_ == 0 {
                        v___x_3473_ = v___x_3470_;
                        v_isShared_3474_ = v_isSharedCheck_3478_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3471_);
                        crate::leanh::lean_dec(v___x_3470_);
                        v___x_3473_ = crate::leanh::lean_box(0);
                        v_isShared_3474_ = v_isSharedCheck_3478_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_insterestingCtors_3459_);
                    crate::leanh::lean_inc(v_majorPos_3457_);
                    v___y_3433_ = v_majorPos_3457_;
                    v___y_3434_ = v_insterestingCtors_3459_;
                    v___y_3435_ = v___y_3461_;
                    v___y_3436_ = v___y_3462_;
                    v___y_3437_ = v___y_3463_;
                    v___y_3438_ = v___y_3464_;
                    state = 1;
                    continue;
                }
            }
            5 => {
                if v_isShared_3474_ == 0 {
                    v___x_3476_ = v___x_3473_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3477_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3477_, 0, v_a_3471_);
                    v___x_3476_ = v_reuseFailAlloc_3477_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3476_;
            }
            7 => {
                if v_isShared_3486_ == 0 {
                    v___x_3488_ = v___x_3485_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3489_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3489_, 0, v_a_3483_);
                    v___x_3488_ = v_reuseFailAlloc_3489_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3488_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___boxed(
    mut v_val_3491_: *mut crate::leanh::LeanObject,
    mut v___x_3492_: *mut crate::leanh::LeanObject,
    mut v_x_3493_: *mut crate::leanh::LeanObject,
    mut v_mvarId_3494_: *mut crate::leanh::LeanObject,
    mut v_declName_3495_: *mut crate::leanh::LeanObject,
    mut v___x_3496_: *mut crate::leanh::LeanObject,
    mut v_____r_3497_: *mut crate::leanh::LeanObject,
    mut v___y_3498_: *mut crate::leanh::LeanObject,
    mut v___y_3499_: *mut crate::leanh::LeanObject,
    mut v___y_3500_: *mut crate::leanh::LeanObject,
    mut v___y_3501_: *mut crate::leanh::LeanObject,
    mut v___y_3502_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_33951__boxed_3503_: u8 = 0;
    let mut v_res_3504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_33951__boxed_3503_ = (crate::leanh::lean_unbox(v___x_3496_) as u8);
    v_res_3504_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1(
        v_val_3491_,
        v___x_3492_,
        v_x_3493_,
        v_mvarId_3494_,
        v_declName_3495_,
        v___x_33951__boxed_3503_,
        v_____r_3497_,
        v___y_3498_,
        v___y_3499_,
        v___y_3500_,
        v___y_3501_,
    );
    crate::leanh::lean_dec(v___y_3501_);
    crate::leanh::lean_dec_ref(v___y_3500_);
    crate::leanh::lean_dec(v___y_3499_);
    crate::leanh::lean_dec_ref(v___y_3498_);
    crate::leanh::lean_dec_ref(v_x_3493_);
    crate::leanh::lean_dec_ref(v___x_3492_);
    return v_res_3504_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(
    mut v_cls_3507_: *mut crate::leanh::LeanObject,
    mut v_msg_3508_: *mut crate::leanh::LeanObject,
    mut v___y_3509_: *mut crate::leanh::LeanObject,
    mut v___y_3510_: *mut crate::leanh::LeanObject,
    mut v___y_3511_: *mut crate::leanh::LeanObject,
    mut v___y_3512_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_3514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3519_: u8 = 0;
    let mut v___x_3520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3532_: u8 = 0;
    let mut v_tid_3533_: u64 = 0;
    let mut v_traces_3534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3537_: u8 = 0;
    let mut v___x_3538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3539_: f64 = 0.0;
    let mut v___x_3540_: u8 = 0;
    let mut v___x_3541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3558_: u8 = 0;
    let mut v_isSharedCheck_3559_: u8 = 0;
    let mut v_isSharedCheck_3560_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3514_ = crate::leanh::lean_ctor_get(v___y_3511_, 5);
                v___x_3515_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3_spec__5(v_msg_3508_, v___y_3509_, v___y_3510_, v___y_3511_, v___y_3512_);
                v_a_3516_ = crate::leanh::lean_ctor_get(v___x_3515_, 0);
                v_isSharedCheck_3560_ = (!crate::leanh::lean_is_exclusive(v___x_3515_)) as u8;
                if v_isSharedCheck_3560_ == 0 {
                    v___x_3518_ = v___x_3515_;
                    v_isShared_3519_ = v_isSharedCheck_3560_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3516_);
                    crate::leanh::lean_dec(v___x_3515_);
                    v___x_3518_ = crate::leanh::lean_box(0);
                    v_isShared_3519_ = v_isSharedCheck_3560_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3520_ = lean_st_ref_take(v___y_3512_);
                v_traceState_3521_ = crate::leanh::lean_ctor_get(v___x_3520_, 4);
                v_env_3522_ = crate::leanh::lean_ctor_get(v___x_3520_, 0);
                v_nextMacroScope_3523_ = crate::leanh::lean_ctor_get(v___x_3520_, 1);
                v_ngen_3524_ = crate::leanh::lean_ctor_get(v___x_3520_, 2);
                v_auxDeclNGen_3525_ = crate::leanh::lean_ctor_get(v___x_3520_, 3);
                v_cache_3526_ = crate::leanh::lean_ctor_get(v___x_3520_, 5);
                v_messages_3527_ = crate::leanh::lean_ctor_get(v___x_3520_, 6);
                v_infoState_3528_ = crate::leanh::lean_ctor_get(v___x_3520_, 7);
                v_snapshotTasks_3529_ = crate::leanh::lean_ctor_get(v___x_3520_, 8);
                v_isSharedCheck_3559_ = (!crate::leanh::lean_is_exclusive(v___x_3520_)) as u8;
                if v_isSharedCheck_3559_ == 0 {
                    v___x_3531_ = v___x_3520_;
                    v_isShared_3532_ = v_isSharedCheck_3559_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_3529_);
                    crate::leanh::lean_inc(v_infoState_3528_);
                    crate::leanh::lean_inc(v_messages_3527_);
                    crate::leanh::lean_inc(v_cache_3526_);
                    crate::leanh::lean_inc(v_traceState_3521_);
                    crate::leanh::lean_inc(v_auxDeclNGen_3525_);
                    crate::leanh::lean_inc(v_ngen_3524_);
                    crate::leanh::lean_inc(v_nextMacroScope_3523_);
                    crate::leanh::lean_inc(v_env_3522_);
                    crate::leanh::lean_dec(v___x_3520_);
                    v___x_3531_ = crate::leanh::lean_box(0);
                    v_isShared_3532_ = v_isSharedCheck_3559_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_3533_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_3521_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_3534_ = crate::leanh::lean_ctor_get(v_traceState_3521_, 0);
                v_isSharedCheck_3558_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_3521_)) as u8;
                if v_isSharedCheck_3558_ == 0 {
                    v___x_3536_ = v_traceState_3521_;
                    v_isShared_3537_ = v_isSharedCheck_3558_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_3534_);
                    crate::leanh::lean_dec(v_traceState_3521_);
                    v___x_3536_ = crate::leanh::lean_box(0);
                    v_isShared_3537_ = v_isSharedCheck_3558_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3538_ = crate::leanh::lean_box(0);
                v___x_3539_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__2_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__2);
                v___x_3540_ = 0;
                v___x_3541_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__6;
                v___x_3542_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v___x_3542_, 0, v_cls_3507_);
                crate::leanh::lean_ctor_set(v___x_3542_, 1, v___x_3538_);
                crate::leanh::lean_ctor_set(v___x_3542_, 2, v___x_3541_);
                crate::leanh::lean_ctor_set_float(
                    v___x_3542_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_3539_,
                );
                crate::leanh::lean_ctor_set_float(
                    v___x_3542_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_3539_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3542_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_3540_,
                );
                v___x_3543_ =
                    l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0___closed__0;
                v___x_3544_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3544_, 0, v___x_3542_);
                crate::leanh::lean_ctor_set(v___x_3544_, 1, v_a_3516_);
                crate::leanh::lean_ctor_set(v___x_3544_, 2, v___x_3543_);
                crate::leanh::lean_inc(v_ref_3514_);
                v___x_3545_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3545_, 0, v_ref_3514_);
                crate::leanh::lean_ctor_set(v___x_3545_, 1, v___x_3544_);
                v___x_3546_ = l_Lean_PersistentArray_push___redArg(v_traces_3534_, v___x_3545_);
                if v_isShared_3537_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3536_, 0, v___x_3546_);
                    v___x_3548_ = v___x_3536_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3557_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3557_, 0, v___x_3546_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_3557_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_3533_,
                    );
                    v___x_3548_ = v_reuseFailAlloc_3557_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3532_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3531_, 4, v___x_3548_);
                    v___x_3550_ = v___x_3531_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3556_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3556_, 0, v_env_3522_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3556_, 1, v_nextMacroScope_3523_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3556_, 2, v_ngen_3524_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3556_, 3, v_auxDeclNGen_3525_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3556_, 4, v___x_3548_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3556_, 5, v_cache_3526_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3556_, 6, v_messages_3527_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3556_, 7, v_infoState_3528_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3556_, 8, v_snapshotTasks_3529_);
                    v___x_3550_ = v_reuseFailAlloc_3556_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3551_ = lean_st_ref_set(v___y_3512_, v___x_3550_);
                v___x_3552_ = crate::leanh::lean_box(0);
                if v_isShared_3519_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3518_, 0, v___x_3552_);
                    v___x_3554_ = v___x_3518_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3555_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3555_, 0, v___x_3552_);
                    v___x_3554_ = v_reuseFailAlloc_3555_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3554_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0___boxed(
    mut v_cls_3561_: *mut crate::leanh::LeanObject,
    mut v_msg_3562_: *mut crate::leanh::LeanObject,
    mut v___y_3563_: *mut crate::leanh::LeanObject,
    mut v___y_3564_: *mut crate::leanh::LeanObject,
    mut v___y_3565_: *mut crate::leanh::LeanObject,
    mut v___y_3566_: *mut crate::leanh::LeanObject,
    mut v___y_3567_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3568_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(
        v_cls_3561_,
        v_msg_3562_,
        v___y_3563_,
        v___y_3564_,
        v___y_3565_,
        v___y_3566_,
    );
    crate::leanh::lean_dec(v___y_3566_);
    crate::leanh::lean_dec_ref(v___y_3565_);
    crate::leanh::lean_dec(v___y_3564_);
    crate::leanh::lean_dec_ref(v___y_3563_);
    return v_res_3568_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__2(
    mut v_val_3569_: *mut crate::leanh::LeanObject,
    mut v___x_3570_: *mut crate::leanh::LeanObject,
    mut v_x_3571_: *mut crate::leanh::LeanObject,
    mut v_mvarId_3572_: *mut crate::leanh::LeanObject,
    mut v___x_3573_: u8,
    mut v_declName_3574_: *mut crate::leanh::LeanObject,
    mut v_____r_3575_: *mut crate::leanh::LeanObject,
    mut v___y_3576_: *mut crate::leanh::LeanObject,
    mut v___y_3577_: *mut crate::leanh::LeanObject,
    mut v___y_3578_: *mut crate::leanh::LeanObject,
    mut v___y_3579_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3594_: usize = 0;
    let mut v___x_3595_: usize = 0;
    let mut v___x_3596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3600_: u8 = 0;
    let mut v___x_3602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3604_: u8 = 0;
    let mut v_majorPos_3605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arity_3606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_insterestingCtors_3607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: u8 = 0;
    let mut v___x_3615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3622_: u8 = 0;
    let mut v___x_3624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3626_: u8 = 0;
    let mut v___x_3627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: u8 = 0;
    let mut v___x_3629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3634_: u8 = 0;
    let mut v___x_3636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3638_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_majorPos_3605_ = crate::leanh::lean_ctor_get(v_val_3569_, 1);
                v_arity_3606_ = crate::leanh::lean_ctor_get(v_val_3569_, 2);
                v_insterestingCtors_3607_ = crate::leanh::lean_ctor_get(v_val_3569_, 3);
                v___x_3627_ = lean_array_get_size(v_x_3571_);
                v___x_3628_ = lean_nat_dec_lt(v___x_3627_, v_arity_3606_);
                if v___x_3628_ == 0 {
                    v___y_3609_ = v___y_3576_;
                    v___y_3610_ = v___y_3577_;
                    v___y_3611_ = v___y_3578_;
                    v___y_3612_ = v___y_3579_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_declName_3574_);
                    crate::leanh::lean_dec(v_mvarId_3572_);
                    crate::leanh::lean_dec_ref(v_val_3569_);
                    v___x_3629_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1), core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1_once), _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1);
                    v___x_3630_ =
                        l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(
                            v___x_3629_,
                            v___y_3576_,
                            v___y_3577_,
                            v___y_3578_,
                            v___y_3579_,
                        );
                    v_a_3631_ = crate::leanh::lean_ctor_get(v___x_3630_, 0);
                    v_isSharedCheck_3638_ = (!crate::leanh::lean_is_exclusive(v___x_3630_)) as u8;
                    if v_isSharedCheck_3638_ == 0 {
                        v___x_3633_ = v___x_3630_;
                        v_isShared_3634_ = v_isSharedCheck_3638_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3631_);
                        crate::leanh::lean_dec(v___x_3630_);
                        v___x_3633_ = crate::leanh::lean_box(0);
                        v_isShared_3634_ = v_isSharedCheck_3638_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3588_ = lean_array_get_borrowed(v___x_3570_, v_x_3571_, v___y_3582_);
                crate::leanh::lean_dec(v___y_3582_);
                v___x_3589_ = l_Lean_Expr_fvarId_x21(v___x_3588_);
                v___x_3590_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__0;
                v___x_3591_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3591_, 0, v___y_3583_);
                v___x_3592_ = l_Lean_MVarId_cases(
                    v_mvarId_3572_,
                    v___x_3589_,
                    v___x_3590_,
                    v___x_3573_,
                    v___x_3591_,
                    v___y_3584_,
                    v___y_3585_,
                    v___y_3586_,
                    v___y_3587_,
                );
                if crate::leanh::lean_obj_tag(v___x_3592_) == 0 {
                    v_a_3593_ = crate::leanh::lean_ctor_get(v___x_3592_, 0);
                    crate::leanh::lean_inc(v_a_3593_);
                    crate::leanh::lean_dec_ref_known(v___x_3592_, 1);
                    v_sz_3594_ = lean_array_size(v_a_3593_);
                    v___x_3595_ = 0usize;
                    v___x_3596_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3(v_declName_3574_, v_val_3569_, v___x_3573_, v_sz_3594_, v___x_3595_, v_a_3593_, v___y_3584_, v___y_3585_, v___y_3586_, v___y_3587_);
                    return v___x_3596_;
                } else {
                    crate::leanh::lean_dec(v_declName_3574_);
                    crate::leanh::lean_dec_ref(v_val_3569_);
                    v_a_3597_ = crate::leanh::lean_ctor_get(v___x_3592_, 0);
                    v_isSharedCheck_3604_ = (!crate::leanh::lean_is_exclusive(v___x_3592_)) as u8;
                    if v_isSharedCheck_3604_ == 0 {
                        v___x_3599_ = v___x_3592_;
                        v_isShared_3600_ = v_isSharedCheck_3604_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3597_);
                        crate::leanh::lean_dec(v___x_3592_);
                        v___x_3599_ = crate::leanh::lean_box(0);
                        v_isShared_3600_ = v_isSharedCheck_3604_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3600_ == 0 {
                    v___x_3602_ = v___x_3599_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3603_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3603_, 0, v_a_3597_);
                    v___x_3602_ = v_reuseFailAlloc_3603_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3602_;
            }
            4 => {
                v___x_3613_ = lean_array_get_borrowed(v___x_3570_, v_x_3571_, v_majorPos_3605_);
                v___x_3614_ = l_Lean_Expr_isFVar(v___x_3613_);
                if v___x_3614_ == 0 {
                    crate::leanh::lean_dec(v_declName_3574_);
                    crate::leanh::lean_dec(v_mvarId_3572_);
                    crate::leanh::lean_dec_ref(v_val_3569_);
                    v___x_3615_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__2), core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__2_once), _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__2);
                    crate::leanh::lean_inc(v___x_3613_);
                    v___x_3616_ = l_Lean_indentExpr(v___x_3613_);
                    v___x_3617_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3617_, 0, v___x_3615_);
                    crate::leanh::lean_ctor_set(v___x_3617_, 1, v___x_3616_);
                    v___x_3618_ =
                        l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(
                            v___x_3617_,
                            v___y_3609_,
                            v___y_3610_,
                            v___y_3611_,
                            v___y_3612_,
                        );
                    v_a_3619_ = crate::leanh::lean_ctor_get(v___x_3618_, 0);
                    v_isSharedCheck_3626_ = (!crate::leanh::lean_is_exclusive(v___x_3618_)) as u8;
                    if v_isSharedCheck_3626_ == 0 {
                        v___x_3621_ = v___x_3618_;
                        v_isShared_3622_ = v_isSharedCheck_3626_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3619_);
                        crate::leanh::lean_dec(v___x_3618_);
                        v___x_3621_ = crate::leanh::lean_box(0);
                        v_isShared_3622_ = v_isSharedCheck_3626_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_insterestingCtors_3607_);
                    crate::leanh::lean_inc(v_majorPos_3605_);
                    v___y_3582_ = v_majorPos_3605_;
                    v___y_3583_ = v_insterestingCtors_3607_;
                    v___y_3584_ = v___y_3609_;
                    v___y_3585_ = v___y_3610_;
                    v___y_3586_ = v___y_3611_;
                    v___y_3587_ = v___y_3612_;
                    state = 1;
                    continue;
                }
            }
            5 => {
                if v_isShared_3622_ == 0 {
                    v___x_3624_ = v___x_3621_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3625_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3625_, 0, v_a_3619_);
                    v___x_3624_ = v_reuseFailAlloc_3625_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3624_;
            }
            7 => {
                if v_isShared_3634_ == 0 {
                    v___x_3636_ = v___x_3633_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3637_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3637_, 0, v_a_3631_);
                    v___x_3636_ = v_reuseFailAlloc_3637_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3636_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__2___boxed(
    mut v_val_3639_: *mut crate::leanh::LeanObject,
    mut v___x_3640_: *mut crate::leanh::LeanObject,
    mut v_x_3641_: *mut crate::leanh::LeanObject,
    mut v_mvarId_3642_: *mut crate::leanh::LeanObject,
    mut v___x_3643_: *mut crate::leanh::LeanObject,
    mut v_declName_3644_: *mut crate::leanh::LeanObject,
    mut v_____r_3645_: *mut crate::leanh::LeanObject,
    mut v___y_3646_: *mut crate::leanh::LeanObject,
    mut v___y_3647_: *mut crate::leanh::LeanObject,
    mut v___y_3648_: *mut crate::leanh::LeanObject,
    mut v___y_3649_: *mut crate::leanh::LeanObject,
    mut v___y_3650_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_34203__boxed_3651_: u8 = 0;
    let mut v_res_3652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_34203__boxed_3651_ = (crate::leanh::lean_unbox(v___x_3643_) as u8);
    v_res_3652_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__2(
        v_val_3639_,
        v___x_3640_,
        v_x_3641_,
        v_mvarId_3642_,
        v___x_34203__boxed_3651_,
        v_declName_3644_,
        v_____r_3645_,
        v___y_3646_,
        v___y_3647_,
        v___y_3648_,
        v___y_3649_,
    );
    crate::leanh::lean_dec(v___y_3649_);
    crate::leanh::lean_dec_ref(v___y_3648_);
    crate::leanh::lean_dec(v___y_3647_);
    crate::leanh::lean_dec_ref(v___y_3646_);
    crate::leanh::lean_dec_ref(v_x_3641_);
    crate::leanh::lean_dec_ref(v___x_3640_);
    return v_res_3652_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__0(
    mut v___x_3653_: *mut crate::leanh::LeanObject,
    mut v___y_3654_: *mut crate::leanh::LeanObject,
    mut v___y_3655_: *mut crate::leanh::LeanObject,
    mut v___y_3656_: *mut crate::leanh::LeanObject,
    mut v___y_3657_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_3659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3660_: u8 = 0;
    v_options_3659_ = crate::leanh::lean_ctor_get(v___y_3656_, 2);
    v_hasTrace_3660_ = crate::leanh::lean_ctor_get_uint8(
        v_options_3659_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
    );
    if v_hasTrace_3660_ == 0 {
        let mut v___x_3661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___x_3653_);
        v___x_3661_ = crate::leanh::lean_box((v_hasTrace_3660_) as usize);
        v___x_3662_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3662_, 0, v___x_3661_);
        return v___x_3662_;
    } else {
        let mut v_inheritedTraceOptions_3663_: *mut crate::leanh::LeanObject =
            core::ptr::null_mut();
        let mut v___x_3664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3666_: u8 = 0;
        let mut v___x_3667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_inheritedTraceOptions_3663_ = crate::leanh::lean_ctor_get(v___y_3656_, 13);
        v___x_3664_ =
            l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__8;
        v___x_3665_ = l_Lean_Name_append(v___x_3664_, v___x_3653_);
        v___x_3666_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
            v_inheritedTraceOptions_3663_,
            v_options_3659_,
            v___x_3665_,
        );
        crate::leanh::lean_dec(v___x_3665_);
        v___x_3667_ = crate::leanh::lean_box((v___x_3666_) as usize);
        v___x_3668_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3668_, 0, v___x_3667_);
        return v___x_3668_;
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__0___boxed(
    mut v___x_3669_: *mut crate::leanh::LeanObject,
    mut v___y_3670_: *mut crate::leanh::LeanObject,
    mut v___y_3671_: *mut crate::leanh::LeanObject,
    mut v___y_3672_: *mut crate::leanh::LeanObject,
    mut v___y_3673_: *mut crate::leanh::LeanObject,
    mut v___y_3674_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3675_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__0(
        v___x_3669_,
        v___y_3670_,
        v___y_3671_,
        v___y_3672_,
        v___y_3673_,
    );
    crate::leanh::lean_dec(v___y_3673_);
    crate::leanh::lean_dec_ref(v___y_3672_);
    crate::leanh::lean_dec(v___y_3671_);
    crate::leanh::lean_dec_ref(v___y_3670_);
    return v_res_3675_;
}
pub unsafe fn _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3677_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__0;
    v___x_3678_ = l_Lean_stringToMessageData(v___x_3677_);
    return v___x_3678_;
}
pub unsafe fn _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3680_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__2;
    v___x_3681_ = l_Lean_stringToMessageData(v___x_3680_);
    return v___x_3681_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5(
    mut v_mvarId_3682_: *mut crate::leanh::LeanObject,
    mut v_x_3683_: *mut crate::leanh::LeanObject,
    mut v_x_3684_: *mut crate::leanh::LeanObject,
    mut v_x_3685_: *mut crate::leanh::LeanObject,
    mut v___y_3686_: *mut crate::leanh::LeanObject,
    mut v___y_3687_: *mut crate::leanh::LeanObject,
    mut v___y_3688_: *mut crate::leanh::LeanObject,
    mut v___y_3689_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fn_3691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_3692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_3697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3704_: u8 = 0;
    let mut v_inheritedTraceOptions_3705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3706_: u8 = 0;
    let mut v___x_3707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3712_: u8 = 0;
    let mut v___x_3713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3717_: u8 = 0;
    let mut v___x_3718_: u8 = 0;
    let mut v___x_3720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3729_: u8 = 0;
    let mut v___x_3731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3733_: u8 = 0;
    let mut v_unused_3734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3738_: u8 = 0;
    let mut v___x_3740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3742_: u8 = 0;
    let mut v_isSharedCheck_3743_: u8 = 0;
    let mut v___y_3745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3747_: u8 = 0;
    let mut v___x_3748_: u8 = 0;
    let mut v___y_3750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3755_: u8 = 0;
    let mut v___x_3756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3760_: u8 = 0;
    let mut v___x_3761_: u8 = 0;
    let mut v___x_3763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3772_: u8 = 0;
    let mut v___x_3774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3776_: u8 = 0;
    let mut v_unused_3777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3781_: u8 = 0;
    let mut v___x_3783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3785_: u8 = 0;
    let mut v_isSharedCheck_3786_: u8 = 0;
    let mut v___y_3788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3790_: u8 = 0;
    let mut v___x_3791_: u8 = 0;
    let mut v___y_3793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3806_: usize = 0;
    let mut v___x_3807_: usize = 0;
    let mut v___x_3808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3813_: u8 = 0;
    let mut v___x_3815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3817_: u8 = 0;
    let mut v_reuseFailAlloc_3818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_majorPos_3819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arity_3820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_insterestingCtors_3821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: u8 = 0;
    let mut v___x_3829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3836_: u8 = 0;
    let mut v___x_3838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3840_: u8 = 0;
    let mut v___x_3841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: u8 = 0;
    let mut v___x_3843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3848_: u8 = 0;
    let mut v___x_3850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3852_: u8 = 0;
    let mut v___f_3853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: u8 = 0;
    let mut v___y_3858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: f64 = 0.0;
    let mut v___x_3863_: f64 = 0.0;
    let mut v___x_3864_: f64 = 0.0;
    let mut v___x_3865_: f64 = 0.0;
    let mut v___x_3866_: f64 = 0.0;
    let mut v___x_3867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3881_: u8 = 0;
    let mut v___x_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3884_: u8 = 0;
    let mut v___x_3885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3895_: u8 = 0;
    let mut v___x_3896_: u8 = 0;
    let mut v___y_3898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3904_: u8 = 0;
    let mut v___x_3906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3908_: u8 = 0;
    let mut v_a_3909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3915_: f64 = 0.0;
    let mut v___x_3916_: f64 = 0.0;
    let mut v___x_3917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3931_: u8 = 0;
    let mut v___x_3932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: u8 = 0;
    let mut v___x_3935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3945_: u8 = 0;
    let mut v___x_3946_: u8 = 0;
    let mut v___y_3948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3954_: u8 = 0;
    let mut v___x_3956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3958_: u8 = 0;
    let mut v_a_3959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3965_: u8 = 0;
    let mut v___x_3966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: u8 = 0;
    let mut v___x_3968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3992_: u8 = 0;
    let mut v___x_3993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: u8 = 0;
    let mut v___x_3995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4006_: u8 = 0;
    let mut v___x_4008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4010_: u8 = 0;
    let mut v_isSharedCheck_4011_: u8 = 0;
    let mut v___x_4012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4017_: u8 = 0;
    let mut v___x_4019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4021_: u8 = 0;
    let mut v___x_4022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3683_) == 5 {
                    v_fn_3691_ = crate::leanh::lean_ctor_get(v_x_3683_, 0);
                    crate::leanh::lean_inc_ref(v_fn_3691_);
                    v_arg_3692_ = crate::leanh::lean_ctor_get(v_x_3683_, 1);
                    crate::leanh::lean_inc_ref(v_arg_3692_);
                    crate::leanh::lean_dec_ref_known(v_x_3683_, 2);
                    v___x_3693_ = lean_array_set(v_x_3684_, v_x_3685_, v_arg_3692_);
                    v___x_3694_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3695_ = lean_nat_sub(v_x_3685_, v___x_3694_);
                    crate::leanh::lean_dec(v_x_3685_);
                    v_x_3683_ = v_fn_3691_;
                    v_x_3684_ = v___x_3693_;
                    v_x_3685_ = v___x_3695_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_x_3685_);
                    if crate::leanh::lean_obj_tag(v_x_3683_) == 4 {
                        v_declName_3697_ = crate::leanh::lean_ctor_get(v_x_3683_, 0);
                        crate::leanh::lean_inc_n(v_declName_3697_, 2);
                        crate::leanh::lean_dec_ref_known(v_x_3683_, 2);
                        v___x_3698_ = l_Lean_Meta_getSparseCasesOnInfo___redArg(
                            v_declName_3697_,
                            v___y_3689_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3698_) == 0 {
                            v_a_3699_ = crate::leanh::lean_ctor_get(v___x_3698_, 0);
                            crate::leanh::lean_inc(v_a_3699_);
                            crate::leanh::lean_dec_ref_known(v___x_3698_, 1);
                            if crate::leanh::lean_obj_tag(v_a_3699_) == 1 {
                                v_options_3700_ = crate::leanh::lean_ctor_get(v___y_3688_, 2);
                                v_val_3701_ = crate::leanh::lean_ctor_get(v_a_3699_, 0);
                                v_isSharedCheck_4011_ =
                                    (!crate::leanh::lean_is_exclusive(v_a_3699_)) as u8;
                                if v_isSharedCheck_4011_ == 0 {
                                    v___x_3703_ = v_a_3699_;
                                    v_isShared_3704_ = v_isSharedCheck_4011_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_val_3701_);
                                    crate::leanh::lean_dec(v_a_3699_);
                                    v___x_3703_ = crate::leanh::lean_box(0);
                                    v_isShared_3704_ = v_isSharedCheck_4011_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_3699_);
                                crate::leanh::lean_dec(v_declName_3697_);
                                crate::leanh::lean_dec_ref(v_x_3684_);
                                crate::leanh::lean_dec(v_mvarId_3682_);
                                v___x_4012_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__12), core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__12_once), _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__12);
                                v___x_4013_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_4012_, v___y_3686_, v___y_3687_, v___y_3688_, v___y_3689_);
                                return v___x_4013_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_declName_3697_);
                            crate::leanh::lean_dec_ref(v_x_3684_);
                            crate::leanh::lean_dec(v_mvarId_3682_);
                            v_a_4014_ = crate::leanh::lean_ctor_get(v___x_3698_, 0);
                            v_isSharedCheck_4021_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3698_)) as u8;
                            if v_isSharedCheck_4021_ == 0 {
                                v___x_4016_ = v___x_3698_;
                                v_isShared_4017_ = v_isSharedCheck_4021_;
                                state = 48;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4014_);
                                crate::leanh::lean_dec(v___x_3698_);
                                v___x_4016_ = crate::leanh::lean_box(0);
                                v_isShared_4017_ = v_isSharedCheck_4021_;
                                state = 48;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_x_3684_);
                        crate::leanh::lean_dec_ref(v_x_3683_);
                        crate::leanh::lean_dec(v_mvarId_3682_);
                        v___x_4022_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__14), core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__14_once), _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__14);
                        v___x_4023_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_4022_, v___y_3686_, v___y_3687_, v___y_3688_, v___y_3689_);
                        return v___x_4023_;
                    }
                }
            }
            1 => {
                v_inheritedTraceOptions_3705_ = crate::leanh::lean_ctor_get(v___y_3688_, 13);
                v_hasTrace_3706_ = crate::leanh::lean_ctor_get_uint8(
                    v_options_3700_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v___x_3707_ = l_Lean_instInhabitedExpr;
                v___x_3708_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__5;
                if v_hasTrace_3706_ == 0 {
                    v_majorPos_3819_ = crate::leanh::lean_ctor_get(v_val_3701_, 1);
                    v_arity_3820_ = crate::leanh::lean_ctor_get(v_val_3701_, 2);
                    v_insterestingCtors_3821_ = crate::leanh::lean_ctor_get(v_val_3701_, 3);
                    v___x_3841_ = lean_array_get_size(v_x_3684_);
                    v___x_3842_ = lean_nat_dec_lt(v___x_3841_, v_arity_3820_);
                    if v___x_3842_ == 0 {
                        v___y_3823_ = v___y_3686_;
                        v___y_3824_ = v___y_3687_;
                        v___y_3825_ = v___y_3688_;
                        v___y_3826_ = v___y_3689_;
                        state = 23;
                        continue;
                    } else {
                        crate::leanh::lean_del_object(v___x_3703_);
                        crate::leanh::lean_dec(v_val_3701_);
                        crate::leanh::lean_dec(v_declName_3697_);
                        crate::leanh::lean_dec_ref(v_x_3684_);
                        crate::leanh::lean_dec(v_mvarId_3682_);
                        v___x_3843_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1), core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1_once), _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1);
                        v___x_3844_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_3843_, v___y_3686_, v___y_3687_, v___y_3688_, v___y_3689_);
                        v_a_3845_ = crate::leanh::lean_ctor_get(v___x_3844_, 0);
                        v_isSharedCheck_3852_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3844_)) as u8;
                        if v_isSharedCheck_3852_ == 0 {
                            v___x_3847_ = v___x_3844_;
                            v_isShared_3848_ = v_isSharedCheck_3852_;
                            state = 26;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3845_);
                            crate::leanh::lean_dec(v___x_3844_);
                            v___x_3847_ = crate::leanh::lean_box(0);
                            v_isShared_3848_ = v_isSharedCheck_3852_;
                            state = 26;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3703_);
                    v___f_3853_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__1;
                    v___x_3854_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__6;
                    v___x_3855_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__9), core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__9_once), _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__9);
                    v___x_3856_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_3705_,
                        v_options_3700_,
                        v___x_3855_,
                    );
                    if v___x_3856_ == 0 {
                        v___x_3993_ = l_Lean_trace_profiler;
                        v___x_3994_ =
                            l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__5(
                                v_options_3700_,
                                v___x_3993_,
                            );
                        if v___x_3994_ == 0 {
                            if v___x_3856_ == 0 {
                                v___x_3995_ = crate::leanh::lean_box(0);
                                v___x_3996_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__2(v_val_3701_, v___x_3707_, v_x_3684_, v_mvarId_3682_, v___x_3994_, v_declName_3697_, v___x_3995_, v___y_3686_, v___y_3687_, v___y_3688_, v___y_3689_);
                                crate::leanh::lean_dec_ref(v_x_3684_);
                                v___y_3750_ = v___x_3996_;
                                state = 10;
                                continue;
                            } else {
                                v___x_3997_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__3), core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__3_once), _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__3);
                                crate::leanh::lean_inc(v_mvarId_3682_);
                                v___x_3998_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3998_, 0, v_mvarId_3682_);
                                v___x_3999_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3999_, 0, v___x_3997_);
                                crate::leanh::lean_ctor_set(v___x_3999_, 1, v___x_3998_);
                                v___x_4000_ =
                                    l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(
                                        v___x_3708_,
                                        v___x_3999_,
                                        v___y_3686_,
                                        v___y_3687_,
                                        v___y_3688_,
                                        v___y_3689_,
                                    );
                                if crate::leanh::lean_obj_tag(v___x_4000_) == 0 {
                                    v_a_4001_ = crate::leanh::lean_ctor_get(v___x_4000_, 0);
                                    crate::leanh::lean_inc(v_a_4001_);
                                    crate::leanh::lean_dec_ref_known(v___x_4000_, 1);
                                    v___x_4002_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__2(v_val_3701_, v___x_3707_, v_x_3684_, v_mvarId_3682_, v___x_3994_, v_declName_3697_, v_a_4001_, v___y_3686_, v___y_3687_, v___y_3688_, v___y_3689_);
                                    crate::leanh::lean_dec_ref(v_x_3684_);
                                    v___y_3750_ = v___x_4002_;
                                    state = 10;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_val_3701_);
                                    crate::leanh::lean_dec(v_declName_3697_);
                                    crate::leanh::lean_dec_ref(v_x_3684_);
                                    crate::leanh::lean_dec(v_mvarId_3682_);
                                    v_a_4003_ = crate::leanh::lean_ctor_get(v___x_4000_, 0);
                                    v_isSharedCheck_4010_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_4000_)) as u8;
                                    if v_isSharedCheck_4010_ == 0 {
                                        v___x_4005_ = v___x_4000_;
                                        v_isShared_4006_ = v_isSharedCheck_4010_;
                                        state = 46;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_4003_);
                                        crate::leanh::lean_dec(v___x_4000_);
                                        v___x_4005_ = crate::leanh::lean_box(0);
                                        v_isShared_4006_ = v_isSharedCheck_4010_;
                                        state = 46;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            state = 42;
                            continue;
                        }
                    } else {
                        state = 42;
                        continue;
                    }
                }
            }
            2 => {
                if v___y_3712_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_3710_);
                    v___x_3713_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__0(v___x_3708_, v___y_3686_, v___y_3687_, v___y_3688_, v___y_3689_);
                    v_a_3714_ = crate::leanh::lean_ctor_get(v___x_3713_, 0);
                    v_isSharedCheck_3743_ = (!crate::leanh::lean_is_exclusive(v___x_3713_)) as u8;
                    if v_isSharedCheck_3743_ == 0 {
                        v___x_3716_ = v___x_3713_;
                        v_isShared_3717_ = v_isSharedCheck_3743_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3714_);
                        crate::leanh::lean_dec(v___x_3713_);
                        v___x_3716_ = crate::leanh::lean_box(0);
                        v_isShared_3717_ = v_isSharedCheck_3743_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_3711_);
                    return v___y_3710_;
                }
            }
            3 => {
                v___x_3718_ = (crate::leanh::lean_unbox(v_a_3714_) as u8);
                crate::leanh::lean_dec(v_a_3714_);
                if v___x_3718_ == 0 {
                    if v_isShared_3717_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_3716_, 1);
                        crate::leanh::lean_ctor_set(v___x_3716_, 0, v___y_3711_);
                        v___x_3720_ = v___x_3716_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3721_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3721_, 0, v___y_3711_);
                        v___x_3720_ = v_reuseFailAlloc_3721_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3716_);
                    v___x_3722_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__1), core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__1_once), _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__1);
                    crate::leanh::lean_inc_ref(v___y_3711_);
                    v___x_3723_ = l_Lean_Exception_toMessageData(v___y_3711_);
                    v___x_3724_ = l_Lean_indentD(v___x_3723_);
                    v___x_3725_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3725_, 0, v___x_3722_);
                    crate::leanh::lean_ctor_set(v___x_3725_, 1, v___x_3724_);
                    v___x_3726_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(
                        v___x_3708_,
                        v___x_3725_,
                        v___y_3686_,
                        v___y_3687_,
                        v___y_3688_,
                        v___y_3689_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3726_) == 0 {
                        v_isSharedCheck_3733_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3726_)) as u8;
                        if v_isSharedCheck_3733_ == 0 {
                            v_unused_3734_ = crate::leanh::lean_ctor_get(v___x_3726_, 0);
                            crate::leanh::lean_dec(v_unused_3734_);
                            v___x_3728_ = v___x_3726_;
                            v_isShared_3729_ = v_isSharedCheck_3733_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_3726_);
                            v___x_3728_ = crate::leanh::lean_box(0);
                            v_isShared_3729_ = v_isSharedCheck_3733_;
                            state = 5;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___y_3711_);
                        v_a_3735_ = crate::leanh::lean_ctor_get(v___x_3726_, 0);
                        v_isSharedCheck_3742_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3726_)) as u8;
                        if v_isSharedCheck_3742_ == 0 {
                            v___x_3737_ = v___x_3726_;
                            v_isShared_3738_ = v_isSharedCheck_3742_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3735_);
                            crate::leanh::lean_dec(v___x_3726_);
                            v___x_3737_ = crate::leanh::lean_box(0);
                            v_isShared_3738_ = v_isSharedCheck_3742_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            4 => {
                return v___x_3720_;
            }
            5 => {
                if v_isShared_3729_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3728_, 1);
                    crate::leanh::lean_ctor_set(v___x_3728_, 0, v___y_3711_);
                    v___x_3731_ = v___x_3728_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3732_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3732_, 0, v___y_3711_);
                    v___x_3731_ = v_reuseFailAlloc_3732_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3731_;
            }
            7 => {
                if v_isShared_3738_ == 0 {
                    v___x_3740_ = v___x_3737_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3741_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3741_, 0, v_a_3735_);
                    v___x_3740_ = v_reuseFailAlloc_3741_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3740_;
            }
            9 => {
                v___x_3747_ = l_Lean_Exception_isInterrupt(v_a_3746_);
                if v___x_3747_ == 0 {
                    crate::leanh::lean_inc_ref(v_a_3746_);
                    v___x_3748_ = l_Lean_Exception_isRuntime(v_a_3746_);
                    v___y_3710_ = v___y_3745_;
                    v___y_3711_ = v_a_3746_;
                    v___y_3712_ = v___x_3748_;
                    state = 2;
                    continue;
                } else {
                    v___y_3710_ = v___y_3745_;
                    v___y_3711_ = v_a_3746_;
                    v___y_3712_ = v___x_3747_;
                    state = 2;
                    continue;
                }
            }
            10 => {
                if crate::leanh::lean_obj_tag(v___y_3750_) == 0 {
                    return v___y_3750_;
                } else {
                    v_a_3751_ = crate::leanh::lean_ctor_get(v___y_3750_, 0);
                    crate::leanh::lean_inc(v_a_3751_);
                    v___y_3745_ = v___y_3750_;
                    v_a_3746_ = v_a_3751_;
                    state = 9;
                    continue;
                }
            }
            11 => {
                if v___y_3755_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_3754_);
                    v___x_3756_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__0(v___x_3708_, v___y_3686_, v___y_3687_, v___y_3688_, v___y_3689_);
                    v_a_3757_ = crate::leanh::lean_ctor_get(v___x_3756_, 0);
                    v_isSharedCheck_3786_ = (!crate::leanh::lean_is_exclusive(v___x_3756_)) as u8;
                    if v_isSharedCheck_3786_ == 0 {
                        v___x_3759_ = v___x_3756_;
                        v_isShared_3760_ = v_isSharedCheck_3786_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3757_);
                        crate::leanh::lean_dec(v___x_3756_);
                        v___x_3759_ = crate::leanh::lean_box(0);
                        v_isShared_3760_ = v_isSharedCheck_3786_;
                        state = 12;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_3753_);
                    return v___y_3754_;
                }
            }
            12 => {
                v___x_3761_ = (crate::leanh::lean_unbox(v_a_3757_) as u8);
                crate::leanh::lean_dec(v_a_3757_);
                if v___x_3761_ == 0 {
                    if v_isShared_3760_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_3759_, 1);
                        crate::leanh::lean_ctor_set(v___x_3759_, 0, v___y_3753_);
                        v___x_3763_ = v___x_3759_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_3764_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3764_, 0, v___y_3753_);
                        v___x_3763_ = v_reuseFailAlloc_3764_;
                        state = 13;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3759_);
                    v___x_3765_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__1), core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__1_once), _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__1);
                    crate::leanh::lean_inc_ref(v___y_3753_);
                    v___x_3766_ = l_Lean_Exception_toMessageData(v___y_3753_);
                    v___x_3767_ = l_Lean_indentD(v___x_3766_);
                    v___x_3768_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3768_, 0, v___x_3765_);
                    crate::leanh::lean_ctor_set(v___x_3768_, 1, v___x_3767_);
                    v___x_3769_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(
                        v___x_3708_,
                        v___x_3768_,
                        v___y_3686_,
                        v___y_3687_,
                        v___y_3688_,
                        v___y_3689_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3769_) == 0 {
                        v_isSharedCheck_3776_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3769_)) as u8;
                        if v_isSharedCheck_3776_ == 0 {
                            v_unused_3777_ = crate::leanh::lean_ctor_get(v___x_3769_, 0);
                            crate::leanh::lean_dec(v_unused_3777_);
                            v___x_3771_ = v___x_3769_;
                            v_isShared_3772_ = v_isSharedCheck_3776_;
                            state = 14;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_3769_);
                            v___x_3771_ = crate::leanh::lean_box(0);
                            v_isShared_3772_ = v_isSharedCheck_3776_;
                            state = 14;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___y_3753_);
                        v_a_3778_ = crate::leanh::lean_ctor_get(v___x_3769_, 0);
                        v_isSharedCheck_3785_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3769_)) as u8;
                        if v_isSharedCheck_3785_ == 0 {
                            v___x_3780_ = v___x_3769_;
                            v_isShared_3781_ = v_isSharedCheck_3785_;
                            state = 16;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3778_);
                            crate::leanh::lean_dec(v___x_3769_);
                            v___x_3780_ = crate::leanh::lean_box(0);
                            v_isShared_3781_ = v_isSharedCheck_3785_;
                            state = 16;
                            continue;
                        }
                    }
                }
            }
            13 => {
                return v___x_3763_;
            }
            14 => {
                if v_isShared_3772_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3771_, 1);
                    crate::leanh::lean_ctor_set(v___x_3771_, 0, v___y_3753_);
                    v___x_3774_ = v___x_3771_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3775_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3775_, 0, v___y_3753_);
                    v___x_3774_ = v_reuseFailAlloc_3775_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_3774_;
            }
            16 => {
                if v_isShared_3781_ == 0 {
                    v___x_3783_ = v___x_3780_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_3784_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3784_, 0, v_a_3778_);
                    v___x_3783_ = v_reuseFailAlloc_3784_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_3783_;
            }
            18 => {
                v___x_3790_ = l_Lean_Exception_isInterrupt(v_a_3789_);
                if v___x_3790_ == 0 {
                    crate::leanh::lean_inc_ref(v_a_3789_);
                    v___x_3791_ = l_Lean_Exception_isRuntime(v_a_3789_);
                    v___y_3753_ = v_a_3789_;
                    v___y_3754_ = v___y_3788_;
                    v___y_3755_ = v___x_3791_;
                    state = 11;
                    continue;
                } else {
                    v___y_3753_ = v_a_3789_;
                    v___y_3754_ = v___y_3788_;
                    v___y_3755_ = v___x_3790_;
                    state = 11;
                    continue;
                }
            }
            19 => {
                v___x_3799_ = lean_array_get(v___x_3707_, v_x_3684_, v___y_3794_);
                crate::leanh::lean_dec(v___y_3794_);
                crate::leanh::lean_dec_ref(v_x_3684_);
                v___x_3800_ = l_Lean_Expr_fvarId_x21(v___x_3799_);
                crate::leanh::lean_dec(v___x_3799_);
                v___x_3801_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__0;
                if v_isShared_3704_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3703_, 0, v___y_3793_);
                    v___x_3803_ = v___x_3703_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3818_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3818_, 0, v___y_3793_);
                    v___x_3803_ = v_reuseFailAlloc_3818_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                v___x_3804_ = l_Lean_MVarId_cases(
                    v_mvarId_3682_,
                    v___x_3800_,
                    v___x_3801_,
                    v_hasTrace_3706_,
                    v___x_3803_,
                    v___y_3795_,
                    v___y_3796_,
                    v___y_3797_,
                    v___y_3798_,
                );
                if crate::leanh::lean_obj_tag(v___x_3804_) == 0 {
                    v_a_3805_ = crate::leanh::lean_ctor_get(v___x_3804_, 0);
                    crate::leanh::lean_inc(v_a_3805_);
                    crate::leanh::lean_dec_ref_known(v___x_3804_, 1);
                    v_sz_3806_ = lean_array_size(v_a_3805_);
                    v___x_3807_ = 0usize;
                    v___x_3808_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3(v_declName_3697_, v_val_3701_, v_hasTrace_3706_, v_sz_3806_, v___x_3807_, v_a_3805_, v___y_3795_, v___y_3796_, v___y_3797_, v___y_3798_);
                    if crate::leanh::lean_obj_tag(v___x_3808_) == 0 {
                        return v___x_3808_;
                    } else {
                        v_a_3809_ = crate::leanh::lean_ctor_get(v___x_3808_, 0);
                        crate::leanh::lean_inc(v_a_3809_);
                        v___y_3788_ = v___x_3808_;
                        v_a_3789_ = v_a_3809_;
                        state = 18;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_val_3701_);
                    crate::leanh::lean_dec(v_declName_3697_);
                    v_a_3810_ = crate::leanh::lean_ctor_get(v___x_3804_, 0);
                    v_isSharedCheck_3817_ = (!crate::leanh::lean_is_exclusive(v___x_3804_)) as u8;
                    if v_isSharedCheck_3817_ == 0 {
                        v___x_3812_ = v___x_3804_;
                        v_isShared_3813_ = v_isSharedCheck_3817_;
                        state = 21;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3810_);
                        crate::leanh::lean_dec(v___x_3804_);
                        v___x_3812_ = crate::leanh::lean_box(0);
                        v_isShared_3813_ = v_isSharedCheck_3817_;
                        state = 21;
                        continue;
                    }
                }
            }
            21 => {
                crate::leanh::lean_inc(v_a_3810_);
                if v_isShared_3813_ == 0 {
                    v___x_3815_ = v___x_3812_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_3816_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3816_, 0, v_a_3810_);
                    v___x_3815_ = v_reuseFailAlloc_3816_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                v___y_3788_ = v___x_3815_;
                v_a_3789_ = v_a_3810_;
                state = 18;
                continue;
            }
            23 => {
                v___x_3827_ = lean_array_get_borrowed(v___x_3707_, v_x_3684_, v_majorPos_3819_);
                v___x_3828_ = l_Lean_Expr_isFVar(v___x_3827_);
                if v___x_3828_ == 0 {
                    crate::leanh::lean_inc(v___x_3827_);
                    crate::leanh::lean_del_object(v___x_3703_);
                    crate::leanh::lean_dec(v_val_3701_);
                    crate::leanh::lean_dec(v_declName_3697_);
                    crate::leanh::lean_dec_ref(v_x_3684_);
                    crate::leanh::lean_dec(v_mvarId_3682_);
                    v___x_3829_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__2), core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__2_once), _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__2);
                    v___x_3830_ = l_Lean_indentExpr(v___x_3827_);
                    v___x_3831_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3831_, 0, v___x_3829_);
                    crate::leanh::lean_ctor_set(v___x_3831_, 1, v___x_3830_);
                    v___x_3832_ =
                        l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(
                            v___x_3831_,
                            v___y_3823_,
                            v___y_3824_,
                            v___y_3825_,
                            v___y_3826_,
                        );
                    v_a_3833_ = crate::leanh::lean_ctor_get(v___x_3832_, 0);
                    v_isSharedCheck_3840_ = (!crate::leanh::lean_is_exclusive(v___x_3832_)) as u8;
                    if v_isSharedCheck_3840_ == 0 {
                        v___x_3835_ = v___x_3832_;
                        v_isShared_3836_ = v_isSharedCheck_3840_;
                        state = 24;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3833_);
                        crate::leanh::lean_dec(v___x_3832_);
                        v___x_3835_ = crate::leanh::lean_box(0);
                        v_isShared_3836_ = v_isSharedCheck_3840_;
                        state = 24;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc(v_majorPos_3819_);
                    crate::leanh::lean_inc_ref(v_insterestingCtors_3821_);
                    v___y_3793_ = v_insterestingCtors_3821_;
                    v___y_3794_ = v_majorPos_3819_;
                    v___y_3795_ = v___y_3823_;
                    v___y_3796_ = v___y_3824_;
                    v___y_3797_ = v___y_3825_;
                    v___y_3798_ = v___y_3826_;
                    state = 19;
                    continue;
                }
            }
            24 => {
                crate::leanh::lean_inc(v_a_3833_);
                if v_isShared_3836_ == 0 {
                    v___x_3838_ = v___x_3835_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_3839_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3839_, 0, v_a_3833_);
                    v___x_3838_ = v_reuseFailAlloc_3839_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                v___y_3788_ = v___x_3838_;
                v_a_3789_ = v_a_3833_;
                state = 18;
                continue;
            }
            26 => {
                crate::leanh::lean_inc(v_a_3845_);
                if v_isShared_3848_ == 0 {
                    v___x_3850_ = v___x_3847_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_3851_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3851_, 0, v_a_3845_);
                    v___x_3850_ = v_reuseFailAlloc_3851_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                v___y_3788_ = v___x_3850_;
                v_a_3789_ = v_a_3845_;
                state = 18;
                continue;
            }
            28 => {
                v___x_3861_ = lean_io_mono_nanos_now();
                v___x_3862_ = lean_float_of_nat(v___y_3859_);
                v___x_3863_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__10), core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__10_once), _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__10);
                v___x_3864_ = lean_float_div(v___x_3862_, v___x_3863_);
                v___x_3865_ = lean_float_of_nat(v___x_3861_);
                v___x_3866_ = lean_float_div(v___x_3865_, v___x_3863_);
                v___x_3867_ = crate::leanh::lean_box_float(v___x_3864_);
                v___x_3868_ = crate::leanh::lean_box_float(v___x_3866_);
                v___x_3869_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3869_, 0, v___x_3867_);
                crate::leanh::lean_ctor_set(v___x_3869_, 1, v___x_3868_);
                v___x_3870_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3870_, 0, v_a_3860_);
                crate::leanh::lean_ctor_set(v___x_3870_, 1, v___x_3869_);
                v___x_3871_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6(v___x_3708_, v_hasTrace_3706_, v___x_3854_, v_options_3700_, v___x_3856_, v___y_3858_, v___f_3853_, v___x_3870_, v___y_3686_, v___y_3687_, v___y_3688_, v___y_3689_);
                return v___x_3871_;
            }
            29 => {
                v___x_3876_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3876_, 0, v_a_3875_);
                v___y_3858_ = v___y_3873_;
                v___y_3859_ = v___y_3874_;
                v_a_3860_ = v___x_3876_;
                state = 28;
                continue;
            }
            30 => {
                if v___y_3881_ == 0 {
                    v___x_3882_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__0(v___x_3708_, v___y_3686_, v___y_3687_, v___y_3688_, v___y_3689_);
                    v_a_3883_ = crate::leanh::lean_ctor_get(v___x_3882_, 0);
                    crate::leanh::lean_inc(v_a_3883_);
                    crate::leanh::lean_dec_ref(v___x_3882_);
                    v___x_3884_ = (crate::leanh::lean_unbox(v_a_3883_) as u8);
                    crate::leanh::lean_dec(v_a_3883_);
                    if v___x_3884_ == 0 {
                        v___y_3873_ = v___y_3878_;
                        v___y_3874_ = v___y_3879_;
                        v_a_3875_ = v___y_3880_;
                        state = 29;
                        continue;
                    } else {
                        v___x_3885_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__1), core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__1_once), _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__1);
                        crate::leanh::lean_inc_ref(v___y_3880_);
                        v___x_3886_ = l_Lean_Exception_toMessageData(v___y_3880_);
                        v___x_3887_ = l_Lean_indentD(v___x_3886_);
                        v___x_3888_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3888_, 0, v___x_3885_);
                        crate::leanh::lean_ctor_set(v___x_3888_, 1, v___x_3887_);
                        v___x_3889_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(
                            v___x_3708_,
                            v___x_3888_,
                            v___y_3686_,
                            v___y_3687_,
                            v___y_3688_,
                            v___y_3689_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3889_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_3889_, 1);
                            v___y_3873_ = v___y_3878_;
                            v___y_3874_ = v___y_3879_;
                            v_a_3875_ = v___y_3880_;
                            state = 29;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v___y_3880_);
                            v_a_3890_ = crate::leanh::lean_ctor_get(v___x_3889_, 0);
                            crate::leanh::lean_inc(v_a_3890_);
                            crate::leanh::lean_dec_ref_known(v___x_3889_, 1);
                            v___y_3873_ = v___y_3878_;
                            v___y_3874_ = v___y_3879_;
                            v_a_3875_ = v_a_3890_;
                            state = 29;
                            continue;
                        }
                    }
                } else {
                    v___y_3873_ = v___y_3878_;
                    v___y_3874_ = v___y_3879_;
                    v_a_3875_ = v___y_3880_;
                    state = 29;
                    continue;
                }
            }
            31 => {
                v___x_3895_ = l_Lean_Exception_isInterrupt(v_a_3894_);
                if v___x_3895_ == 0 {
                    crate::leanh::lean_inc_ref(v_a_3894_);
                    v___x_3896_ = l_Lean_Exception_isRuntime(v_a_3894_);
                    v___y_3878_ = v___y_3892_;
                    v___y_3879_ = v___y_3893_;
                    v___y_3880_ = v_a_3894_;
                    v___y_3881_ = v___x_3896_;
                    state = 30;
                    continue;
                } else {
                    v___y_3878_ = v___y_3892_;
                    v___y_3879_ = v___y_3893_;
                    v___y_3880_ = v_a_3894_;
                    v___y_3881_ = v___x_3895_;
                    state = 30;
                    continue;
                }
            }
            32 => {
                if crate::leanh::lean_obj_tag(v___y_3900_) == 0 {
                    v_a_3901_ = crate::leanh::lean_ctor_get(v___y_3900_, 0);
                    v_isSharedCheck_3908_ = (!crate::leanh::lean_is_exclusive(v___y_3900_)) as u8;
                    if v_isSharedCheck_3908_ == 0 {
                        v___x_3903_ = v___y_3900_;
                        v_isShared_3904_ = v_isSharedCheck_3908_;
                        state = 33;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3901_);
                        crate::leanh::lean_dec(v___y_3900_);
                        v___x_3903_ = crate::leanh::lean_box(0);
                        v_isShared_3904_ = v_isSharedCheck_3908_;
                        state = 33;
                        continue;
                    }
                } else {
                    v_a_3909_ = crate::leanh::lean_ctor_get(v___y_3900_, 0);
                    crate::leanh::lean_inc(v_a_3909_);
                    crate::leanh::lean_dec_ref_known(v___y_3900_, 1);
                    v___y_3892_ = v___y_3898_;
                    v___y_3893_ = v___y_3899_;
                    v_a_3894_ = v_a_3909_;
                    state = 31;
                    continue;
                }
            }
            33 => {
                if v_isShared_3904_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3903_, 1);
                    v___x_3906_ = v___x_3903_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_3907_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3907_, 0, v_a_3901_);
                    v___x_3906_ = v_reuseFailAlloc_3907_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                v___y_3858_ = v___y_3898_;
                v___y_3859_ = v___y_3899_;
                v_a_3860_ = v___x_3906_;
                state = 28;
                continue;
            }
            35 => {
                v___x_3914_ = lean_io_get_num_heartbeats();
                v___x_3915_ = lean_float_of_nat(v___y_3912_);
                v___x_3916_ = lean_float_of_nat(v___x_3914_);
                v___x_3917_ = crate::leanh::lean_box_float(v___x_3915_);
                v___x_3918_ = crate::leanh::lean_box_float(v___x_3916_);
                v___x_3919_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3919_, 0, v___x_3917_);
                crate::leanh::lean_ctor_set(v___x_3919_, 1, v___x_3918_);
                v___x_3920_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3920_, 0, v_a_3913_);
                crate::leanh::lean_ctor_set(v___x_3920_, 1, v___x_3919_);
                v___x_3921_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6(v___x_3708_, v_hasTrace_3706_, v___x_3854_, v_options_3700_, v___x_3856_, v___y_3911_, v___f_3853_, v___x_3920_, v___y_3686_, v___y_3687_, v___y_3688_, v___y_3689_);
                return v___x_3921_;
            }
            36 => {
                v___x_3926_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3926_, 0, v_a_3925_);
                v___y_3911_ = v___y_3923_;
                v___y_3912_ = v___y_3924_;
                v_a_3913_ = v___x_3926_;
                state = 35;
                continue;
            }
            37 => {
                if v___y_3931_ == 0 {
                    v___x_3932_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__0(v___x_3708_, v___y_3686_, v___y_3687_, v___y_3688_, v___y_3689_);
                    v_a_3933_ = crate::leanh::lean_ctor_get(v___x_3932_, 0);
                    crate::leanh::lean_inc(v_a_3933_);
                    crate::leanh::lean_dec_ref(v___x_3932_);
                    v___x_3934_ = (crate::leanh::lean_unbox(v_a_3933_) as u8);
                    crate::leanh::lean_dec(v_a_3933_);
                    if v___x_3934_ == 0 {
                        v___y_3923_ = v___y_3929_;
                        v___y_3924_ = v___y_3930_;
                        v_a_3925_ = v___y_3928_;
                        state = 36;
                        continue;
                    } else {
                        v___x_3935_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__1), core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__1_once), _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__1);
                        crate::leanh::lean_inc_ref(v___y_3928_);
                        v___x_3936_ = l_Lean_Exception_toMessageData(v___y_3928_);
                        v___x_3937_ = l_Lean_indentD(v___x_3936_);
                        v___x_3938_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3938_, 0, v___x_3935_);
                        crate::leanh::lean_ctor_set(v___x_3938_, 1, v___x_3937_);
                        v___x_3939_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(
                            v___x_3708_,
                            v___x_3938_,
                            v___y_3686_,
                            v___y_3687_,
                            v___y_3688_,
                            v___y_3689_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3939_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_3939_, 1);
                            v___y_3923_ = v___y_3929_;
                            v___y_3924_ = v___y_3930_;
                            v_a_3925_ = v___y_3928_;
                            state = 36;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v___y_3928_);
                            v_a_3940_ = crate::leanh::lean_ctor_get(v___x_3939_, 0);
                            crate::leanh::lean_inc(v_a_3940_);
                            crate::leanh::lean_dec_ref_known(v___x_3939_, 1);
                            v___y_3923_ = v___y_3929_;
                            v___y_3924_ = v___y_3930_;
                            v_a_3925_ = v_a_3940_;
                            state = 36;
                            continue;
                        }
                    }
                } else {
                    v___y_3923_ = v___y_3929_;
                    v___y_3924_ = v___y_3930_;
                    v_a_3925_ = v___y_3928_;
                    state = 36;
                    continue;
                }
            }
            38 => {
                v___x_3945_ = l_Lean_Exception_isInterrupt(v_a_3944_);
                if v___x_3945_ == 0 {
                    crate::leanh::lean_inc_ref(v_a_3944_);
                    v___x_3946_ = l_Lean_Exception_isRuntime(v_a_3944_);
                    v___y_3928_ = v_a_3944_;
                    v___y_3929_ = v___y_3942_;
                    v___y_3930_ = v___y_3943_;
                    v___y_3931_ = v___x_3946_;
                    state = 37;
                    continue;
                } else {
                    v___y_3928_ = v_a_3944_;
                    v___y_3929_ = v___y_3942_;
                    v___y_3930_ = v___y_3943_;
                    v___y_3931_ = v___x_3945_;
                    state = 37;
                    continue;
                }
            }
            39 => {
                if crate::leanh::lean_obj_tag(v___y_3950_) == 0 {
                    v_a_3951_ = crate::leanh::lean_ctor_get(v___y_3950_, 0);
                    v_isSharedCheck_3958_ = (!crate::leanh::lean_is_exclusive(v___y_3950_)) as u8;
                    if v_isSharedCheck_3958_ == 0 {
                        v___x_3953_ = v___y_3950_;
                        v_isShared_3954_ = v_isSharedCheck_3958_;
                        state = 40;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3951_);
                        crate::leanh::lean_dec(v___y_3950_);
                        v___x_3953_ = crate::leanh::lean_box(0);
                        v_isShared_3954_ = v_isSharedCheck_3958_;
                        state = 40;
                        continue;
                    }
                } else {
                    v_a_3959_ = crate::leanh::lean_ctor_get(v___y_3950_, 0);
                    crate::leanh::lean_inc(v_a_3959_);
                    crate::leanh::lean_dec_ref_known(v___y_3950_, 1);
                    v___y_3942_ = v___y_3948_;
                    v___y_3943_ = v___y_3949_;
                    v_a_3944_ = v_a_3959_;
                    state = 38;
                    continue;
                }
            }
            40 => {
                if v_isShared_3954_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3953_, 1);
                    v___x_3956_ = v___x_3953_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_3957_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3957_, 0, v_a_3951_);
                    v___x_3956_ = v_reuseFailAlloc_3957_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                v___y_3911_ = v___y_3948_;
                v___y_3912_ = v___y_3949_;
                v_a_3913_ = v___x_3956_;
                state = 35;
                continue;
            }
            42 => {
                v___x_3961_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg(v___y_3689_);
                v_a_3962_ = crate::leanh::lean_ctor_get(v___x_3961_, 0);
                v_isSharedCheck_3992_ = (!crate::leanh::lean_is_exclusive(v___x_3961_)) as u8;
                if v_isSharedCheck_3992_ == 0 {
                    v___x_3964_ = v___x_3961_;
                    v_isShared_3965_ = v_isSharedCheck_3992_;
                    state = 43;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3962_);
                    crate::leanh::lean_dec(v___x_3961_);
                    v___x_3964_ = crate::leanh::lean_box(0);
                    v_isShared_3965_ = v_isSharedCheck_3992_;
                    state = 43;
                    continue;
                }
            }
            43 => {
                v___x_3966_ = l_Lean_trace_profiler_useHeartbeats;
                v___x_3967_ = l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__5(
                    v_options_3700_,
                    v___x_3966_,
                );
                if v___x_3967_ == 0 {
                    v___x_3968_ = lean_io_mono_nanos_now();
                    if v___x_3856_ == 0 {
                        crate::leanh::lean_del_object(v___x_3964_);
                        v___x_3969_ = crate::leanh::lean_box(0);
                        v___x_3970_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__2(v_val_3701_, v___x_3707_, v_x_3684_, v_mvarId_3682_, v___x_3967_, v_declName_3697_, v___x_3969_, v___y_3686_, v___y_3687_, v___y_3688_, v___y_3689_);
                        crate::leanh::lean_dec_ref(v_x_3684_);
                        v___y_3898_ = v_a_3962_;
                        v___y_3899_ = v___x_3968_;
                        v___y_3900_ = v___x_3970_;
                        state = 32;
                        continue;
                    } else {
                        v___x_3971_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__3), core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__3_once), _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__3);
                        crate::leanh::lean_inc(v_mvarId_3682_);
                        if v_isShared_3965_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_3964_, 1);
                            crate::leanh::lean_ctor_set(v___x_3964_, 0, v_mvarId_3682_);
                            v___x_3973_ = v___x_3964_;
                            state = 44;
                            continue;
                        } else {
                            v_reuseFailAlloc_3979_ =
                                crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3979_, 0, v_mvarId_3682_);
                            v___x_3973_ = v_reuseFailAlloc_3979_;
                            state = 44;
                            continue;
                        }
                    }
                } else {
                    v___x_3980_ = lean_io_get_num_heartbeats();
                    if v___x_3856_ == 0 {
                        crate::leanh::lean_del_object(v___x_3964_);
                        v___x_3981_ = crate::leanh::lean_box(0);
                        v___x_3982_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1(v_val_3701_, v___x_3707_, v_x_3684_, v_mvarId_3682_, v_declName_3697_, v___x_3967_, v___x_3981_, v___y_3686_, v___y_3687_, v___y_3688_, v___y_3689_);
                        crate::leanh::lean_dec_ref(v_x_3684_);
                        v___y_3948_ = v_a_3962_;
                        v___y_3949_ = v___x_3980_;
                        v___y_3950_ = v___x_3982_;
                        state = 39;
                        continue;
                    } else {
                        v___x_3983_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__3), core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__3_once), _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__3);
                        crate::leanh::lean_inc(v_mvarId_3682_);
                        if v_isShared_3965_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_3964_, 1);
                            crate::leanh::lean_ctor_set(v___x_3964_, 0, v_mvarId_3682_);
                            v___x_3985_ = v___x_3964_;
                            state = 45;
                            continue;
                        } else {
                            v_reuseFailAlloc_3991_ =
                                crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3991_, 0, v_mvarId_3682_);
                            v___x_3985_ = v_reuseFailAlloc_3991_;
                            state = 45;
                            continue;
                        }
                    }
                }
            }
            44 => {
                v___x_3974_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3974_, 0, v___x_3971_);
                crate::leanh::lean_ctor_set(v___x_3974_, 1, v___x_3973_);
                v___x_3975_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(
                    v___x_3708_,
                    v___x_3974_,
                    v___y_3686_,
                    v___y_3687_,
                    v___y_3688_,
                    v___y_3689_,
                );
                if crate::leanh::lean_obj_tag(v___x_3975_) == 0 {
                    v_a_3976_ = crate::leanh::lean_ctor_get(v___x_3975_, 0);
                    crate::leanh::lean_inc(v_a_3976_);
                    crate::leanh::lean_dec_ref_known(v___x_3975_, 1);
                    v___x_3977_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__2(v_val_3701_, v___x_3707_, v_x_3684_, v_mvarId_3682_, v___x_3967_, v_declName_3697_, v_a_3976_, v___y_3686_, v___y_3687_, v___y_3688_, v___y_3689_);
                    crate::leanh::lean_dec_ref(v_x_3684_);
                    v___y_3898_ = v_a_3962_;
                    v___y_3899_ = v___x_3968_;
                    v___y_3900_ = v___x_3977_;
                    state = 32;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_3701_);
                    crate::leanh::lean_dec(v_declName_3697_);
                    crate::leanh::lean_dec_ref(v_x_3684_);
                    crate::leanh::lean_dec(v_mvarId_3682_);
                    v_a_3978_ = crate::leanh::lean_ctor_get(v___x_3975_, 0);
                    crate::leanh::lean_inc(v_a_3978_);
                    crate::leanh::lean_dec_ref_known(v___x_3975_, 1);
                    v___y_3892_ = v_a_3962_;
                    v___y_3893_ = v___x_3968_;
                    v_a_3894_ = v_a_3978_;
                    state = 31;
                    continue;
                }
            }
            45 => {
                v___x_3986_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3986_, 0, v___x_3983_);
                crate::leanh::lean_ctor_set(v___x_3986_, 1, v___x_3985_);
                v___x_3987_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(
                    v___x_3708_,
                    v___x_3986_,
                    v___y_3686_,
                    v___y_3687_,
                    v___y_3688_,
                    v___y_3689_,
                );
                if crate::leanh::lean_obj_tag(v___x_3987_) == 0 {
                    v_a_3988_ = crate::leanh::lean_ctor_get(v___x_3987_, 0);
                    crate::leanh::lean_inc(v_a_3988_);
                    crate::leanh::lean_dec_ref_known(v___x_3987_, 1);
                    v___x_3989_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1(v_val_3701_, v___x_3707_, v_x_3684_, v_mvarId_3682_, v_declName_3697_, v___x_3967_, v_a_3988_, v___y_3686_, v___y_3687_, v___y_3688_, v___y_3689_);
                    crate::leanh::lean_dec_ref(v_x_3684_);
                    v___y_3948_ = v_a_3962_;
                    v___y_3949_ = v___x_3980_;
                    v___y_3950_ = v___x_3989_;
                    state = 39;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_3701_);
                    crate::leanh::lean_dec(v_declName_3697_);
                    crate::leanh::lean_dec_ref(v_x_3684_);
                    crate::leanh::lean_dec(v_mvarId_3682_);
                    v_a_3990_ = crate::leanh::lean_ctor_get(v___x_3987_, 0);
                    crate::leanh::lean_inc(v_a_3990_);
                    crate::leanh::lean_dec_ref_known(v___x_3987_, 1);
                    v___y_3942_ = v_a_3962_;
                    v___y_3943_ = v___x_3980_;
                    v_a_3944_ = v_a_3990_;
                    state = 38;
                    continue;
                }
            }
            46 => {
                crate::leanh::lean_inc(v_a_4003_);
                if v_isShared_4006_ == 0 {
                    v___x_4008_ = v___x_4005_;
                    state = 47;
                    continue;
                } else {
                    v_reuseFailAlloc_4009_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4009_, 0, v_a_4003_);
                    v___x_4008_ = v_reuseFailAlloc_4009_;
                    state = 47;
                    continue;
                }
            }
            47 => {
                v___y_3745_ = v___x_4008_;
                v_a_3746_ = v_a_4003_;
                state = 9;
                continue;
            }
            48 => {
                if v_isShared_4017_ == 0 {
                    v___x_4019_ = v___x_4016_;
                    state = 49;
                    continue;
                } else {
                    v_reuseFailAlloc_4020_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4020_, 0, v_a_4014_);
                    v___x_4019_ = v_reuseFailAlloc_4020_;
                    state = 49;
                    continue;
                }
            }
            49 => {
                return v___x_4019_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___boxed(
    mut v_mvarId_4024_: *mut crate::leanh::LeanObject,
    mut v_x_4025_: *mut crate::leanh::LeanObject,
    mut v_x_4026_: *mut crate::leanh::LeanObject,
    mut v_x_4027_: *mut crate::leanh::LeanObject,
    mut v___y_4028_: *mut crate::leanh::LeanObject,
    mut v___y_4029_: *mut crate::leanh::LeanObject,
    mut v___y_4030_: *mut crate::leanh::LeanObject,
    mut v___y_4031_: *mut crate::leanh::LeanObject,
    mut v___y_4032_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4033_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5(
        v_mvarId_4024_,
        v_x_4025_,
        v_x_4026_,
        v_x_4027_,
        v___y_4028_,
        v___y_4029_,
        v___y_4030_,
        v___y_4031_,
    );
    crate::leanh::lean_dec(v___y_4031_);
    crate::leanh::lean_dec_ref(v___y_4030_);
    crate::leanh::lean_dec(v___y_4029_);
    crate::leanh::lean_dec_ref(v___y_4028_);
    return v_res_4033_;
}
pub unsafe fn l_Lean_Meta_splitSparseCasesOn(
    mut v_mvarId_4034_: *mut crate::leanh::LeanObject,
    mut v_a_4035_: *mut crate::leanh::LeanObject,
    mut v_a_4036_: *mut crate::leanh::LeanObject,
    mut v_a_4037_: *mut crate::leanh::LeanObject,
    mut v_a_4038_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_4046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_4047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4057_: u8 = 0;
    let mut v___x_4059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4061_: u8 = 0;
    let mut v_a_4062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4065_: u8 = 0;
    let mut v___x_4067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4069_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_mvarId_4034_);
                v___x_4040_ = l_Lean_MVarId_getType(
                    v_mvarId_4034_,
                    v_a_4035_,
                    v_a_4036_,
                    v_a_4037_,
                    v_a_4038_,
                );
                if crate::leanh::lean_obj_tag(v___x_4040_) == 0 {
                    v_a_4041_ = crate::leanh::lean_ctor_get(v___x_4040_, 0);
                    crate::leanh::lean_inc(v_a_4041_);
                    crate::leanh::lean_dec_ref_known(v___x_4040_, 1);
                    v___x_4042_ = l_Lean_Meta_matchEqHEqLHS_x3f(
                        v_a_4041_, v_a_4035_, v_a_4036_, v_a_4037_, v_a_4038_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4042_) == 0 {
                        v_a_4043_ = crate::leanh::lean_ctor_get(v___x_4042_, 0);
                        crate::leanh::lean_inc(v_a_4043_);
                        crate::leanh::lean_dec_ref_known(v___x_4042_, 1);
                        if crate::leanh::lean_obj_tag(v_a_4043_) == 1 {
                            v_val_4044_ = crate::leanh::lean_ctor_get(v_a_4043_, 0);
                            crate::leanh::lean_inc(v_val_4044_);
                            crate::leanh::lean_dec_ref_known(v_a_4043_, 1);
                            v_snd_4045_ = crate::leanh::lean_ctor_get(v_val_4044_, 1);
                            crate::leanh::lean_inc(v_snd_4045_);
                            crate::leanh::lean_dec(v_val_4044_);
                            v_dummy_4046_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0), core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0_once), _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0);
                            v_nargs_4047_ = l_Lean_Expr_getAppNumArgs(v_snd_4045_);
                            crate::leanh::lean_inc(v_nargs_4047_);
                            v___x_4048_ = lean_mk_array(v_nargs_4047_, v_dummy_4046_);
                            v___x_4049_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_4050_ = lean_nat_sub(v_nargs_4047_, v___x_4049_);
                            crate::leanh::lean_dec(v_nargs_4047_);
                            v___x_4051_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5(v_mvarId_4034_, v_snd_4045_, v___x_4048_, v___x_4050_, v_a_4035_, v_a_4036_, v_a_4037_, v_a_4038_);
                            return v___x_4051_;
                        } else {
                            crate::leanh::lean_dec(v_a_4043_);
                            crate::leanh::lean_dec(v_mvarId_4034_);
                            v___x_4052_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_reduceSparseCasesOn___closed__1
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_reduceSparseCasesOn___closed__1_once
                                ),
                                _init_l_Lean_Meta_reduceSparseCasesOn___closed__1,
                            );
                            v___x_4053_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_4052_, v_a_4035_, v_a_4036_, v_a_4037_, v_a_4038_);
                            return v___x_4053_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_mvarId_4034_);
                        v_a_4054_ = crate::leanh::lean_ctor_get(v___x_4042_, 0);
                        v_isSharedCheck_4061_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4042_)) as u8;
                        if v_isSharedCheck_4061_ == 0 {
                            v___x_4056_ = v___x_4042_;
                            v_isShared_4057_ = v_isSharedCheck_4061_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4054_);
                            crate::leanh::lean_dec(v___x_4042_);
                            v___x_4056_ = crate::leanh::lean_box(0);
                            v_isShared_4057_ = v_isSharedCheck_4061_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_mvarId_4034_);
                    v_a_4062_ = crate::leanh::lean_ctor_get(v___x_4040_, 0);
                    v_isSharedCheck_4069_ = (!crate::leanh::lean_is_exclusive(v___x_4040_)) as u8;
                    if v_isSharedCheck_4069_ == 0 {
                        v___x_4064_ = v___x_4040_;
                        v_isShared_4065_ = v_isSharedCheck_4069_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4062_);
                        crate::leanh::lean_dec(v___x_4040_);
                        v___x_4064_ = crate::leanh::lean_box(0);
                        v_isShared_4065_ = v_isSharedCheck_4069_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4057_ == 0 {
                    v___x_4059_ = v___x_4056_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4060_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4060_, 0, v_a_4054_);
                    v___x_4059_ = v_reuseFailAlloc_4060_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4059_;
            }
            3 => {
                if v_isShared_4065_ == 0 {
                    v___x_4067_ = v___x_4064_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4068_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4068_, 0, v_a_4062_);
                    v___x_4067_ = v_reuseFailAlloc_4068_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4067_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_splitSparseCasesOn___boxed(
    mut v_mvarId_4070_: *mut crate::leanh::LeanObject,
    mut v_a_4071_: *mut crate::leanh::LeanObject,
    mut v_a_4072_: *mut crate::leanh::LeanObject,
    mut v_a_4073_: *mut crate::leanh::LeanObject,
    mut v_a_4074_: *mut crate::leanh::LeanObject,
    mut v_a_4075_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4076_ =
        l_Lean_Meta_splitSparseCasesOn(v_mvarId_4070_, v_a_4071_, v_a_4072_, v_a_4073_, v_a_4074_);
    crate::leanh::lean_dec(v_a_4074_);
    crate::leanh::lean_dec_ref(v_a_4073_);
    crate::leanh::lean_dec(v_a_4072_);
    crate::leanh::lean_dec_ref(v_a_4071_);
    return v_res_4076_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_SplitSparseCasesOn(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Rewrite(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Constructions_SparseCasesOn(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Constructions_SparseCasesOnEq(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_HasNotBit(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Cases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Replace(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_SplitSparseCasesOn(
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
pub unsafe fn initialize_Lean_Meta_SplitSparseCasesOn(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Rewrite(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Constructions_SparseCasesOn(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Constructions_SparseCasesOnEq(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_HasNotBit(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Cases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Replace(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_SplitSparseCasesOn(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_SplitSparseCasesOn(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_SplitSparseCasesOn(builtin);
}
