// Lean compiler output
// Module: Lean.Meta.Tactic.LibrarySearch
// Imports: Lean.Meta.LazyDiscrTree Lean.Meta.Tactic.SolveByElim Lean.Meta.Tactic.Grind.Main Lean.Util.Heartbeats Init.Grind.Util Init.Try Lean.Elab.Tactic.Basic Init.Omega
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::List::Basic::l_List_isEmpty___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Grind::Util::{
    initialize_Init_Grind_Util, runtime_initialize_Init_Grind_Util,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::{
    l_Array_extract___redArg, l_Array_mkArray0, l_Lean_Name_append, l_Lean_Name_num___override,
    l_Lean_Name_str___override, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_node1,
    l_Lean_Syntax_node2, l_Lean_replaceRef,
};
use crate::r#gen::Init::Try::{initialize_Init_Try, runtime_initialize_Init_Try};
use crate::r#gen::Lean::CoreM::l_Lean_Exception_isRuntime;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isMetaprogramming;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::PersistentArray::{
    l_Lean_PersistentArray_append___redArg, l_Lean_PersistentArray_push___redArg,
    l_Lean_PersistentArray_toArray___redArg,
};
use crate::r#gen::Lean::Declaration::l_Lean_ConstantInfo_type;
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    initialize_Lean_Elab_Tactic_Basic, l_Lean_Elab_Tactic_evalTactic___boxed,
    l_Lean_Elab_Tactic_run___boxed, l_Lean_Elab_Tactic_withSuppressedMessages___boxed,
    runtime_initialize_Lean_Elab_Tactic_Basic,
};
use crate::r#gen::Lean::Elab::Term::TermElabM::l_Lean_Elab_Term_TermElabM_run___redArg;
use crate::r#gen::Lean::Environment::{
    l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg,
    l_Lean_registerEnvExtension___redArg,
};
use crate::r#gen::Lean::Exception::l_Lean_Exception_isInterrupt;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_const___override, l_Lean_Expr_hasMVar, l_Lean_mkConst,
};
use crate::r#gen::Lean::InternalExceptionId::{
    l_Lean_instBEqInternalExceptionId_beq, l_Lean_registerInternalExceptionId,
};
use crate::r#gen::Lean::Linter::Deprecated::l_Lean_Linter_isDeprecated;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofName,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::AppBuilder::l_Lean_Meta_mkAppM;
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux,
    l_Lean_Meta_Context_config, l_Lean_Meta_SavedState_restore___redArg,
    l_Lean_Meta_mapForallTelescope, l_Lean_Meta_mkConstWithFreshMVarLevels,
    l_Lean_Meta_saveState___redArg,
};
use crate::r#gen::Lean::Meta::InferType::l_Lean_Meta_getLevel;
use crate::r#gen::Lean::Meta::LazyDiscrTree::{
    initialize_Lean_Meta_LazyDiscrTree, l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg,
    l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg,
    l_Lean_Meta_LazyDiscrTree_findMatches___redArg, l_Lean_Meta_LazyDiscrTree_instBEqKey_beq,
    runtime_initialize_Lean_Meta_LazyDiscrTree,
};
use crate::r#gen::Lean::Meta::Tactic::Apply::l_Lean_MVarId_apply;
use crate::r#gen::Lean::Meta::Tactic::Grind::Main::{
    initialize_Lean_Meta_Tactic_Grind_Main, l_Lean_Meta_Grind_Result_hasFailed,
    l_Lean_Meta_Grind_main, l_Lean_Meta_Grind_mkDefaultParams,
    runtime_initialize_Lean_Meta_Tactic_Grind_Main,
};
use crate::r#gen::Lean::Meta::Tactic::SolveByElim::{
    initialize_Lean_Meta_Tactic_SolveByElim,
    l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll,
    l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge,
    l_Lean_Meta_SolveByElim_mkAssumptionSet, l_Lean_Meta_SolveByElim_solveByElim,
    runtime_initialize_Lean_Meta_Tactic_SolveByElim,
};
use crate::r#gen::Lean::Meta::Tactic::Symm::l_Lean_MVarId_applySymm___boxed;
use crate::r#gen::Lean::Meta::Tactic::Util::l_Lean_MVarId_getType;
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Lean::Util::Heartbeats::{
    initialize_Lean_Util_Heartbeats, l_Lean_getMaxHeartbeats___redArg,
    l_Lean_getRemainingHeartbeats___redArg, runtime_initialize_Lean_Util_Heartbeats,
};
use crate::r#gen::Lean::Util::Profile::l_Lean_profileitIOUnsafe___redArg;
use crate::r#gen::Lean::Util::Trace::{
    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go, l_Lean_TraceResult_toEmoji,
    l_Lean_registerTraceClass, l_Lean_trace_profiler, l_Lean_trace_profiler_threshold,
    l_Lean_trace_profiler_useHeartbeats,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::Float::{lean_float_decLt, lean_float_div, lean_float_sub};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget_borrowed, lean_array_get_size, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::IO::{
    lean_io_get_num_heartbeats, lean_io_mono_nanos_now,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
pub static l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__0_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__0_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__0_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__1_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [108, 105, 98, 114, 97, 114, 121, 83, 101, 97, 114, 99, 104, 0]};
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__1_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__1_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__2_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__0_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,5416787921777642938 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__2_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__2_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__1_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,7521313873384996499 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__2_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__2_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__3_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__3_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__3_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__4_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__3_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__4_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__4_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__5_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__5_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__5_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__6_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__4_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__5_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10352885018404983386 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__6_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__6_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__7_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__7_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__7_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__8_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__6_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__7_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,13556645696814629918 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__8_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__8_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__9_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__8_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__0_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,18261494228143523011 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__9_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__9_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__10_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [76, 105, 98, 114, 97, 114, 121, 83, 101, 97, 114, 99, 104, 0]};
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__10_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__10_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__11_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__9_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__10_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,3710107952214331043 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__11_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__11_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__12_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__11_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,17952552163774986350 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__12_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__12_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__13_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__12_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__5_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,14776029588489540247 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__13_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__13_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__14_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__13_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__7_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,3047509625944605639 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__14_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__14_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__15_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__14_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__10_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,2873580876700406095 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__15_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__15_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__16_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__16_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__16_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__17_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__15_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__16_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,1412053500070494670 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__17_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__17_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__18_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__18_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__18_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__19_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__17_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__18_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,711289630588661199 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__19_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__19_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__20_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__19_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__5_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,2945768279020755426 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__20_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__20_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__21_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__20_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__7_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,15130933583494682870 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__21_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__21_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__22_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__21_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__0_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,7443663195510620939 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__22_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__22_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__23_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__22_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__10_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,18428517577648499083 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__23_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__23_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__24_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__24_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__25_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__25_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__25_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__26_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__26_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__27_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__27_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__27_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__28_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__28_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__29_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__29_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__0_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [108, 101, 109, 109, 97, 115, 0]};
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__0_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__0_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__1_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__0_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,5416787921777642938 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__1_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__1_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__1_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,7521313873384996499 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__1_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__1_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__0_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,16866162578278397637 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__1_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__1_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__2_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__23_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 472600257 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,16029677084840091546 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__2_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__2_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__3_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__2_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__25_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,3099002283468202293 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__3_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__3_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__4_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__3_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__27_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,6805166700648767861 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__4_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__4_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__5_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__4_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,10481796823014400056 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__5_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__5_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_LibrarySearch_grindDischarger___lam__0___closed__0_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Meta_LibrarySearch_grindDischarger___lam__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_grindDischarger___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_LibrarySearch_grindDischarger___closed__0_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [71, 114, 105, 110, 100, 0],
};
static mut l_Lean_Meta_LibrarySearch_grindDischarger___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_grindDischarger___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_LibrarySearch_grindDischarger___closed__1_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [77, 97, 114, 107, 101, 114, 0],
};
static mut l_Lean_Meta_LibrarySearch_grindDischarger___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_grindDischarger___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_LibrarySearch_grindDischarger___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__5_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_LibrarySearch_grindDischarger___closed__2_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_grindDischarger___closed__2_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_grindDischarger___closed__0_value)
            as *mut crate::leanh::LeanObject,
        13563742693681136756 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_LibrarySearch_grindDischarger___closed__2_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_grindDischarger___closed__2_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_grindDischarger___closed__1_value)
            as *mut crate::leanh::LeanObject,
        2236570562028567086 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_LibrarySearch_grindDischarger___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_grindDischarger___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_LibrarySearch_grindDischarger___closed__3_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0
            + 8) as u16,
        other: 0,
        tag: 0,
    },
    m_objs: [16777472 as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Meta_LibrarySearch_grindDischarger___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_grindDischarger___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_LibrarySearch_grindDischarger___closed__4_value:
    crate::leanh::LeanCtorObject<17> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13
            + 32) as u16,
        other: 13,
        tag: 0,
    },
    m_objs: [
        (((9 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((5 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((8 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((8 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((1000 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((1000 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((100000 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((1000 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((1048576 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((10 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((50 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        72340168526266368 as *mut crate::leanh::LeanObject,
        72340172821299200 as *mut crate::leanh::LeanObject,
        72340172838076417 as *mut crate::leanh::LeanObject,
        72339073326448897 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_LibrarySearch_grindDischarger___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_grindDischarger___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_LibrarySearch_tryDischarger___closed__0_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [84, 114, 121, 0],
};
static mut l_Lean_Meta_LibrarySearch_tryDischarger___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_tryDischarger___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_LibrarySearch_tryDischarger___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__5_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_LibrarySearch_tryDischarger___closed__1_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_tryDischarger___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_tryDischarger___closed__0_value)
            as *mut crate::leanh::LeanObject,
        8093993747192278382 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_LibrarySearch_tryDischarger___closed__1_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_tryDischarger___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_grindDischarger___closed__1_value)
            as *mut crate::leanh::LeanObject,
        3562682717658811740 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_LibrarySearch_tryDischarger___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_tryDischarger___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_LibrarySearch_tryDischarger___closed__2_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_LibrarySearch_tryDischarger___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Meta_LibrarySearch_tryDischarger___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_tryDischarger___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_LibrarySearch_tryDischarger___closed__3_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [80, 97, 114, 115, 101, 114, 0],
};
static mut l_Lean_Meta_LibrarySearch_tryDischarger___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_tryDischarger___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_LibrarySearch_tryDischarger___closed__4_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [116, 114, 121, 84, 114, 97, 99, 101, 0],
};
static mut l_Lean_Meta_LibrarySearch_tryDischarger___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_tryDischarger___closed__4_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_LibrarySearch_tryDischarger___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__5_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_LibrarySearch_tryDischarger___closed__5_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_tryDischarger___closed__5_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_tryDischarger___closed__3_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_LibrarySearch_tryDischarger___closed__5_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_tryDischarger___closed__5_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__0_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_LibrarySearch_tryDischarger___closed__5_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_tryDischarger___closed__5_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_tryDischarger___closed__4_value)
            as *mut crate::leanh::LeanObject,
        1540710835455164638 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_LibrarySearch_tryDischarger___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_tryDischarger___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_LibrarySearch_tryDischarger___closed__6_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [116, 114, 121, 63, 0],
};
static mut l_Lean_Meta_LibrarySearch_tryDischarger___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_tryDischarger___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_LibrarySearch_tryDischarger___closed__7_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [111, 112, 116, 67, 111, 110, 102, 105, 103, 0],
};
static mut l_Lean_Meta_LibrarySearch_tryDischarger___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_tryDischarger___closed__7_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_LibrarySearch_tryDischarger___closed__8_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__5_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_LibrarySearch_tryDischarger___closed__8_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_tryDischarger___closed__8_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_tryDischarger___closed__3_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_LibrarySearch_tryDischarger___closed__8_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_tryDischarger___closed__8_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__0_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_LibrarySearch_tryDischarger___closed__8_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_tryDischarger___closed__8_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_tryDischarger___closed__7_value)
            as *mut crate::leanh::LeanObject,
        3488656302031949961 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_LibrarySearch_tryDischarger___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_tryDischarger___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_LibrarySearch_tryDischarger___closed__9_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [110, 117, 108, 108, 0],
};
static mut l_Lean_Meta_LibrarySearch_tryDischarger___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_tryDischarger___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_LibrarySearch_tryDischarger___closed__10_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_tryDischarger___closed__9_value)
            as *mut crate::leanh::LeanObject,
        9855511589286918680 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_LibrarySearch_tryDischarger___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_tryDischarger___closed__10_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_LibrarySearch_tryDischarger___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_LibrarySearch_tryDischarger___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_LibrarySearch_tryDischarger___closed__12_value:
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
static mut l_Lean_Meta_LibrarySearch_tryDischarger___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_tryDischarger___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_LibrarySearch_tryDischarger___closed__13_value:
    crate::leanh::LeanCtorObject<10> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8
            + 16) as u16,
        other: 8,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_tryDischarger___closed__2_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_tryDischarger___closed__12_value)
            as *mut crate::leanh::LeanObject,
        16843009 as *mut crate::leanh::LeanObject,
        65537 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_LibrarySearch_tryDischarger___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_tryDischarger___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [102, 97, 105, 108, 101, 100, 0],
};
static mut l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_LibrarySearch_solveByElim___closed__0_value:
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
    m_fun: l_Lean_Meta_LibrarySearch_solveByElim___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_LibrarySearch_solveByElim___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_solveByElim___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_LibrarySearch_solveByElim___closed__1_value:
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
    m_fun: l_Lean_Meta_LibrarySearch_solveByElim___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_LibrarySearch_solveByElim___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_solveByElim___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_LibrarySearch_solveByElim___closed__2_value:
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
    m_fun: l_Lean_Meta_LibrarySearch_solveByElim___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_LibrarySearch_solveByElim___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_solveByElim___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_LibrarySearch_solveByElim___closed__3_value: crate::leanh::LeanArrayObject<
    0,
> = crate::leanh::LeanArrayObject {
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
static mut l_Lean_Meta_LibrarySearch_solveByElim___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_solveByElim___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_LibrarySearch_solveByElim___closed__4_value:
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
    m_fun: l_Lean_Meta_LibrarySearch_grindDischarger___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_LibrarySearch_solveByElim___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_solveByElim___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_LibrarySearch_solveByElim___closed__5_value:
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
    m_fun: l_Lean_Meta_LibrarySearch_tryDischarger___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_LibrarySearch_solveByElim___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_solveByElim___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_LibrarySearch_instInhabitedDeclMod_default: u8 = 0;
pub static mut l_Lean_Meta_LibrarySearch_instInhabitedDeclMod: u8 = 0;
pub static l_Lean_Meta_LibrarySearch_instOrdDeclMod___closed__0_value:
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
    m_fun: l_Lean_Meta_LibrarySearch_instOrdDeclMod_ord___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_LibrarySearch_instOrdDeclMod___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_instOrdDeclMod___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_LibrarySearch_instOrdDeclMod: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_instOrdDeclMod___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_LibrarySearch_instHashableDeclMod___closed__0_value:
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
    m_fun: l_Lean_Meta_LibrarySearch_instHashableDeclMod_hash___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_LibrarySearch_instHashableDeclMod___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_instHashableDeclMod___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_LibrarySearch_instHashableDeclMod: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_instHashableDeclMod___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0___closed__0_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [73, 102, 102, 0]};
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,9917798623386220051 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0___closed__2_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_defaultLibSearchState: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_instInhabitedLibSearchState: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__0_00___x40_Lean_Meta_Tactic_LibrarySearch_2561004661____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___lam__0_00___x40_Lean_Meta_Tactic_LibrarySearch_2561004661____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__0_00___x40_Lean_Meta_Tactic_LibrarySearch_2561004661____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__0_00___x40_Lean_Meta_Tactic_LibrarySearch_2561004661____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_ext:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_LibrarySearch_droppedKeys___closed__0_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((3 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_LibrarySearch_droppedKeys___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_droppedKeys___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_LibrarySearch_droppedKeys___closed__1_value: crate::leanh::LeanStringObject<
    3,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [69, 113, 0],
};
static mut l_Lean_Meta_LibrarySearch_droppedKeys___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_droppedKeys___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_LibrarySearch_droppedKeys___closed__2_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_droppedKeys___closed__1_value)
            as *mut crate::leanh::LeanObject,
        16122875713692181903 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_LibrarySearch_droppedKeys___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_droppedKeys___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_LibrarySearch_droppedKeys___closed__3_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_droppedKeys___closed__2_value)
            as *mut crate::leanh::LeanObject,
        (((3 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_LibrarySearch_droppedKeys___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_droppedKeys___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_LibrarySearch_droppedKeys___closed__4_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((3 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_droppedKeys___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_LibrarySearch_droppedKeys___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_droppedKeys___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_LibrarySearch_droppedKeys___closed__5_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((3 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_droppedKeys___closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_LibrarySearch_droppedKeys___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_droppedKeys___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_LibrarySearch_droppedKeys___closed__6_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_droppedKeys___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_droppedKeys___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_LibrarySearch_droppedKeys___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_droppedKeys___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_LibrarySearch_droppedKeys___closed__7_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_droppedKeys___closed__6_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_LibrarySearch_droppedKeys___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_droppedKeys___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_LibrarySearch_droppedKeys___closed__8_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_droppedKeys___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_droppedKeys___closed__7_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_LibrarySearch_droppedKeys___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_droppedKeys___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_LibrarySearch_droppedKeys: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_droppedKeys___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_constantsPerImportTask: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__0_00___x40_Lean_Meta_Tactic_LibrarySearch_956453063____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___lam__0_00___x40_Lean_Meta_Tactic_LibrarySearch_956453063____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__0_00___x40_Lean_Meta_Tactic_LibrarySearch_956453063____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__0_00___x40_Lean_Meta_Tactic_LibrarySearch_956453063____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_starLemmasExt: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_LibrarySearch_libSearchFindDecls___closed__0_value:
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
    m_fun: l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___boxed
        as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_LibrarySearch_libSearchFindDecls___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_libSearchFindDecls___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_LibrarySearch_getStarLemmas___closed__0_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [84, 114, 117, 101, 0],
};
static mut l_Lean_Meta_LibrarySearch_getStarLemmas___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_getStarLemmas___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_LibrarySearch_getStarLemmas___closed__1_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_getStarLemmas___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11870096045526947150 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_LibrarySearch_getStarLemmas___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_getStarLemmas___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_LibrarySearch_getStarLemmas___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_LibrarySearch_getStarLemmas___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_LibrarySearch_getStarLemmas___closed__3_value:
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
static mut l_Lean_Meta_LibrarySearch_getStarLemmas___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_getStarLemmas___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__0_00___x40_Lean_Meta_Tactic_LibrarySearch_989218885____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [97, 98, 111, 114, 116, 83, 112, 101, 99, 117, 108, 97, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__0_00___x40_Lean_Meta_Tactic_LibrarySearch_989218885____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__0_00___x40_Lean_Meta_Tactic_LibrarySearch_989218885____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__1_00___x40_Lean_Meta_Tactic_LibrarySearch_989218885____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__5_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__1_00___x40_Lean_Meta_Tactic_LibrarySearch_989218885____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__1_00___x40_Lean_Meta_Tactic_LibrarySearch_989218885____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__7_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,15449383196166861506 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__1_00___x40_Lean_Meta_Tactic_LibrarySearch_989218885____hygCtx___hyg_2__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__1_00___x40_Lean_Meta_Tactic_LibrarySearch_989218885____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__10_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,15735798734296298254 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__1_00___x40_Lean_Meta_Tactic_LibrarySearch_989218885____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__1_00___x40_Lean_Meta_Tactic_LibrarySearch_989218885____hygCtx___hyg_2__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__0_00___x40_Lean_Meta_Tactic_LibrarySearch_989218885____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,15255471975451243741 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__1_00___x40_Lean_Meta_Tactic_LibrarySearch_989218885____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__1_00___x40_Lean_Meta_Tactic_LibrarySearch_989218885____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_abortSpeculationId: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [109, 112, 0],
};
static mut l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__0___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,9917798623386220051 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__0___closed__1_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__0___closed__1_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__0___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        12550588708175797395 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__0___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__1___closed__0_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [109, 112, 114, 0],
};
static mut l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__1___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,9917798623386220051 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__1___closed__1_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__1___closed__1_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__1___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        240879799840100622 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__1___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___closed__0_value:
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
    m_fun: l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___closed__1_value:
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
    m_fun: l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__0_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [116, 114, 121, 105, 110, 103, 32, 0]};
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__2_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__4_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__5_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__4_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__5_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__7_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [32, 119, 105, 116, 104, 32, 109, 112, 0]};
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__8_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__7_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__10_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [32, 119, 105, 116, 104, 32, 109, 112, 114, 0]};
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__11_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__10_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__11_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__12_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__12: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0: f64 = 0.0;
pub static l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__1_value: crate::leanh::LeanStringObject<54> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [60, 101, 120, 99, 101, 112, 116, 105, 111, 110, 32, 116, 104, 114, 111, 119, 110, 32, 119, 104, 105, 108, 101, 32, 112, 114, 111, 100, 117, 99, 105, 110, 103, 32, 116, 114, 97, 99, 101, 32, 110, 111, 100, 101, 32, 109, 101, 115, 115, 97, 103, 101, 62, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3: f64 = 0.0;
pub static l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__0_value) as *mut crate::leanh::LeanObject,14231257465488249300 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3: f64 = 0.0;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LibrarySearch_tryOnEach_spec__0___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LibrarySearch_tryOnEach_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LibrarySearch_tryOnEach_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_LibrarySearch_tryOnEach___closed__0_value: crate::leanh::LeanArrayObject<0> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Meta_LibrarySearch_tryOnEach___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_tryOnEach___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_LibrarySearch_tryOnEach___closed__1_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_tryOnEach___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_LibrarySearch_tryOnEach___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_LibrarySearch_tryOnEach___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_LibrarySearch_libSearchFindDecls___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0 + 8) as u16, other: 0, tag: 0 }, m_objs: [16843008 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___closed__0_value) as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__24_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3356_ = crate::leanh::lean_unsigned_to_nat(4259869437);
    v___x_3357_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__23_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_;
    v___x_3358_ = l_Lean_Name_num___override(v___x_3357_, v___x_3356_);
    return v___x_3358_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__26_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3360_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__25_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_;
    v___x_3361_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__24_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__24_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__24_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_);
    v___x_3362_ = l_Lean_Name_str___override(v___x_3361_, v___x_3360_);
    return v___x_3362_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__28_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3364_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__27_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_;
    v___x_3365_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__26_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__26_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__26_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_);
    v___x_3366_ = l_Lean_Name_str___override(v___x_3365_, v___x_3364_);
    return v___x_3366_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__29_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3367_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_3368_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__28_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__28_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__28_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_);
    v___x_3369_ = l_Lean_Name_num___override(v___x_3368_, v___x_3367_);
    return v___x_3369_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3372_: u8 = 0;
    let mut v___x_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3371_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__2_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_;
    v___x_3372_ = 0;
    v___x_3373_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__29_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__29_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__29_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_);
    v___x_3374_ = l_Lean_registerTraceClass(v___x_3371_, v___x_3372_, v___x_3373_);
    return v___x_3374_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2____boxed(
    mut v_a_3375_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3376_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_();
    return v_res_3376_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3396_: u8 = 0;
    let mut v___x_3397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3395_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__1_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2_;
    v___x_3396_ = 0;
    v___x_3397_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__5_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2_;
    v___x_3398_ = l_Lean_registerTraceClass(v___x_3395_, v___x_3396_, v___x_3397_);
    return v___x_3398_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2____boxed(
    mut v_a_3399_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3400_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2_();
    return v_res_3400_;
}
pub unsafe fn l_Lean_Meta_LibrarySearch_grindDischarger___lam__0(
    mut v_x_3403_: *mut crate::leanh::LeanObject,
    mut v___y_3404_: *mut crate::leanh::LeanObject,
    mut v___y_3405_: *mut crate::leanh::LeanObject,
    mut v___y_3406_: *mut crate::leanh::LeanObject,
    mut v___y_3407_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3409_ = l_Lean_Meta_LibrarySearch_grindDischarger___lam__0___closed__0;
    v___x_3410_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3410_, 0, v___x_3409_);
    return v___x_3410_;
}
pub unsafe fn l_Lean_Meta_LibrarySearch_grindDischarger___lam__0___boxed(
    mut v_x_3411_: *mut crate::leanh::LeanObject,
    mut v___y_3412_: *mut crate::leanh::LeanObject,
    mut v___y_3413_: *mut crate::leanh::LeanObject,
    mut v___y_3414_: *mut crate::leanh::LeanObject,
    mut v___y_3415_: *mut crate::leanh::LeanObject,
    mut v___y_3416_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3417_ = l_Lean_Meta_LibrarySearch_grindDischarger___lam__0(
        v_x_3411_,
        v___y_3412_,
        v___y_3413_,
        v___y_3414_,
        v___y_3415_,
    );
    crate::leanh::lean_dec(v___y_3415_);
    crate::leanh::lean_dec_ref(v___y_3414_);
    crate::leanh::lean_dec(v___y_3413_);
    crate::leanh::lean_dec_ref(v___y_3412_);
    crate::leanh::lean_dec(v_x_3411_);
    return v_res_3417_;
}
pub unsafe fn l_Lean_Meta_LibrarySearch_grindDischarger(
    mut v_mvarId_3441_: *mut crate::leanh::LeanObject,
    mut v_a_3442_: *mut crate::leanh::LeanObject,
    mut v_a_3443_: *mut crate::leanh::LeanObject,
    mut v_a_3444_: *mut crate::leanh::LeanObject,
    mut v_a_3445_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3449_: u8 = 0;
    let mut v___x_3450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: u8 = 0;
    let mut v___x_3456_: u8 = 0;
    let mut v___y_3458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3462_: u8 = 0;
    let mut v_a_3463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3467_: u8 = 0;
    let mut v___x_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3488_: u8 = 0;
    let mut v___x_3489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3493_: u8 = 0;
    let mut v___x_3494_: u8 = 0;
    let mut v___x_3496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3504_: u8 = 0;
    let mut v_a_3505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3506_: u8 = 0;
    let mut v_a_3507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_mvarId_3441_);
                v___x_3468_ = l_Lean_MVarId_getType(
                    v_mvarId_3441_,
                    v_a_3442_,
                    v_a_3443_,
                    v_a_3444_,
                    v_a_3445_,
                );
                if crate::leanh::lean_obj_tag(v___x_3468_) == 0 {
                    v_a_3469_ = crate::leanh::lean_ctor_get(v___x_3468_, 0);
                    crate::leanh::lean_inc_n(v_a_3469_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_3468_, 1);
                    v___x_3470_ =
                        l_Lean_Meta_getLevel(v_a_3469_, v_a_3442_, v_a_3443_, v_a_3444_, v_a_3445_);
                    if crate::leanh::lean_obj_tag(v___x_3470_) == 0 {
                        v_a_3471_ = crate::leanh::lean_ctor_get(v___x_3470_, 0);
                        crate::leanh::lean_inc(v_a_3471_);
                        crate::leanh::lean_dec_ref_known(v___x_3470_, 1);
                        v___x_3472_ = l_Lean_Meta_LibrarySearch_grindDischarger___closed__2;
                        v___x_3473_ = crate::leanh::lean_box(0);
                        v___x_3474_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3474_, 0, v_a_3471_);
                        crate::leanh::lean_ctor_set(v___x_3474_, 1, v___x_3473_);
                        v___x_3475_ = l_Lean_Expr_const___override(v___x_3472_, v___x_3474_);
                        v___x_3476_ = l_Lean_Expr_app___override(v___x_3475_, v_a_3469_);
                        v___x_3477_ = l_Lean_Meta_LibrarySearch_grindDischarger___closed__3;
                        v___x_3478_ = crate::leanh::lean_box(0);
                        v___x_3479_ = l_Lean_MVarId_apply(
                            v_mvarId_3441_,
                            v___x_3476_,
                            v___x_3477_,
                            v___x_3478_,
                            v_a_3442_,
                            v_a_3443_,
                            v_a_3444_,
                            v_a_3445_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3479_) == 0 {
                            v_a_3480_ = crate::leanh::lean_ctor_get(v___x_3479_, 0);
                            crate::leanh::lean_inc(v_a_3480_);
                            crate::leanh::lean_dec_ref_known(v___x_3479_, 1);
                            if crate::leanh::lean_obj_tag(v_a_3480_) == 1 {
                                v_tail_3481_ = crate::leanh::lean_ctor_get(v_a_3480_, 1);
                                if crate::leanh::lean_obj_tag(v_tail_3481_) == 0 {
                                    crate::leanh::lean_inc(v_tail_3481_);
                                    v_head_3482_ = crate::leanh::lean_ctor_get(v_a_3480_, 0);
                                    crate::leanh::lean_inc(v_head_3482_);
                                    crate::leanh::lean_dec_ref_known(v_a_3480_, 2);
                                    v___x_3483_ =
                                        l_Lean_Meta_LibrarySearch_grindDischarger___closed__4;
                                    v___x_3484_ = l_Lean_Meta_Grind_mkDefaultParams(
                                        v___x_3483_,
                                        v_a_3442_,
                                        v_a_3443_,
                                        v_a_3444_,
                                        v_a_3445_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_3484_) == 0 {
                                        v_a_3485_ = crate::leanh::lean_ctor_get(v___x_3484_, 0);
                                        v_isSharedCheck_3506_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_3484_)) as u8;
                                        if v_isSharedCheck_3506_ == 0 {
                                            v___x_3487_ = v___x_3484_;
                                            v_isShared_3488_ = v_isSharedCheck_3506_;
                                            state = 6;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_3485_);
                                            crate::leanh::lean_dec(v___x_3484_);
                                            v___x_3487_ = crate::leanh::lean_box(0);
                                            v_isShared_3488_ = v_isSharedCheck_3506_;
                                            state = 6;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_head_3482_);
                                        v_a_3507_ = crate::leanh::lean_ctor_get(v___x_3484_, 0);
                                        crate::leanh::lean_inc(v_a_3507_);
                                        crate::leanh::lean_dec_ref_known(v___x_3484_, 1);
                                        v_a_3454_ = v_a_3507_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    v___x_3508_ =
                                        l_Lean_Meta_LibrarySearch_grindDischarger___lam__0(
                                            v_a_3480_, v_a_3442_, v_a_3443_, v_a_3444_, v_a_3445_,
                                        );
                                    crate::leanh::lean_dec_ref_known(v_a_3480_, 2);
                                    v___y_3458_ = v___x_3508_;
                                    state = 3;
                                    continue;
                                }
                            } else {
                                v___x_3509_ = l_Lean_Meta_LibrarySearch_grindDischarger___lam__0(
                                    v_a_3480_, v_a_3442_, v_a_3443_, v_a_3444_, v_a_3445_,
                                );
                                crate::leanh::lean_dec(v_a_3480_);
                                v___y_3458_ = v___x_3509_;
                                state = 3;
                                continue;
                            }
                        } else {
                            v_a_3510_ = crate::leanh::lean_ctor_get(v___x_3479_, 0);
                            crate::leanh::lean_inc(v_a_3510_);
                            crate::leanh::lean_dec_ref_known(v___x_3479_, 1);
                            v_a_3454_ = v_a_3510_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3469_);
                        crate::leanh::lean_dec(v_mvarId_3441_);
                        v_a_3511_ = crate::leanh::lean_ctor_get(v___x_3470_, 0);
                        crate::leanh::lean_inc(v_a_3511_);
                        crate::leanh::lean_dec_ref_known(v___x_3470_, 1);
                        v_a_3454_ = v_a_3511_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_mvarId_3441_);
                    v_a_3512_ = crate::leanh::lean_ctor_get(v___x_3468_, 0);
                    crate::leanh::lean_inc(v_a_3512_);
                    crate::leanh::lean_dec_ref_known(v___x_3468_, 1);
                    v_a_3454_ = v_a_3512_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                if v___y_3449_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_3448_);
                    v___x_3450_ = crate::leanh::lean_box(0);
                    v___x_3451_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3451_, 0, v___x_3450_);
                    return v___x_3451_;
                } else {
                    v___x_3452_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3452_, 0, v___y_3448_);
                    return v___x_3452_;
                }
            }
            2 => {
                v___x_3455_ = l_Lean_Exception_isInterrupt(v_a_3454_);
                if v___x_3455_ == 0 {
                    crate::leanh::lean_inc_ref(v_a_3454_);
                    v___x_3456_ = l_Lean_Exception_isRuntime(v_a_3454_);
                    v___y_3448_ = v_a_3454_;
                    v___y_3449_ = v___x_3456_;
                    state = 1;
                    continue;
                } else {
                    v___y_3448_ = v_a_3454_;
                    v___y_3449_ = v___x_3455_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v_a_3459_ = crate::leanh::lean_ctor_get(v___y_3458_, 0);
                v_isSharedCheck_3467_ = (!crate::leanh::lean_is_exclusive(v___y_3458_)) as u8;
                if v_isSharedCheck_3467_ == 0 {
                    v___x_3461_ = v___y_3458_;
                    v_isShared_3462_ = v_isSharedCheck_3467_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3459_);
                    crate::leanh::lean_dec(v___y_3458_);
                    v___x_3461_ = crate::leanh::lean_box(0);
                    v_isShared_3462_ = v_isSharedCheck_3467_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_a_3463_ = crate::leanh::lean_ctor_get(v_a_3459_, 0);
                crate::leanh::lean_inc(v_a_3463_);
                crate::leanh::lean_dec(v_a_3459_);
                if v_isShared_3462_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3461_, 0, v_a_3463_);
                    v___x_3465_ = v___x_3461_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3466_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3466_, 0, v_a_3463_);
                    v___x_3465_ = v_reuseFailAlloc_3466_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3465_;
            }
            6 => {
                v___x_3489_ = l_Lean_Meta_Grind_main(
                    v_head_3482_,
                    v_a_3485_,
                    v_a_3442_,
                    v_a_3443_,
                    v_a_3444_,
                    v_a_3445_,
                );
                if crate::leanh::lean_obj_tag(v___x_3489_) == 0 {
                    v_a_3490_ = crate::leanh::lean_ctor_get(v___x_3489_, 0);
                    v_isSharedCheck_3504_ = (!crate::leanh::lean_is_exclusive(v___x_3489_)) as u8;
                    if v_isSharedCheck_3504_ == 0 {
                        v___x_3492_ = v___x_3489_;
                        v_isShared_3493_ = v_isSharedCheck_3504_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3490_);
                        crate::leanh::lean_dec(v___x_3489_);
                        v___x_3492_ = crate::leanh::lean_box(0);
                        v_isShared_3493_ = v_isSharedCheck_3504_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3487_);
                    v_a_3505_ = crate::leanh::lean_ctor_get(v___x_3489_, 0);
                    crate::leanh::lean_inc(v_a_3505_);
                    crate::leanh::lean_dec_ref_known(v___x_3489_, 1);
                    v_a_3454_ = v_a_3505_;
                    state = 2;
                    continue;
                }
            }
            7 => {
                v___x_3494_ = l_Lean_Meta_Grind_Result_hasFailed(v_a_3490_);
                crate::leanh::lean_dec(v_a_3490_);
                if v___x_3494_ == 0 {
                    if v_isShared_3488_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_3487_, 1);
                        crate::leanh::lean_ctor_set(v___x_3487_, 0, v_tail_3481_);
                        v___x_3496_ = v___x_3487_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_3500_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3500_, 0, v_tail_3481_);
                        v___x_3496_ = v_reuseFailAlloc_3500_;
                        state = 8;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3487_);
                    if v_isShared_3493_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3492_, 0, v___x_3478_);
                        v___x_3502_ = v___x_3492_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_3503_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3503_, 0, v___x_3478_);
                        v___x_3502_ = v_reuseFailAlloc_3503_;
                        state = 10;
                        continue;
                    }
                }
            }
            8 => {
                if v_isShared_3493_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3492_, 0, v___x_3496_);
                    v___x_3498_ = v___x_3492_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3499_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3499_, 0, v___x_3496_);
                    v___x_3498_ = v_reuseFailAlloc_3499_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3498_;
            }
            10 => {
                return v___x_3502_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_LibrarySearch_grindDischarger___boxed(
    mut v_mvarId_3513_: *mut crate::leanh::LeanObject,
    mut v_a_3514_: *mut crate::leanh::LeanObject,
    mut v_a_3515_: *mut crate::leanh::LeanObject,
    mut v_a_3516_: *mut crate::leanh::LeanObject,
    mut v_a_3517_: *mut crate::leanh::LeanObject,
    mut v_a_3518_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3519_ = l_Lean_Meta_LibrarySearch_grindDischarger(
        v_mvarId_3513_,
        v_a_3514_,
        v_a_3515_,
        v_a_3516_,
        v_a_3517_,
    );
    crate::leanh::lean_dec(v_a_3517_);
    crate::leanh::lean_dec_ref(v_a_3516_);
    crate::leanh::lean_dec(v_a_3515_);
    crate::leanh::lean_dec_ref(v_a_3514_);
    return v_res_3519_;
}
pub unsafe fn l_Lean_Meta_LibrarySearch_tryDischarger___lam__1(
    mut v___x_3520_: u8,
    mut v_x_3521_: *mut crate::leanh::LeanObject,
) -> u8 {
    return v___x_3520_;
}
pub unsafe fn l_Lean_Meta_LibrarySearch_tryDischarger___lam__1___boxed(
    mut v___x_3522_: *mut crate::leanh::LeanObject,
    mut v_x_3523_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3971__boxed_3524_: u8 = 0;
    let mut v_res_3525_: u8 = 0;
    let mut v_r_3526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3971__boxed_3524_ = (crate::leanh::lean_unbox(v___x_3522_) as u8);
    v_res_3525_ =
        l_Lean_Meta_LibrarySearch_tryDischarger___lam__1(v___x_3971__boxed_3524_, v_x_3523_);
    crate::leanh::lean_dec(v_x_3523_);
    v_r_3526_ = crate::leanh::lean_box((v_res_3525_) as usize);
    return v_r_3526_;
}
pub unsafe fn _init_l_Lean_Meta_LibrarySearch_tryDischarger___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3552_ = l_Array_mkArray0(crate::leanh::lean_box(0));
    return v___x_3552_;
}
pub unsafe fn l_Lean_Meta_LibrarySearch_tryDischarger(
    mut v_mvarId_3563_: *mut crate::leanh::LeanObject,
    mut v_a_3564_: *mut crate::leanh::LeanObject,
    mut v_a_3565_: *mut crate::leanh::LeanObject,
    mut v_a_3566_: *mut crate::leanh::LeanObject,
    mut v_a_3567_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3571_: u8 = 0;
    let mut v___x_3572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3577_: u8 = 0;
    let mut v___x_3578_: u8 = 0;
    let mut v___y_3580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3584_: u8 = 0;
    let mut v_a_3585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3589_: u8 = 0;
    let mut v___x_3590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: u8 = 0;
    let mut v___x_3600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3606_: u8 = 0;
    let mut v_tail_3607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3611_: u8 = 0;
    let mut v_ref_3612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3634_: u8 = 0;
    let mut v_fst_3635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: u8 = 0;
    let mut v___x_3638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3646_: u8 = 0;
    let mut v_a_3647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3649_: u8 = 0;
    let mut v_unused_3650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3653_: u8 = 0;
    let mut v_a_3654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_mvarId_3563_);
                v___x_3590_ = l_Lean_MVarId_getType(
                    v_mvarId_3563_,
                    v_a_3564_,
                    v_a_3565_,
                    v_a_3566_,
                    v_a_3567_,
                );
                if crate::leanh::lean_obj_tag(v___x_3590_) == 0 {
                    v_a_3591_ = crate::leanh::lean_ctor_get(v___x_3590_, 0);
                    crate::leanh::lean_inc_n(v_a_3591_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_3590_, 1);
                    v___x_3592_ =
                        l_Lean_Meta_getLevel(v_a_3591_, v_a_3564_, v_a_3565_, v_a_3566_, v_a_3567_);
                    if crate::leanh::lean_obj_tag(v___x_3592_) == 0 {
                        v_a_3593_ = crate::leanh::lean_ctor_get(v___x_3592_, 0);
                        crate::leanh::lean_inc(v_a_3593_);
                        crate::leanh::lean_dec_ref_known(v___x_3592_, 1);
                        v___x_3594_ = l_Lean_Meta_LibrarySearch_tryDischarger___closed__1;
                        v___x_3595_ = crate::leanh::lean_box(0);
                        v___x_3596_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3596_, 0, v_a_3593_);
                        crate::leanh::lean_ctor_set(v___x_3596_, 1, v___x_3595_);
                        v___x_3597_ = l_Lean_Expr_const___override(v___x_3594_, v___x_3596_);
                        v___x_3598_ = l_Lean_Expr_app___override(v___x_3597_, v_a_3591_);
                        v___x_3599_ = 0;
                        v___x_3600_ = l_Lean_Meta_LibrarySearch_grindDischarger___closed__3;
                        v___x_3601_ = crate::leanh::lean_box(0);
                        v___x_3602_ = l_Lean_MVarId_apply(
                            v_mvarId_3563_,
                            v___x_3598_,
                            v___x_3600_,
                            v___x_3601_,
                            v_a_3564_,
                            v_a_3565_,
                            v_a_3566_,
                            v_a_3567_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3602_) == 0 {
                            v_a_3603_ = crate::leanh::lean_ctor_get(v___x_3602_, 0);
                            v_isSharedCheck_3653_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3602_)) as u8;
                            if v_isSharedCheck_3653_ == 0 {
                                v___x_3605_ = v___x_3602_;
                                v_isShared_3606_ = v_isSharedCheck_3653_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3603_);
                                crate::leanh::lean_dec(v___x_3602_);
                                v___x_3605_ = crate::leanh::lean_box(0);
                                v_isShared_3606_ = v_isSharedCheck_3653_;
                                state = 6;
                                continue;
                            }
                        } else {
                            v_a_3654_ = crate::leanh::lean_ctor_get(v___x_3602_, 0);
                            crate::leanh::lean_inc(v_a_3654_);
                            crate::leanh::lean_dec_ref_known(v___x_3602_, 1);
                            v_a_3576_ = v_a_3654_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3591_);
                        crate::leanh::lean_dec(v_mvarId_3563_);
                        v_a_3655_ = crate::leanh::lean_ctor_get(v___x_3592_, 0);
                        crate::leanh::lean_inc(v_a_3655_);
                        crate::leanh::lean_dec_ref_known(v___x_3592_, 1);
                        v_a_3576_ = v_a_3655_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_mvarId_3563_);
                    v_a_3656_ = crate::leanh::lean_ctor_get(v___x_3590_, 0);
                    crate::leanh::lean_inc(v_a_3656_);
                    crate::leanh::lean_dec_ref_known(v___x_3590_, 1);
                    v_a_3576_ = v_a_3656_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                if v___y_3571_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_3570_);
                    v___x_3572_ = crate::leanh::lean_box(0);
                    v___x_3573_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3573_, 0, v___x_3572_);
                    return v___x_3573_;
                } else {
                    v___x_3574_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3574_, 0, v___y_3570_);
                    return v___x_3574_;
                }
            }
            2 => {
                v___x_3577_ = l_Lean_Exception_isInterrupt(v_a_3576_);
                if v___x_3577_ == 0 {
                    crate::leanh::lean_inc_ref(v_a_3576_);
                    v___x_3578_ = l_Lean_Exception_isRuntime(v_a_3576_);
                    v___y_3570_ = v_a_3576_;
                    v___y_3571_ = v___x_3578_;
                    state = 1;
                    continue;
                } else {
                    v___y_3570_ = v_a_3576_;
                    v___y_3571_ = v___x_3577_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v_a_3581_ = crate::leanh::lean_ctor_get(v___y_3580_, 0);
                v_isSharedCheck_3589_ = (!crate::leanh::lean_is_exclusive(v___y_3580_)) as u8;
                if v_isSharedCheck_3589_ == 0 {
                    v___x_3583_ = v___y_3580_;
                    v_isShared_3584_ = v_isSharedCheck_3589_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3581_);
                    crate::leanh::lean_dec(v___y_3580_);
                    v___x_3583_ = crate::leanh::lean_box(0);
                    v_isShared_3584_ = v_isSharedCheck_3589_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_a_3585_ = crate::leanh::lean_ctor_get(v_a_3581_, 0);
                crate::leanh::lean_inc(v_a_3585_);
                crate::leanh::lean_dec(v_a_3581_);
                if v_isShared_3584_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3583_, 0, v_a_3585_);
                    v___x_3587_ = v___x_3583_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3588_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3588_, 0, v_a_3585_);
                    v___x_3587_ = v_reuseFailAlloc_3588_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3587_;
            }
            6 => {
                if crate::leanh::lean_obj_tag(v_a_3603_) == 1 {
                    v_tail_3607_ = crate::leanh::lean_ctor_get(v_a_3603_, 1);
                    if crate::leanh::lean_obj_tag(v_tail_3607_) == 0 {
                        crate::leanh::lean_inc(v_tail_3607_);
                        v_head_3608_ = crate::leanh::lean_ctor_get(v_a_3603_, 0);
                        v_isSharedCheck_3649_ = (!crate::leanh::lean_is_exclusive(v_a_3603_)) as u8;
                        if v_isSharedCheck_3649_ == 0 {
                            v_unused_3650_ = crate::leanh::lean_ctor_get(v_a_3603_, 1);
                            crate::leanh::lean_dec(v_unused_3650_);
                            v___x_3610_ = v_a_3603_;
                            v_isShared_3611_ = v_isSharedCheck_3649_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_head_3608_);
                            crate::leanh::lean_dec(v_a_3603_);
                            v___x_3610_ = crate::leanh::lean_box(0);
                            v_isShared_3611_ = v_isSharedCheck_3649_;
                            state = 7;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_3605_);
                        v___x_3651_ = l_Lean_Meta_LibrarySearch_grindDischarger___lam__0(
                            v_a_3603_, v_a_3564_, v_a_3565_, v_a_3566_, v_a_3567_,
                        );
                        crate::leanh::lean_dec_ref_known(v_a_3603_, 2);
                        v___y_3580_ = v___x_3651_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3605_);
                    v___x_3652_ = l_Lean_Meta_LibrarySearch_grindDischarger___lam__0(
                        v_a_3603_, v_a_3564_, v_a_3565_, v_a_3566_, v_a_3567_,
                    );
                    crate::leanh::lean_dec(v_a_3603_);
                    v___y_3580_ = v___x_3652_;
                    state = 3;
                    continue;
                }
            }
            7 => {
                v_ref_3612_ = crate::leanh::lean_ctor_get(v_a_3566_, 5);
                v___x_3613_ = l_Lean_SourceInfo_fromRef(v_ref_3612_, v___x_3599_);
                v___x_3614_ = l_Lean_Meta_LibrarySearch_tryDischarger___closed__5;
                v___x_3615_ = l_Lean_Meta_LibrarySearch_tryDischarger___closed__6;
                crate::leanh::lean_inc(v___x_3613_);
                if v_isShared_3611_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3610_, 2);
                    crate::leanh::lean_ctor_set(v___x_3610_, 1, v___x_3615_);
                    crate::leanh::lean_ctor_set(v___x_3610_, 0, v___x_3613_);
                    v___x_3617_ = v___x_3610_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3648_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3648_, 0, v___x_3613_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3648_, 1, v___x_3615_);
                    v___x_3617_ = v_reuseFailAlloc_3648_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_3618_ = l_Lean_Meta_LibrarySearch_tryDischarger___closed__8;
                v___x_3619_ = l_Lean_Meta_LibrarySearch_tryDischarger___closed__10;
                v___x_3620_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_LibrarySearch_tryDischarger___closed__11),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_LibrarySearch_tryDischarger___closed__11_once
                    ),
                    _init_l_Lean_Meta_LibrarySearch_tryDischarger___closed__11,
                );
                crate::leanh::lean_inc_n(v___x_3613_, 2);
                v___x_3621_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3621_, 0, v___x_3613_);
                crate::leanh::lean_ctor_set(v___x_3621_, 1, v___x_3619_);
                crate::leanh::lean_ctor_set(v___x_3621_, 2, v___x_3620_);
                v___x_3622_ = l_Lean_Syntax_node1(v___x_3613_, v___x_3618_, v___x_3621_);
                v___x_3623_ =
                    l_Lean_Syntax_node2(v___x_3613_, v___x_3614_, v___x_3617_, v___x_3622_);
                v___x_3624_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_Tactic_evalTactic___boxed as *mut core::ffi::c_void,
                    10,
                    1,
                );
                crate::leanh::lean_closure_set(v___x_3624_, 0, v___x_3623_);
                v___x_3625_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_Tactic_withSuppressedMessages___boxed as *mut core::ffi::c_void,
                    11,
                    2,
                );
                crate::leanh::lean_closure_set(v___x_3625_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_3625_, 1, v___x_3624_);
                v___x_3626_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_Tactic_run___boxed as *mut core::ffi::c_void,
                    9,
                    2,
                );
                crate::leanh::lean_closure_set(v___x_3626_, 0, v_head_3608_);
                crate::leanh::lean_closure_set(v___x_3626_, 1, v___x_3625_);
                v___x_3627_ = crate::leanh::lean_box(1);
                v___x_3628_ = l_Lean_Meta_LibrarySearch_tryDischarger___closed__13;
                v___x_3629_ = crate::leanh::lean_alloc_ctor(0, 7, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3629_, 0, v___x_3595_);
                crate::leanh::lean_ctor_set(v___x_3629_, 1, v___x_3627_);
                crate::leanh::lean_ctor_set(v___x_3629_, 2, v_tail_3607_);
                crate::leanh::lean_ctor_set(v___x_3629_, 3, v___x_3595_);
                crate::leanh::lean_ctor_set(v___x_3629_, 4, v___x_3595_);
                crate::leanh::lean_ctor_set(v___x_3629_, 5, v___x_3627_);
                crate::leanh::lean_ctor_set(v___x_3629_, 6, v___x_3595_);
                v___x_3630_ = l_Lean_Elab_Term_TermElabM_run___redArg(
                    v___x_3626_,
                    v___x_3628_,
                    v___x_3629_,
                    v_a_3564_,
                    v_a_3565_,
                    v_a_3566_,
                    v_a_3567_,
                );
                if crate::leanh::lean_obj_tag(v___x_3630_) == 0 {
                    v_a_3631_ = crate::leanh::lean_ctor_get(v___x_3630_, 0);
                    v_isSharedCheck_3646_ = (!crate::leanh::lean_is_exclusive(v___x_3630_)) as u8;
                    if v_isSharedCheck_3646_ == 0 {
                        v___x_3633_ = v___x_3630_;
                        v_isShared_3634_ = v_isSharedCheck_3646_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3631_);
                        crate::leanh::lean_dec(v___x_3630_);
                        v___x_3633_ = crate::leanh::lean_box(0);
                        v_isShared_3634_ = v_isSharedCheck_3646_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3605_);
                    v_a_3647_ = crate::leanh::lean_ctor_get(v___x_3630_, 0);
                    crate::leanh::lean_inc(v_a_3647_);
                    crate::leanh::lean_dec_ref_known(v___x_3630_, 1);
                    v_a_3576_ = v_a_3647_;
                    state = 2;
                    continue;
                }
            }
            9 => {
                v_fst_3635_ = crate::leanh::lean_ctor_get(v_a_3631_, 0);
                crate::leanh::lean_inc(v_fst_3635_);
                crate::leanh::lean_dec(v_a_3631_);
                v___x_3636_ = l_List_isEmpty___redArg(v_fst_3635_);
                crate::leanh::lean_dec(v_fst_3635_);
                if v___x_3636_ == 0 {
                    crate::leanh::lean_del_object(v___x_3605_);
                    if v_isShared_3634_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3633_, 0, v___x_3601_);
                        v___x_3638_ = v___x_3633_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_3639_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3639_, 0, v___x_3601_);
                        v___x_3638_ = v_reuseFailAlloc_3639_;
                        state = 10;
                        continue;
                    }
                } else {
                    if v_isShared_3606_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_3605_, 1);
                        crate::leanh::lean_ctor_set(v___x_3605_, 0, v_tail_3607_);
                        v___x_3641_ = v___x_3605_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_3645_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3645_, 0, v_tail_3607_);
                        v___x_3641_ = v_reuseFailAlloc_3645_;
                        state = 11;
                        continue;
                    }
                }
            }
            10 => {
                return v___x_3638_;
            }
            11 => {
                if v_isShared_3634_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3633_, 0, v___x_3641_);
                    v___x_3643_ = v___x_3633_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3644_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3644_, 0, v___x_3641_);
                    v___x_3643_ = v_reuseFailAlloc_3644_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3643_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_LibrarySearch_tryDischarger___boxed(
    mut v_mvarId_3657_: *mut crate::leanh::LeanObject,
    mut v_a_3658_: *mut crate::leanh::LeanObject,
    mut v_a_3659_: *mut crate::leanh::LeanObject,
    mut v_a_3660_: *mut crate::leanh::LeanObject,
    mut v_a_3661_: *mut crate::leanh::LeanObject,
    mut v_a_3662_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3663_ = l_Lean_Meta_LibrarySearch_tryDischarger(
        v_mvarId_3657_,
        v_a_3658_,
        v_a_3659_,
        v_a_3660_,
        v_a_3661_,
    );
    crate::leanh::lean_dec(v_a_3661_);
    crate::leanh::lean_dec_ref(v_a_3660_);
    crate::leanh::lean_dec(v_a_3659_);
    crate::leanh::lean_dec_ref(v_a_3658_);
    return v_res_3663_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0_spec__0(
    mut v_msgData_3664_: *mut crate::leanh::LeanObject,
    mut v___y_3665_: *mut crate::leanh::LeanObject,
    mut v___y_3666_: *mut crate::leanh::LeanObject,
    mut v___y_3667_: *mut crate::leanh::LeanObject,
    mut v___y_3668_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3670_ = lean_st_ref_get(v___y_3668_);
    v_env_3671_ = crate::leanh::lean_ctor_get(v___x_3670_, 0);
    crate::leanh::lean_inc_ref(v_env_3671_);
    crate::leanh::lean_dec(v___x_3670_);
    v___x_3672_ = lean_st_ref_get(v___y_3666_);
    v_mctx_3673_ = crate::leanh::lean_ctor_get(v___x_3672_, 0);
    crate::leanh::lean_inc_ref(v_mctx_3673_);
    crate::leanh::lean_dec(v___x_3672_);
    v_lctx_3674_ = crate::leanh::lean_ctor_get(v___y_3665_, 2);
    v_options_3675_ = crate::leanh::lean_ctor_get(v___y_3667_, 2);
    crate::leanh::lean_inc_ref(v_options_3675_);
    crate::leanh::lean_inc_ref(v_lctx_3674_);
    v___x_3676_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3676_, 0, v_env_3671_);
    crate::leanh::lean_ctor_set(v___x_3676_, 1, v_mctx_3673_);
    crate::leanh::lean_ctor_set(v___x_3676_, 2, v_lctx_3674_);
    crate::leanh::lean_ctor_set(v___x_3676_, 3, v_options_3675_);
    v___x_3677_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3677_, 0, v___x_3676_);
    crate::leanh::lean_ctor_set(v___x_3677_, 1, v_msgData_3664_);
    v___x_3678_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3678_, 0, v___x_3677_);
    return v___x_3678_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0_spec__0___boxed(
    mut v_msgData_3679_: *mut crate::leanh::LeanObject,
    mut v___y_3680_: *mut crate::leanh::LeanObject,
    mut v___y_3681_: *mut crate::leanh::LeanObject,
    mut v___y_3682_: *mut crate::leanh::LeanObject,
    mut v___y_3683_: *mut crate::leanh::LeanObject,
    mut v___y_3684_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3685_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0_spec__0(v_msgData_3679_, v___y_3680_, v___y_3681_, v___y_3682_, v___y_3683_);
    crate::leanh::lean_dec(v___y_3683_);
    crate::leanh::lean_dec_ref(v___y_3682_);
    crate::leanh::lean_dec(v___y_3681_);
    crate::leanh::lean_dec_ref(v___y_3680_);
    return v_res_3685_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(
    mut v_msg_3686_: *mut crate::leanh::LeanObject,
    mut v___y_3687_: *mut crate::leanh::LeanObject,
    mut v___y_3688_: *mut crate::leanh::LeanObject,
    mut v___y_3689_: *mut crate::leanh::LeanObject,
    mut v___y_3690_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_3692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3697_: u8 = 0;
    let mut v___x_3698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3702_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3692_ = crate::leanh::lean_ctor_get(v___y_3689_, 5);
                v___x_3693_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0_spec__0(v_msg_3686_, v___y_3687_, v___y_3688_, v___y_3689_, v___y_3690_);
                v_a_3694_ = crate::leanh::lean_ctor_get(v___x_3693_, 0);
                v_isSharedCheck_3702_ = (!crate::leanh::lean_is_exclusive(v___x_3693_)) as u8;
                if v_isSharedCheck_3702_ == 0 {
                    v___x_3696_ = v___x_3693_;
                    v_isShared_3697_ = v_isSharedCheck_3702_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3694_);
                    crate::leanh::lean_dec(v___x_3693_);
                    v___x_3696_ = crate::leanh::lean_box(0);
                    v_isShared_3697_ = v_isSharedCheck_3702_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_3692_);
                v___x_3698_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3698_, 0, v_ref_3692_);
                crate::leanh::lean_ctor_set(v___x_3698_, 1, v_a_3694_);
                if v_isShared_3697_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3696_, 1);
                    crate::leanh::lean_ctor_set(v___x_3696_, 0, v___x_3698_);
                    v___x_3700_ = v___x_3696_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3701_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3701_, 0, v___x_3698_);
                    v___x_3700_ = v_reuseFailAlloc_3701_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3700_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg___boxed(
    mut v_msg_3703_: *mut crate::leanh::LeanObject,
    mut v___y_3704_: *mut crate::leanh::LeanObject,
    mut v___y_3705_: *mut crate::leanh::LeanObject,
    mut v___y_3706_: *mut crate::leanh::LeanObject,
    mut v___y_3707_: *mut crate::leanh::LeanObject,
    mut v___y_3708_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3709_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(
        v_msg_3703_,
        v___y_3704_,
        v___y_3705_,
        v___y_3706_,
        v___y_3707_,
    );
    crate::leanh::lean_dec(v___y_3707_);
    crate::leanh::lean_dec_ref(v___y_3706_);
    crate::leanh::lean_dec(v___y_3705_);
    crate::leanh::lean_dec_ref(v___y_3704_);
    return v_res_3709_;
}
pub unsafe fn _init_l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3711_ = l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__0;
    v___x_3712_ = l_Lean_stringToMessageData(v___x_3711_);
    return v___x_3712_;
}
pub unsafe fn l_Lean_Meta_LibrarySearch_solveByElim___lam__0(
    mut v_x_3713_: *mut crate::leanh::LeanObject,
    mut v___y_3714_: *mut crate::leanh::LeanObject,
    mut v___y_3715_: *mut crate::leanh::LeanObject,
    mut v___y_3716_: *mut crate::leanh::LeanObject,
    mut v___y_3717_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3719_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1_once),
        _init_l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1,
    );
    v___x_3720_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(
        v___x_3719_,
        v___y_3714_,
        v___y_3715_,
        v___y_3716_,
        v___y_3717_,
    );
    return v___x_3720_;
}
pub unsafe fn l_Lean_Meta_LibrarySearch_solveByElim___lam__0___boxed(
    mut v_x_3721_: *mut crate::leanh::LeanObject,
    mut v___y_3722_: *mut crate::leanh::LeanObject,
    mut v___y_3723_: *mut crate::leanh::LeanObject,
    mut v___y_3724_: *mut crate::leanh::LeanObject,
    mut v___y_3725_: *mut crate::leanh::LeanObject,
    mut v___y_3726_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3727_ = l_Lean_Meta_LibrarySearch_solveByElim___lam__0(
        v_x_3721_,
        v___y_3722_,
        v___y_3723_,
        v___y_3724_,
        v___y_3725_,
    );
    crate::leanh::lean_dec(v___y_3725_);
    crate::leanh::lean_dec_ref(v___y_3724_);
    crate::leanh::lean_dec(v___y_3723_);
    crate::leanh::lean_dec_ref(v___y_3722_);
    crate::leanh::lean_dec(v_x_3721_);
    return v_res_3727_;
}
pub unsafe fn l_Lean_Meta_LibrarySearch_solveByElim___lam__1(
    mut v_x_3728_: *mut crate::leanh::LeanObject,
    mut v___y_3729_: *mut crate::leanh::LeanObject,
    mut v___y_3730_: *mut crate::leanh::LeanObject,
    mut v___y_3731_: *mut crate::leanh::LeanObject,
    mut v___y_3732_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3734_: u8 = 0;
    let mut v___x_3735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3734_ = 0;
    v___x_3735_ = crate::leanh::lean_box((v___x_3734_) as usize);
    v___x_3736_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3736_, 0, v___x_3735_);
    return v___x_3736_;
}
pub unsafe fn l_Lean_Meta_LibrarySearch_solveByElim___lam__1___boxed(
    mut v_x_3737_: *mut crate::leanh::LeanObject,
    mut v___y_3738_: *mut crate::leanh::LeanObject,
    mut v___y_3739_: *mut crate::leanh::LeanObject,
    mut v___y_3740_: *mut crate::leanh::LeanObject,
    mut v___y_3741_: *mut crate::leanh::LeanObject,
    mut v___y_3742_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3743_ = l_Lean_Meta_LibrarySearch_solveByElim___lam__1(
        v_x_3737_,
        v___y_3738_,
        v___y_3739_,
        v___y_3740_,
        v___y_3741_,
    );
    crate::leanh::lean_dec(v___y_3741_);
    crate::leanh::lean_dec_ref(v___y_3740_);
    crate::leanh::lean_dec(v___y_3739_);
    crate::leanh::lean_dec_ref(v___y_3738_);
    crate::leanh::lean_dec(v_x_3737_);
    return v_res_3743_;
}
pub unsafe fn l_Lean_Meta_LibrarySearch_solveByElim___lam__2(
    mut v_x_3744_: *mut crate::leanh::LeanObject,
    mut v_x_3745_: *mut crate::leanh::LeanObject,
    mut v___y_3746_: *mut crate::leanh::LeanObject,
    mut v___y_3747_: *mut crate::leanh::LeanObject,
    mut v___y_3748_: *mut crate::leanh::LeanObject,
    mut v___y_3749_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3751_ = crate::leanh::lean_box(0);
    v___x_3752_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3752_, 0, v___x_3751_);
    return v___x_3752_;
}
pub unsafe fn l_Lean_Meta_LibrarySearch_solveByElim___lam__2___boxed(
    mut v_x_3753_: *mut crate::leanh::LeanObject,
    mut v_x_3754_: *mut crate::leanh::LeanObject,
    mut v___y_3755_: *mut crate::leanh::LeanObject,
    mut v___y_3756_: *mut crate::leanh::LeanObject,
    mut v___y_3757_: *mut crate::leanh::LeanObject,
    mut v___y_3758_: *mut crate::leanh::LeanObject,
    mut v___y_3759_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3760_ = l_Lean_Meta_LibrarySearch_solveByElim___lam__2(
        v_x_3753_,
        v_x_3754_,
        v___y_3755_,
        v___y_3756_,
        v___y_3757_,
        v___y_3758_,
    );
    crate::leanh::lean_dec(v___y_3758_);
    crate::leanh::lean_dec_ref(v___y_3757_);
    crate::leanh::lean_dec(v___y_3756_);
    crate::leanh::lean_dec_ref(v___y_3755_);
    crate::leanh::lean_dec(v_x_3754_);
    crate::leanh::lean_dec(v_x_3753_);
    return v_res_3760_;
}
pub unsafe fn l_Lean_Meta_LibrarySearch_solveByElim(
    mut v_required_3768_: *mut crate::leanh::LeanObject,
    mut v_exfalso_3769_: u8,
    mut v_goals_3770_: *mut crate::leanh::LeanObject,
    mut v_maxDepth_3771_: *mut crate::leanh::LeanObject,
    mut v_grind_3772_: u8,
    mut v_try_x3f_3773_: u8,
    mut v_a_3774_: *mut crate::leanh::LeanObject,
    mut v_a_3775_: *mut crate::leanh::LeanObject,
    mut v_a_3776_: *mut crate::leanh::LeanObject,
    mut v_a_3777_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_transparency_3780_: u8 = 0;
    let mut v___f_3781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3784_: u8 = 0;
    let mut v___x_3785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: u8 = 0;
    let mut v___y_3788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3795_: u8 = 0;
    let mut v___x_3796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3802_: u8 = 0;
    let mut v___x_3804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3806_: u8 = 0;
    let mut v___x_3807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3779_ = l_Lean_Meta_Context_config(v_a_3774_);
                v_transparency_3780_ = crate::leanh::lean_ctor_get_uint8(v___x_3779_, 9 as u32);
                crate::leanh::lean_dec_ref(v___x_3779_);
                v___f_3781_ = l_Lean_Meta_LibrarySearch_solveByElim___closed__0;
                v___f_3782_ = l_Lean_Meta_LibrarySearch_solveByElim___closed__1;
                v___f_3783_ = l_Lean_Meta_LibrarySearch_solveByElim___closed__2;
                v___x_3784_ = 1;
                v___x_3785_ = crate::leanh::lean_alloc_ctor(0, 4, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3785_, 0, v_maxDepth_3771_);
                crate::leanh::lean_ctor_set(v___x_3785_, 1, v___f_3783_);
                crate::leanh::lean_ctor_set(v___x_3785_, 2, v___f_3782_);
                crate::leanh::lean_ctor_set(v___x_3785_, 3, v___f_3781_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3785_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v___x_3784_,
                );
                v___x_3786_ = 0;
                v___x_3807_ = l_Lean_Meta_LibrarySearch_grindDischarger___closed__3;
                v___x_3808_ = crate::leanh::lean_alloc_ctor(0, 2, (3) as u32);
                crate::leanh::lean_ctor_set(v___x_3808_, 0, v___x_3785_);
                crate::leanh::lean_ctor_set(v___x_3808_, 1, v___x_3807_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3808_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v_transparency_3780_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3808_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 1) as u32,
                    v___x_3784_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3808_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 2) as u32,
                    v_exfalso_3769_,
                );
                v___x_3809_ = crate::leanh::lean_alloc_ctor(0, 1, (4) as u32);
                crate::leanh::lean_ctor_set(v___x_3809_, 0, v___x_3808_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3809_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_3784_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3809_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 1) as u32,
                    v___x_3784_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3809_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 2) as u32,
                    v___x_3786_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3809_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 3) as u32,
                    v___x_3786_,
                );
                if v_try_x3f_3773_ == 0 {
                    if v_grind_3772_ == 0 {
                        v___y_3788_ = v___x_3809_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3810_ = l_Lean_Meta_LibrarySearch_solveByElim___closed__4;
                        v___x_3811_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(
                            v___x_3809_,
                            v___x_3810_,
                        );
                        v___y_3788_ = v___x_3811_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_3812_ = l_Lean_Meta_LibrarySearch_solveByElim___closed__5;
                    v___x_3813_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(
                        v___x_3809_,
                        v___x_3812_,
                    );
                    v___y_3788_ = v___x_3813_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3789_ = crate::leanh::lean_box(0);
                v___x_3790_ = l_Lean_Meta_LibrarySearch_solveByElim___closed__3;
                v___x_3791_ = l_Lean_Meta_SolveByElim_mkAssumptionSet(
                    v___x_3786_,
                    v___x_3786_,
                    v___x_3789_,
                    v___x_3789_,
                    v___x_3790_,
                    v_a_3774_,
                    v_a_3775_,
                    v_a_3776_,
                    v_a_3777_,
                );
                if crate::leanh::lean_obj_tag(v___x_3791_) == 0 {
                    v_a_3792_ = crate::leanh::lean_ctor_get(v___x_3791_, 0);
                    crate::leanh::lean_inc(v_a_3792_);
                    crate::leanh::lean_dec_ref_known(v___x_3791_, 1);
                    v_fst_3793_ = crate::leanh::lean_ctor_get(v_a_3792_, 0);
                    crate::leanh::lean_inc(v_fst_3793_);
                    v_snd_3794_ = crate::leanh::lean_ctor_get(v_a_3792_, 1);
                    crate::leanh::lean_inc(v_snd_3794_);
                    crate::leanh::lean_dec(v_a_3792_);
                    v___x_3795_ = l_List_isEmpty___redArg(v_required_3768_);
                    if v___x_3795_ == 0 {
                        v___x_3796_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll(
                            v___y_3788_,
                            v_required_3768_,
                        );
                        v___x_3797_ = l_Lean_Meta_SolveByElim_solveByElim(
                            v___x_3796_,
                            v_fst_3793_,
                            v_snd_3794_,
                            v_goals_3770_,
                            v_a_3774_,
                            v_a_3775_,
                            v_a_3776_,
                            v_a_3777_,
                        );
                        return v___x_3797_;
                    } else {
                        crate::leanh::lean_dec(v_required_3768_);
                        v___x_3798_ = l_Lean_Meta_SolveByElim_solveByElim(
                            v___y_3788_,
                            v_fst_3793_,
                            v_snd_3794_,
                            v_goals_3770_,
                            v_a_3774_,
                            v_a_3775_,
                            v_a_3776_,
                            v_a_3777_,
                        );
                        return v___x_3798_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_3788_);
                    crate::leanh::lean_dec(v_goals_3770_);
                    crate::leanh::lean_dec(v_required_3768_);
                    v_a_3799_ = crate::leanh::lean_ctor_get(v___x_3791_, 0);
                    v_isSharedCheck_3806_ = (!crate::leanh::lean_is_exclusive(v___x_3791_)) as u8;
                    if v_isSharedCheck_3806_ == 0 {
                        v___x_3801_ = v___x_3791_;
                        v_isShared_3802_ = v_isSharedCheck_3806_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3799_);
                        crate::leanh::lean_dec(v___x_3791_);
                        v___x_3801_ = crate::leanh::lean_box(0);
                        v_isShared_3802_ = v_isSharedCheck_3806_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3802_ == 0 {
                    v___x_3804_ = v___x_3801_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3805_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3805_, 0, v_a_3799_);
                    v___x_3804_ = v_reuseFailAlloc_3805_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3804_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_LibrarySearch_solveByElim___boxed(
    mut v_required_3814_: *mut crate::leanh::LeanObject,
    mut v_exfalso_3815_: *mut crate::leanh::LeanObject,
    mut v_goals_3816_: *mut crate::leanh::LeanObject,
    mut v_maxDepth_3817_: *mut crate::leanh::LeanObject,
    mut v_grind_3818_: *mut crate::leanh::LeanObject,
    mut v_try_x3f_3819_: *mut crate::leanh::LeanObject,
    mut v_a_3820_: *mut crate::leanh::LeanObject,
    mut v_a_3821_: *mut crate::leanh::LeanObject,
    mut v_a_3822_: *mut crate::leanh::LeanObject,
    mut v_a_3823_: *mut crate::leanh::LeanObject,
    mut v_a_3824_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_exfalso_boxed_3825_: u8 = 0;
    let mut v_grind_boxed_3826_: u8 = 0;
    let mut v_try_x3f_boxed_3827_: u8 = 0;
    let mut v_res_3828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_exfalso_boxed_3825_ = (crate::leanh::lean_unbox(v_exfalso_3815_) as u8);
    v_grind_boxed_3826_ = (crate::leanh::lean_unbox(v_grind_3818_) as u8);
    v_try_x3f_boxed_3827_ = (crate::leanh::lean_unbox(v_try_x3f_3819_) as u8);
    v_res_3828_ = l_Lean_Meta_LibrarySearch_solveByElim(
        v_required_3814_,
        v_exfalso_boxed_3825_,
        v_goals_3816_,
        v_maxDepth_3817_,
        v_grind_boxed_3826_,
        v_try_x3f_boxed_3827_,
        v_a_3820_,
        v_a_3821_,
        v_a_3822_,
        v_a_3823_,
    );
    crate::leanh::lean_dec(v_a_3823_);
    crate::leanh::lean_dec_ref(v_a_3822_);
    crate::leanh::lean_dec(v_a_3821_);
    crate::leanh::lean_dec_ref(v_a_3820_);
    return v_res_3828_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0(
    mut v_00_u03b1_3829_: *mut crate::leanh::LeanObject,
    mut v_msg_3830_: *mut crate::leanh::LeanObject,
    mut v___y_3831_: *mut crate::leanh::LeanObject,
    mut v___y_3832_: *mut crate::leanh::LeanObject,
    mut v___y_3833_: *mut crate::leanh::LeanObject,
    mut v___y_3834_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3836_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(
        v_msg_3830_,
        v___y_3831_,
        v___y_3832_,
        v___y_3833_,
        v___y_3834_,
    );
    return v___x_3836_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___boxed(
    mut v_00_u03b1_3837_: *mut crate::leanh::LeanObject,
    mut v_msg_3838_: *mut crate::leanh::LeanObject,
    mut v___y_3839_: *mut crate::leanh::LeanObject,
    mut v___y_3840_: *mut crate::leanh::LeanObject,
    mut v___y_3841_: *mut crate::leanh::LeanObject,
    mut v___y_3842_: *mut crate::leanh::LeanObject,
    mut v___y_3843_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3844_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0(
        v_00_u03b1_3837_,
        v_msg_3838_,
        v___y_3839_,
        v___y_3840_,
        v___y_3841_,
        v___y_3842_,
    );
    crate::leanh::lean_dec(v___y_3842_);
    crate::leanh::lean_dec_ref(v___y_3841_);
    crate::leanh::lean_dec(v___y_3840_);
    crate::leanh::lean_dec_ref(v___y_3839_);
    return v_res_3844_;
}
pub unsafe fn l_Lean_Meta_LibrarySearch_DeclMod_ctorIdx(
    mut v_x_3845_: u8,
) -> *mut crate::leanh::LeanObject {
    match v_x_3845_ {
        0 => {
            let mut v___x_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3846_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_3846_;
        }
        1 => {
            let mut v___x_3847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3847_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_3847_;
        }
        _ => {
            let mut v___x_3848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3848_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_3848_;
        }
    }
}
pub unsafe fn l_Lean_Meta_LibrarySearch_DeclMod_ctorIdx___boxed(
    mut v_x_3849_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_3850_: u8 = 0;
    let mut v_res_3851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_3850_ = (crate::leanh::lean_unbox(v_x_3849_) as u8);
    v_res_3851_ = l_Lean_Meta_LibrarySearch_DeclMod_ctorIdx(v_x_boxed_3850_);
    return v_res_3851_;
}
pub unsafe fn l_Lean_Meta_LibrarySearch_DeclMod_toCtorIdx(
    mut v_x_3852_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3853_ = l_Lean_Meta_LibrarySearch_DeclMod_ctorIdx(v_x_3852_);
    return v___x_3853_;
}
pub unsafe fn l_Lean_Meta_LibrarySearch_DeclMod_toCtorIdx___boxed(
    mut v_x_3854_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4__boxed_3855_: u8 = 0;
    let mut v_res_3856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_3855_ = (crate::leanh::lean_unbox(v_x_3854_) as u8);
    v_res_3856_ = l_Lean_Meta_LibrarySearch_DeclMod_toCtorIdx(v_x_4__boxed_3855_);
    return v_res_3856_;
}
pub unsafe fn l_Lean_Meta_LibrarySearch_DeclMod_ctorElim___redArg(
    mut v_k_3857_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_3857_);
    return v_k_3857_;
}
pub unsafe fn l_Lean_Meta_LibrarySearch_DeclMod_ctorElim___redArg___boxed(
    mut v_k_3858_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3859_ = l_Lean_Meta_LibrarySearch_DeclMod_ctorElim___redArg(v_k_3858_);
    crate::leanh::lean_dec(v_k_3858_);
    return v_res_3859_;
}
pub unsafe fn l_Lean_Meta_LibrarySearch_DeclMod_ctorElim(
    mut v_motive_3860_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_3861_: *mut crate::leanh::LeanObject,
    mut v_t_3862_: u8,
    mut v_h_3863_: *mut crate::leanh::LeanObject,
    mut v_k_3864_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_3864_);
    return v_k_3864_;
}
pub unsafe fn l_Lean_Meta_LibrarySearch_DeclMod_ctorElim___boxed(
    mut v_motive_3865_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_3866_: *mut crate::leanh::LeanObject,
    mut v_t_3867_: *mut crate::leanh::LeanObject,
    mut v_h_3868_: *mut crate::leanh::LeanObject,
    mut v_k_3869_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_3870_: u8 = 0;
    let mut v_res_3871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_3870_ = (crate::leanh::lean_unbox(v_t_3867_) as u8);
    v_res_3871_ = l_Lean_Meta_LibrarySearch_DeclMod_ctorElim(
        v_motive_3865_,
        v_ctorIdx_3866_,
        v_t_boxed_3870_,
        v_h_3868_,
        v_k_3869_,
    );
    crate::leanh::lean_dec(v_k_3869_);
    crate::leanh::lean_dec(v_ctorIdx_3866_);
    return v_res_3871_;
}
pub unsafe fn l_Lean_Meta_LibrarySearch_DeclMod_none_elim___redArg(
    mut v_none_3872_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_none_3872_);
    return v_none_3872_;
}
pub unsafe fn l_Lean_Meta_LibrarySearch_DeclMod_none_elim___redArg___boxed(
    mut v_none_3873_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3874_ = l_Lean_Meta_LibrarySearch_DeclMod_none_elim___redArg(v_none_3873_);
    crate::leanh::lean_dec(v_none_3873_);
    return v_res_3874_;
}
pub unsafe fn l_Lean_Meta_LibrarySearch_DeclMod_none_elim(
    mut v_motive_3875_: *mut crate::leanh::LeanObject,
    mut v_t_3876_: u8,
    mut v_h_3877_: *mut crate::leanh::LeanObject,
    mut v_none_3878_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_none_3878_);
    return v_none_3878_;
}
pub unsafe fn l_Lean_Meta_LibrarySearch_DeclMod_none_elim___boxed(
    mut v_motive_3879_: *mut crate::leanh::LeanObject,
    mut v_t_3880_: *mut crate::leanh::LeanObject,
    mut v_h_3881_: *mut crate::leanh::LeanObject,
    mut v_none_3882_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_3883_: u8 = 0;
    let mut v_res_3884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_3883_ = (crate::leanh::lean_unbox(v_t_3880_) as u8);
    v_res_3884_ = l_Lean_Meta_LibrarySearch_DeclMod_none_elim(
        v_motive_3879_,
        v_t_boxed_3883_,
        v_h_3881_,
        v_none_3882_,
    );
    crate::leanh::lean_dec(v_none_3882_);
    return v_res_3884_;
}
pub unsafe fn l_Lean_Meta_LibrarySearch_DeclMod_mp_elim___redArg(
    mut v_mp_3885_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_mp_3885_);
    return v_mp_3885_;
}
pub unsafe fn l_Lean_Meta_LibrarySearch_DeclMod_mp_elim___redArg___boxed(
    mut v_mp_3886_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3887_ = l_Lean_Meta_LibrarySearch_DeclMod_mp_elim___redArg(v_mp_3886_);
    crate::leanh::lean_dec(v_mp_3886_);
    return v_res_3887_;
}
pub unsafe fn l_Lean_Meta_LibrarySearch_DeclMod_mp_elim(
    mut v_motive_3888_: *mut crate::leanh::LeanObject,
    mut v_t_3889_: u8,
    mut v_h_3890_: *mut crate::leanh::LeanObject,
    mut v_mp_3891_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_mp_3891_);
    return v_mp_3891_;
}
pub unsafe fn l_Lean_Meta_LibrarySearch_DeclMod_mp_elim___boxed(
    mut v_motive_3892_: *mut crate::leanh::LeanObject,
    mut v_t_3893_: *mut crate::leanh::LeanObject,
    mut v_h_3894_: *mut crate::leanh::LeanObject,
    mut v_mp_3895_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_3896_: u8 = 0;
    let mut v_res_3897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_3896_ = (crate::leanh::lean_unbox(v_t_3893_) as u8);
    v_res_3897_ = l_Lean_Meta_LibrarySearch_DeclMod_mp_elim(
        v_motive_3892_,
        v_t_boxed_3896_,
        v_h_3894_,
        v_mp_3895_,
    );
    crate::leanh::lean_dec(v_mp_3895_);
    return v_res_3897_;
}
pub unsafe fn l_Lean_Meta_LibrarySearch_DeclMod_mpr_elim___redArg(
    mut v_mpr_3898_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_mpr_3898_);
    return v_mpr_3898_;
}
pub unsafe fn l_Lean_Meta_LibrarySearch_DeclMod_mpr_elim___redArg___boxed(
    mut v_mpr_3899_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3900_ = l_Lean_Meta_LibrarySearch_DeclMod_mpr_elim___redArg(v_mpr_3899_);
    crate::leanh::lean_dec(v_mpr_3899_);
    return v_res_3900_;
}
pub unsafe fn l_Lean_Meta_LibrarySearch_DeclMod_mpr_elim(
    mut v_motive_3901_: *mut crate::leanh::LeanObject,
    mut v_t_3902_: u8,
    mut v_h_3903_: *mut crate::leanh::LeanObject,
    mut v_mpr_3904_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_mpr_3904_);
    return v_mpr_3904_;
}
pub unsafe fn l_Lean_Meta_LibrarySearch_DeclMod_mpr_elim___boxed(
    mut v_motive_3905_: *mut crate::leanh::LeanObject,
    mut v_t_3906_: *mut crate::leanh::LeanObject,
    mut v_h_3907_: *mut crate::leanh::LeanObject,
    mut v_mpr_3908_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_3909_: u8 = 0;
    let mut v_res_3910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_3909_ = (crate::leanh::lean_unbox(v_t_3906_) as u8);
    v_res_3910_ = l_Lean_Meta_LibrarySearch_DeclMod_mpr_elim(
        v_motive_3905_,
        v_t_boxed_3909_,
        v_h_3907_,
        v_mpr_3908_,
    );
    crate::leanh::lean_dec(v_mpr_3908_);
    return v_res_3910_;
}
pub unsafe fn l_Lean_Meta_LibrarySearch_DeclMod_ofNat(
    mut v_n_3911_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: u8 = 0;
    v___x_3912_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3913_ = lean_nat_dec_le(v_n_3911_, v___x_3912_);
    if v___x_3913_ == 0 {
        let mut v___x_3914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3915_: u8 = 0;
        v___x_3914_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_3915_ = lean_nat_dec_le(v_n_3911_, v___x_3914_);
        if v___x_3915_ == 0 {
            let mut v___x_3916_: u8 = 0;
            v___x_3916_ = 2;
            return v___x_3916_;
        } else {
            let mut v___x_3917_: u8 = 0;
            v___x_3917_ = 1;
            return v___x_3917_;
        }
    } else {
        let mut v___x_3918_: u8 = 0;
        v___x_3918_ = 0;
        return v___x_3918_;
    }
}
pub unsafe fn l_Lean_Meta_LibrarySearch_DeclMod_ofNat___boxed(
    mut v_n_3919_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3920_: u8 = 0;
    let mut v_r_3921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3920_ = l_Lean_Meta_LibrarySearch_DeclMod_ofNat(v_n_3919_);
    crate::leanh::lean_dec(v_n_3919_);
    v_r_3921_ = crate::leanh::lean_box((v_res_3920_) as usize);
    return v_r_3921_;
}
pub unsafe fn l_Lean_Meta_LibrarySearch_instDecidableEqDeclMod(
    mut v_x_3922_: u8,
    mut v_y_3923_: u8,
) -> u8 {
    let mut v___x_3924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: u8 = 0;
    v___x_3924_ = l_Lean_Meta_LibrarySearch_DeclMod_ctorIdx(v_x_3922_);
    v___x_3925_ = l_Lean_Meta_LibrarySearch_DeclMod_ctorIdx(v_y_3923_);
    v___x_3926_ = lean_nat_dec_eq(v___x_3924_, v___x_3925_);
    crate::leanh::lean_dec(v___x_3925_);
    crate::leanh::lean_dec(v___x_3924_);
    return v___x_3926_;
}
pub unsafe fn l_Lean_Meta_LibrarySearch_instDecidableEqDeclMod___boxed(
    mut v_x_3927_: *mut crate::leanh::LeanObject,
    mut v_y_3928_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_13__boxed_3929_: u8 = 0;
    let mut v_y_14__boxed_3930_: u8 = 0;
    let mut v_res_3931_: u8 = 0;
    let mut v_r_3932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_13__boxed_3929_ = (crate::leanh::lean_unbox(v_x_3927_) as u8);
    v_y_14__boxed_3930_ = (crate::leanh::lean_unbox(v_y_3928_) as u8);
    v_res_3931_ =
        l_Lean_Meta_LibrarySearch_instDecidableEqDeclMod(v_x_13__boxed_3929_, v_y_14__boxed_3930_);
    v_r_3932_ = crate::leanh::lean_box((v_res_3931_) as usize);
    return v_r_3932_;
}
pub unsafe fn _init_l_Lean_Meta_LibrarySearch_instInhabitedDeclMod_default() -> u8 {
    let mut v___x_3933_: u8 = 0;
    v___x_3933_ = 0;
    return v___x_3933_;
}
pub unsafe fn _init_l_Lean_Meta_LibrarySearch_instInhabitedDeclMod() -> u8 {
    let mut v___x_3934_: u8 = 0;
    v___x_3934_ = 0;
    return v___x_3934_;
}
pub unsafe fn l_Lean_Meta_LibrarySearch_instOrdDeclMod_ord(
    mut v_x_3935_: u8,
    mut v_y_3936_: u8,
) -> u8 {
    let mut v___x_3937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3939_: u8 = 0;
    v___x_3937_ = l_Lean_Meta_LibrarySearch_DeclMod_ctorIdx(v_x_3935_);
    v___x_3938_ = l_Lean_Meta_LibrarySearch_DeclMod_ctorIdx(v_y_3936_);
    v___x_3939_ = lean_nat_dec_lt(v___x_3937_, v___x_3938_);
    if v___x_3939_ == 0 {
        let mut v___x_3940_: u8 = 0;
        v___x_3940_ = lean_nat_dec_eq(v___x_3937_, v___x_3938_);
        crate::leanh::lean_dec(v___x_3938_);
        crate::leanh::lean_dec(v___x_3937_);
        if v___x_3940_ == 0 {
            let mut v___x_3941_: u8 = 0;
            v___x_3941_ = 2;
            return v___x_3941_;
        } else {
            let mut v___x_3942_: u8 = 0;
            v___x_3942_ = 1;
            return v___x_3942_;
        }
    } else {
        let mut v___x_3943_: u8 = 0;
        crate::leanh::lean_dec(v___x_3938_);
        crate::leanh::lean_dec(v___x_3937_);
        v___x_3943_ = 0;
        return v___x_3943_;
    }
}
pub unsafe fn l_Lean_Meta_LibrarySearch_instOrdDeclMod_ord___boxed(
    mut v_x_3944_: *mut crate::leanh::LeanObject,
    mut v_y_3945_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_30__boxed_3946_: u8 = 0;
    let mut v_y_31__boxed_3947_: u8 = 0;
    let mut v_res_3948_: u8 = 0;
    let mut v_r_3949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_30__boxed_3946_ = (crate::leanh::lean_unbox(v_x_3944_) as u8);
    v_y_31__boxed_3947_ = (crate::leanh::lean_unbox(v_y_3945_) as u8);
    v_res_3948_ =
        l_Lean_Meta_LibrarySearch_instOrdDeclMod_ord(v_x_30__boxed_3946_, v_y_31__boxed_3947_);
    v_r_3949_ = crate::leanh::lean_box((v_res_3948_) as usize);
    return v_r_3949_;
}
pub unsafe fn l_Lean_Meta_LibrarySearch_instHashableDeclMod_hash(mut v_x_3952_: u8) -> u64 {
    match v_x_3952_ {
        0 => {
            let mut v___x_3953_: u64 = 0;
            v___x_3953_ = 0u64;
            return v___x_3953_;
        }
        1 => {
            let mut v___x_3954_: u64 = 0;
            v___x_3954_ = 1u64;
            return v___x_3954_;
        }
        _ => {
            let mut v___x_3955_: u64 = 0;
            v___x_3955_ = 2u64;
            return v___x_3955_;
        }
    }
}
pub unsafe fn l_Lean_Meta_LibrarySearch_instHashableDeclMod_hash___boxed(
    mut v_x_3956_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_40__boxed_3957_: u8 = 0;
    let mut v_res_3958_: u64 = 0;
    let mut v_r_3959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_40__boxed_3957_ = (crate::leanh::lean_unbox(v_x_3956_) as u8);
    v_res_3958_ = l_Lean_Meta_LibrarySearch_instHashableDeclMod_hash(v_x_40__boxed_3957_);
    v_r_3959_ = crate::leanh::lean_box_uint64(v_res_3958_);
    return v_r_3959_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg___lam__0(
    mut v_k_3962_: *mut crate::leanh::LeanObject,
    mut v_b_3963_: *mut crate::leanh::LeanObject,
    mut v_c_3964_: *mut crate::leanh::LeanObject,
    mut v___y_3965_: *mut crate::leanh::LeanObject,
    mut v___y_3966_: *mut crate::leanh::LeanObject,
    mut v___y_3967_: *mut crate::leanh::LeanObject,
    mut v___y_3968_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_3968_);
    crate::leanh::lean_inc_ref(v___y_3967_);
    crate::leanh::lean_inc(v___y_3966_);
    crate::leanh::lean_inc_ref(v___y_3965_);
    v___x_3970_ = crate::leanh::lean_apply_7(
        v_k_3962_,
        v_b_3963_,
        v_c_3964_,
        v___y_3965_,
        v___y_3966_,
        v___y_3967_,
        v___y_3968_,
        crate::leanh::lean_box(0),
    );
    return v___x_3970_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg___lam__0___boxed(
    mut v_k_3971_: *mut crate::leanh::LeanObject,
    mut v_b_3972_: *mut crate::leanh::LeanObject,
    mut v_c_3973_: *mut crate::leanh::LeanObject,
    mut v___y_3974_: *mut crate::leanh::LeanObject,
    mut v___y_3975_: *mut crate::leanh::LeanObject,
    mut v___y_3976_: *mut crate::leanh::LeanObject,
    mut v___y_3977_: *mut crate::leanh::LeanObject,
    mut v___y_3978_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3979_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg___lam__0(v_k_3971_, v_b_3972_, v_c_3973_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_);
    crate::leanh::lean_dec(v___y_3977_);
    crate::leanh::lean_dec_ref(v___y_3976_);
    crate::leanh::lean_dec(v___y_3975_);
    crate::leanh::lean_dec_ref(v___y_3974_);
    return v_res_3979_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg(
    mut v_type_3980_: *mut crate::leanh::LeanObject,
    mut v_k_3981_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_3982_: u8,
    mut v___y_3983_: *mut crate::leanh::LeanObject,
    mut v___y_3984_: *mut crate::leanh::LeanObject,
    mut v___y_3985_: *mut crate::leanh::LeanObject,
    mut v___y_3986_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: u8 = 0;
    let mut v___x_3990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3995_: u8 = 0;
    let mut v___x_3997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3999_: u8 = 0;
    let mut v_a_4000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4003_: u8 = 0;
    let mut v___x_4005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4007_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_3988_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                crate::leanh::lean_closure_set(v___f_3988_, 0, v_k_3981_);
                v___x_3989_ = 0;
                v___x_3990_ = crate::leanh::lean_box(0);
                v___x_3991_ =
                    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(
                        crate::leanh::lean_box(0),
                        v___x_3989_,
                        v___x_3990_,
                        v_type_3980_,
                        v___f_3988_,
                        v_cleanupAnnotations_3982_,
                        v___x_3989_,
                        v___y_3983_,
                        v___y_3984_,
                        v___y_3985_,
                        v___y_3986_,
                    );
                if crate::leanh::lean_obj_tag(v___x_3991_) == 0 {
                    v_a_3992_ = crate::leanh::lean_ctor_get(v___x_3991_, 0);
                    v_isSharedCheck_3999_ = (!crate::leanh::lean_is_exclusive(v___x_3991_)) as u8;
                    if v_isSharedCheck_3999_ == 0 {
                        v___x_3994_ = v___x_3991_;
                        v_isShared_3995_ = v_isSharedCheck_3999_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3992_);
                        crate::leanh::lean_dec(v___x_3991_);
                        v___x_3994_ = crate::leanh::lean_box(0);
                        v_isShared_3995_ = v_isSharedCheck_3999_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4000_ = crate::leanh::lean_ctor_get(v___x_3991_, 0);
                    v_isSharedCheck_4007_ = (!crate::leanh::lean_is_exclusive(v___x_3991_)) as u8;
                    if v_isSharedCheck_4007_ == 0 {
                        v___x_4002_ = v___x_3991_;
                        v_isShared_4003_ = v_isSharedCheck_4007_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4000_);
                        crate::leanh::lean_dec(v___x_3991_);
                        v___x_4002_ = crate::leanh::lean_box(0);
                        v_isShared_4003_ = v_isSharedCheck_4007_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3995_ == 0 {
                    v___x_3997_ = v___x_3994_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3998_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3998_, 0, v_a_3992_);
                    v___x_3997_ = v_reuseFailAlloc_3998_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3997_;
            }
            3 => {
                if v_isShared_4003_ == 0 {
                    v___x_4005_ = v___x_4002_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4006_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4006_, 0, v_a_4000_);
                    v___x_4005_ = v_reuseFailAlloc_4006_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4005_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg___boxed(
    mut v_type_4008_: *mut crate::leanh::LeanObject,
    mut v_k_4009_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_4010_: *mut crate::leanh::LeanObject,
    mut v___y_4011_: *mut crate::leanh::LeanObject,
    mut v___y_4012_: *mut crate::leanh::LeanObject,
    mut v___y_4013_: *mut crate::leanh::LeanObject,
    mut v___y_4014_: *mut crate::leanh::LeanObject,
    mut v___y_4015_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_4016_: u8 = 0;
    let mut v_res_4017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_4016_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_4010_) as u8);
    v_res_4017_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg(v_type_4008_, v_k_4009_, v_cleanupAnnotations_boxed_4016_, v___y_4011_, v___y_4012_, v___y_4013_, v___y_4014_);
    crate::leanh::lean_dec(v___y_4014_);
    crate::leanh::lean_dec_ref(v___y_4013_);
    crate::leanh::lean_dec(v___y_4012_);
    crate::leanh::lean_dec_ref(v___y_4011_);
    return v_res_4017_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0(
    mut v_00_u03b1_4018_: *mut crate::leanh::LeanObject,
    mut v_type_4019_: *mut crate::leanh::LeanObject,
    mut v_k_4020_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_4021_: u8,
    mut v___y_4022_: *mut crate::leanh::LeanObject,
    mut v___y_4023_: *mut crate::leanh::LeanObject,
    mut v___y_4024_: *mut crate::leanh::LeanObject,
    mut v___y_4025_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4027_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg(v_type_4019_, v_k_4020_, v_cleanupAnnotations_4021_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_);
    return v___x_4027_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___boxed(
    mut v_00_u03b1_4028_: *mut crate::leanh::LeanObject,
    mut v_type_4029_: *mut crate::leanh::LeanObject,
    mut v_k_4030_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_4031_: *mut crate::leanh::LeanObject,
    mut v___y_4032_: *mut crate::leanh::LeanObject,
    mut v___y_4033_: *mut crate::leanh::LeanObject,
    mut v___y_4034_: *mut crate::leanh::LeanObject,
    mut v___y_4035_: *mut crate::leanh::LeanObject,
    mut v___y_4036_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_4037_: u8 = 0;
    let mut v_res_4038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_4037_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_4031_) as u8);
    v_res_4038_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0(v_00_u03b1_4028_, v_type_4029_, v_k_4030_, v_cleanupAnnotations_boxed_4037_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_);
    crate::leanh::lean_dec(v___y_4035_);
    crate::leanh::lean_dec_ref(v___y_4034_);
    crate::leanh::lean_dec(v___y_4033_);
    crate::leanh::lean_dec_ref(v___y_4032_);
    return v_res_4038_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0(
    mut v_name_4045_: *mut crate::leanh::LeanObject,
    mut v_x_4046_: *mut crate::leanh::LeanObject,
    mut v_type_4047_: *mut crate::leanh::LeanObject,
    mut v___y_4048_: *mut crate::leanh::LeanObject,
    mut v___y_4049_: *mut crate::leanh::LeanObject,
    mut v___y_4050_: *mut crate::leanh::LeanObject,
    mut v___y_4051_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4053_: u8 = 0;
    let mut v___x_4054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4060_: u8 = 0;
    let mut v_key_4061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4066_: u8 = 0;
    let mut v___x_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4071_: u8 = 0;
    let mut v___x_4072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4076_: u8 = 0;
    let mut v___x_4077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4083_: u8 = 0;
    let mut v___x_4084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4089_: u8 = 0;
    let mut v_a_4090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4093_: u8 = 0;
    let mut v___x_4095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4097_: u8 = 0;
    let mut v_a_4098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4101_: u8 = 0;
    let mut v___x_4103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4105_: u8 = 0;
    let mut v_isSharedCheck_4106_: u8 = 0;
    let mut v_a_4107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4110_: u8 = 0;
    let mut v___x_4112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4114_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4053_ = 0;
                v___x_4054_ = crate::leanh::lean_box((v___x_4053_) as usize);
                crate::leanh::lean_inc(v_name_4045_);
                v___x_4055_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4055_, 0, v_name_4045_);
                crate::leanh::lean_ctor_set(v___x_4055_, 1, v___x_4054_);
                v___x_4056_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(
                    v_type_4047_,
                    v___x_4055_,
                    v___y_4048_,
                    v___y_4049_,
                    v___y_4050_,
                    v___y_4051_,
                );
                if crate::leanh::lean_obj_tag(v___x_4056_) == 0 {
                    v_a_4057_ = crate::leanh::lean_ctor_get(v___x_4056_, 0);
                    v_isSharedCheck_4106_ = (!crate::leanh::lean_is_exclusive(v___x_4056_)) as u8;
                    if v_isSharedCheck_4106_ == 0 {
                        v___x_4059_ = v___x_4056_;
                        v_isShared_4060_ = v_isSharedCheck_4106_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4057_);
                        crate::leanh::lean_dec(v___x_4056_);
                        v___x_4059_ = crate::leanh::lean_box(0);
                        v_isShared_4060_ = v_isSharedCheck_4106_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_name_4045_);
                    v_a_4107_ = crate::leanh::lean_ctor_get(v___x_4056_, 0);
                    v_isSharedCheck_4114_ = (!crate::leanh::lean_is_exclusive(v___x_4056_)) as u8;
                    if v_isSharedCheck_4114_ == 0 {
                        v___x_4109_ = v___x_4056_;
                        v_isShared_4110_ = v_isSharedCheck_4114_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4107_);
                        crate::leanh::lean_dec(v___x_4056_);
                        v___x_4109_ = crate::leanh::lean_box(0);
                        v_isShared_4110_ = v_isSharedCheck_4114_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v_key_4061_ = crate::leanh::lean_ctor_get(v_a_4057_, 0);
                v___x_4062_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4063_ = lean_mk_empty_array_with_capacity(v___x_4062_);
                crate::leanh::lean_inc(v_a_4057_);
                v___x_4064_ = lean_array_push(v___x_4063_, v_a_4057_);
                v___x_4065_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0___closed__2;
                v___x_4066_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_key_4061_, v___x_4065_);
                if v___x_4066_ == 0 {
                    crate::leanh::lean_dec(v_a_4057_);
                    crate::leanh::lean_dec(v_name_4045_);
                    if v_isShared_4060_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4059_, 0, v___x_4064_);
                        v___x_4068_ = v___x_4059_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4069_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4069_, 0, v___x_4064_);
                        v___x_4068_ = v_reuseFailAlloc_4069_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4059_);
                    v___x_4070_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4071_ = 1;
                    v___x_4072_ = crate::leanh::lean_box((v___x_4071_) as usize);
                    crate::leanh::lean_inc(v_name_4045_);
                    v___x_4073_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4073_, 0, v_name_4045_);
                    crate::leanh::lean_ctor_set(v___x_4073_, 1, v___x_4072_);
                    crate::leanh::lean_inc(v_a_4057_);
                    v___x_4074_ = l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg(
                        v_a_4057_,
                        v___x_4070_,
                        v___x_4073_,
                        v___y_4048_,
                        v___y_4049_,
                        v___y_4050_,
                        v___y_4051_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4074_) == 0 {
                        v_a_4075_ = crate::leanh::lean_ctor_get(v___x_4074_, 0);
                        crate::leanh::lean_inc(v_a_4075_);
                        crate::leanh::lean_dec_ref_known(v___x_4074_, 1);
                        v___x_4076_ = 2;
                        v___x_4077_ = crate::leanh::lean_box((v___x_4076_) as usize);
                        v___x_4078_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4078_, 0, v_name_4045_);
                        crate::leanh::lean_ctor_set(v___x_4078_, 1, v___x_4077_);
                        v___x_4079_ = l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg(
                            v_a_4057_,
                            v___x_4062_,
                            v___x_4078_,
                            v___y_4048_,
                            v___y_4049_,
                            v___y_4050_,
                            v___y_4051_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4079_) == 0 {
                            v_a_4080_ = crate::leanh::lean_ctor_get(v___x_4079_, 0);
                            v_isSharedCheck_4089_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4079_)) as u8;
                            if v_isSharedCheck_4089_ == 0 {
                                v___x_4082_ = v___x_4079_;
                                v_isShared_4083_ = v_isSharedCheck_4089_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4080_);
                                crate::leanh::lean_dec(v___x_4079_);
                                v___x_4082_ = crate::leanh::lean_box(0);
                                v_isShared_4083_ = v_isSharedCheck_4089_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_4075_);
                            crate::leanh::lean_dec_ref(v___x_4064_);
                            v_a_4090_ = crate::leanh::lean_ctor_get(v___x_4079_, 0);
                            v_isSharedCheck_4097_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4079_)) as u8;
                            if v_isSharedCheck_4097_ == 0 {
                                v___x_4092_ = v___x_4079_;
                                v_isShared_4093_ = v_isSharedCheck_4097_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4090_);
                                crate::leanh::lean_dec(v___x_4079_);
                                v___x_4092_ = crate::leanh::lean_box(0);
                                v_isShared_4093_ = v_isSharedCheck_4097_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_4064_);
                        crate::leanh::lean_dec(v_a_4057_);
                        crate::leanh::lean_dec(v_name_4045_);
                        v_a_4098_ = crate::leanh::lean_ctor_get(v___x_4074_, 0);
                        v_isSharedCheck_4105_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4074_)) as u8;
                        if v_isSharedCheck_4105_ == 0 {
                            v___x_4100_ = v___x_4074_;
                            v_isShared_4101_ = v_isSharedCheck_4105_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4098_);
                            crate::leanh::lean_dec(v___x_4074_);
                            v___x_4100_ = crate::leanh::lean_box(0);
                            v_isShared_4101_ = v_isSharedCheck_4105_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_4068_;
            }
            3 => {
                v___x_4084_ = lean_array_push(v___x_4064_, v_a_4075_);
                v___x_4085_ = lean_array_push(v___x_4084_, v_a_4080_);
                if v_isShared_4083_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4082_, 0, v___x_4085_);
                    v___x_4087_ = v___x_4082_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4088_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4088_, 0, v___x_4085_);
                    v___x_4087_ = v_reuseFailAlloc_4088_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4087_;
            }
            5 => {
                if v_isShared_4093_ == 0 {
                    v___x_4095_ = v___x_4092_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4096_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4096_, 0, v_a_4090_);
                    v___x_4095_ = v_reuseFailAlloc_4096_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4095_;
            }
            7 => {
                if v_isShared_4101_ == 0 {
                    v___x_4103_ = v___x_4100_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4104_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4104_, 0, v_a_4098_);
                    v___x_4103_ = v_reuseFailAlloc_4104_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4103_;
            }
            9 => {
                if v_isShared_4110_ == 0 {
                    v___x_4112_ = v___x_4109_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4113_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4113_, 0, v_a_4107_);
                    v___x_4112_ = v_reuseFailAlloc_4113_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4112_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0___boxed(
    mut v_name_4115_: *mut crate::leanh::LeanObject,
    mut v_x_4116_: *mut crate::leanh::LeanObject,
    mut v_type_4117_: *mut crate::leanh::LeanObject,
    mut v___y_4118_: *mut crate::leanh::LeanObject,
    mut v___y_4119_: *mut crate::leanh::LeanObject,
    mut v___y_4120_: *mut crate::leanh::LeanObject,
    mut v___y_4121_: *mut crate::leanh::LeanObject,
    mut v___y_4122_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4123_ =
        l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0(
            v_name_4115_,
            v_x_4116_,
            v_type_4117_,
            v___y_4118_,
            v___y_4119_,
            v___y_4120_,
            v___y_4121_,
        );
    crate::leanh::lean_dec(v___y_4121_);
    crate::leanh::lean_dec_ref(v___y_4120_);
    crate::leanh::lean_dec(v___y_4119_);
    crate::leanh::lean_dec_ref(v___y_4118_);
    crate::leanh::lean_dec_ref(v_x_4116_);
    return v_res_4123_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport(
    mut v_name_4126_: *mut crate::leanh::LeanObject,
    mut v_constInfo_4127_: *mut crate::leanh::LeanObject,
    mut v_a_4128_: *mut crate::leanh::LeanObject,
    mut v_a_4129_: *mut crate::leanh::LeanObject,
    mut v_a_4130_: *mut crate::leanh::LeanObject,
    mut v_a_4131_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4135_: u8 = 0;
    v___x_4133_ = lean_st_ref_get(v_a_4131_);
    v_env_4134_ = crate::leanh::lean_ctor_get(v___x_4133_, 0);
    crate::leanh::lean_inc_ref(v_env_4134_);
    crate::leanh::lean_dec(v___x_4133_);
    crate::leanh::lean_inc(v_name_4126_);
    v___x_4135_ = l_Lean_Linter_isDeprecated(v_env_4134_, v_name_4126_);
    if v___x_4135_ == 0 {
        let mut v___x_4136_: u8 = 0;
        crate::leanh::lean_inc(v_name_4126_);
        v___x_4136_ = l_Lean_Name_isMetaprogramming(v_name_4126_);
        if v___x_4136_ == 0 {
            let mut v___f_4137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___f_4137_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
            crate::leanh::lean_closure_set(v___f_4137_, 0, v_name_4126_);
            v___x_4138_ = l_Lean_ConstantInfo_type(v_constInfo_4127_);
            v___x_4139_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg(v___x_4138_, v___f_4137_, v___x_4136_, v_a_4128_, v_a_4129_, v_a_4130_, v_a_4131_);
            return v___x_4139_;
        } else {
            let mut v___x_4140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_name_4126_);
            v___x_4140_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___closed__0;
            v___x_4141_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_4141_, 0, v___x_4140_);
            return v___x_4141_;
        }
    } else {
        let mut v___x_4142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_name_4126_);
        v___x_4142_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___closed__0;
        v___x_4143_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4143_, 0, v___x_4142_);
        return v___x_4143_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___boxed(
    mut v_name_4144_: *mut crate::leanh::LeanObject,
    mut v_constInfo_4145_: *mut crate::leanh::LeanObject,
    mut v_a_4146_: *mut crate::leanh::LeanObject,
    mut v_a_4147_: *mut crate::leanh::LeanObject,
    mut v_a_4148_: *mut crate::leanh::LeanObject,
    mut v_a_4149_: *mut crate::leanh::LeanObject,
    mut v_a_4150_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4151_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport(
        v_name_4144_,
        v_constInfo_4145_,
        v_a_4146_,
        v_a_4147_,
        v_a_4148_,
        v_a_4149_,
    );
    crate::leanh::lean_dec(v_a_4149_);
    crate::leanh::lean_dec_ref(v_a_4148_);
    crate::leanh::lean_dec(v_a_4147_);
    crate::leanh::lean_dec_ref(v_a_4146_);
    crate::leanh::lean_dec_ref(v_constInfo_4145_);
    return v_res_4151_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_641666102____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4153_ = crate::leanh::lean_box(0);
    v___x_4154_ = lean_st_mk_ref(v___x_4153_);
    v___x_4155_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4155_, 0, v___x_4154_);
    return v___x_4155_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_641666102____hygCtx___hyg_2____boxed(
    mut v_a_4156_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4157_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_641666102____hygCtx___hyg_2_();
    return v_res_4157_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_instInhabitedLibSearchState()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4158_ =
        l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_defaultLibSearchState;
    return v___x_4158_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___lam__0_00___x40_Lean_Meta_Tactic_LibrarySearch_2561004661____hygCtx___hyg_2_(
    mut v___x_4159_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4161_ = lean_st_mk_ref(v___x_4159_);
    v___x_4162_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4162_, 0, v___x_4161_);
    return v___x_4162_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___lam__0_00___x40_Lean_Meta_Tactic_LibrarySearch_2561004661____hygCtx___hyg_2____boxed(
    mut v___x_4163_: *mut crate::leanh::LeanObject,
    mut v___y_4164_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4165_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___lam__0_00___x40_Lean_Meta_Tactic_LibrarySearch_2561004661____hygCtx___hyg_2_(v___x_4163_);
    return v_res_4165_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_2561004661____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4169_ = crate::leanh::lean_box(0);
    v___f_4170_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__0_00___x40_Lean_Meta_Tactic_LibrarySearch_2561004661____hygCtx___hyg_2_;
    v___x_4171_ = crate::leanh::lean_box(2);
    v___x_4172_ = l_Lean_registerEnvExtension___redArg(v___f_4170_, v___x_4169_, v___x_4171_);
    return v___x_4172_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_2561004661____hygCtx___hyg_2____boxed(
    mut v_a_4173_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4174_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_2561004661____hygCtx___hyg_2_();
    return v_res_4174_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_constantsPerImportTask()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4200_ = crate::leanh::lean_unsigned_to_nat(6500);
    return v___x_4200_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___lam__0_00___x40_Lean_Meta_Tactic_LibrarySearch_956453063____hygCtx___hyg_2_(
    mut v___x_4201_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4203_ = lean_st_mk_ref(v___x_4201_);
    v___x_4204_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4204_, 0, v___x_4203_);
    return v___x_4204_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___lam__0_00___x40_Lean_Meta_Tactic_LibrarySearch_956453063____hygCtx___hyg_2____boxed(
    mut v___x_4205_: *mut crate::leanh::LeanObject,
    mut v___y_4206_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4207_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___lam__0_00___x40_Lean_Meta_Tactic_LibrarySearch_956453063____hygCtx___hyg_2_(v___x_4205_);
    return v_res_4207_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_956453063____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4211_ = crate::leanh::lean_box(0);
    v___f_4212_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__0_00___x40_Lean_Meta_Tactic_LibrarySearch_956453063____hygCtx___hyg_2_;
    v___x_4213_ = crate::leanh::lean_box(2);
    v___x_4214_ = l_Lean_registerEnvExtension___redArg(v___f_4212_, v___x_4211_, v___x_4213_);
    return v___x_4214_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_956453063____hygCtx___hyg_2____boxed(
    mut v_a_4215_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4216_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_956453063____hygCtx___hyg_2_();
    return v_res_4216_;
}
pub unsafe fn l_Lean_Meta_LibrarySearch_libSearchFindDecls(
    mut v_ty_4218_: *mut crate::leanh::LeanObject,
    mut v_a_4219_: *mut crate::leanh::LeanObject,
    mut v_a_4220_: *mut crate::leanh::LeanObject,
    mut v_a_4221_: *mut crate::leanh::LeanObject,
    mut v_a_4222_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_4229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4224_ = crate::leanh::lean_box(0);
    v___x_4225_ = lean_st_mk_ref(v___x_4224_);
    v___x_4226_ = lean_st_ref_get(v_a_4222_);
    v_env_4227_ = crate::leanh::lean_ctor_get(v___x_4226_, 0);
    crate::leanh::lean_inc_ref(v_env_4227_);
    crate::leanh::lean_dec(v___x_4226_);
    v___x_4228_ =
        l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_starLemmasExt;
    v_asyncMode_4229_ = crate::leanh::lean_ctor_get(v___x_4228_, 2);
    v___x_4230_ = crate::leanh::lean_box(0);
    v___x_4231_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(
        v___x_4225_,
        v___x_4228_,
        v_env_4227_,
        v_asyncMode_4229_,
        v___x_4230_,
    );
    crate::leanh::lean_dec(v___x_4225_);
    v___x_4232_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_ext;
    v___x_4233_ = l_Lean_Meta_LibrarySearch_libSearchFindDecls___closed__0;
    v___x_4234_ = l_Lean_Meta_LibrarySearch_droppedKeys;
    v___x_4235_ = crate::leanh::lean_unsigned_to_nat(6500);
    v___x_4236_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4236_, 0, v___x_4231_);
    v___x_4237_ = l_Lean_Meta_LazyDiscrTree_findMatches___redArg(
        v___x_4232_,
        v___x_4233_,
        v___x_4234_,
        v___x_4235_,
        v___x_4236_,
        v_ty_4218_,
        v_a_4219_,
        v_a_4220_,
        v_a_4221_,
        v_a_4222_,
    );
    return v___x_4237_;
}
pub unsafe fn l_Lean_Meta_LibrarySearch_libSearchFindDecls___boxed(
    mut v_ty_4238_: *mut crate::leanh::LeanObject,
    mut v_a_4239_: *mut crate::leanh::LeanObject,
    mut v_a_4240_: *mut crate::leanh::LeanObject,
    mut v_a_4241_: *mut crate::leanh::LeanObject,
    mut v_a_4242_: *mut crate::leanh::LeanObject,
    mut v_a_4243_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4244_ = l_Lean_Meta_LibrarySearch_libSearchFindDecls(
        v_ty_4238_, v_a_4239_, v_a_4240_, v_a_4241_, v_a_4242_,
    );
    crate::leanh::lean_dec(v_a_4242_);
    crate::leanh::lean_dec_ref(v_a_4241_);
    crate::leanh::lean_dec(v_a_4240_);
    crate::leanh::lean_dec_ref(v_a_4239_);
    return v_res_4244_;
}
pub unsafe fn _init_l_Lean_Meta_LibrarySearch_getStarLemmas___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4248_ = crate::leanh::lean_box(0);
    v___x_4249_ = l_Lean_Meta_LibrarySearch_getStarLemmas___closed__1;
    v___x_4250_ = l_Lean_mkConst(v___x_4249_, v___x_4248_);
    return v___x_4250_;
}
pub unsafe fn l_Lean_Meta_LibrarySearch_getStarLemmas(
    mut v_a_4253_: *mut crate::leanh::LeanObject,
    mut v_a_4254_: *mut crate::leanh::LeanObject,
    mut v_a_4255_: *mut crate::leanh::LeanObject,
    mut v_a_4256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_4263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4271_: u8 = 0;
    let mut v___x_4272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4281_: u8 = 0;
    let mut v_unused_4282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4286_: u8 = 0;
    let mut v___x_4288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4290_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4258_ = crate::leanh::lean_box(0);
                v___x_4259_ = lean_st_mk_ref(v___x_4258_);
                v___x_4260_ = lean_st_ref_get(v_a_4256_);
                v_env_4261_ = crate::leanh::lean_ctor_get(v___x_4260_, 0);
                crate::leanh::lean_inc_ref(v_env_4261_);
                crate::leanh::lean_dec(v___x_4260_);
                v___x_4262_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_starLemmasExt;
                v_asyncMode_4263_ = crate::leanh::lean_ctor_get(v___x_4262_, 2);
                v___x_4264_ = crate::leanh::lean_box(0);
                v___x_4265_ =
                    l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(
                        v___x_4259_,
                        v___x_4262_,
                        v_env_4261_,
                        v_asyncMode_4263_,
                        v___x_4264_,
                    );
                crate::leanh::lean_dec(v___x_4259_);
                v___x_4266_ = lean_st_ref_get(v___x_4265_);
                if crate::leanh::lean_obj_tag(v___x_4266_) == 0 {
                    v___x_4267_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_LibrarySearch_getStarLemmas___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_LibrarySearch_getStarLemmas___closed__2_once
                        ),
                        _init_l_Lean_Meta_LibrarySearch_getStarLemmas___closed__2,
                    );
                    v___x_4268_ = l_Lean_Meta_LibrarySearch_libSearchFindDecls(
                        v___x_4267_,
                        v_a_4253_,
                        v_a_4254_,
                        v_a_4255_,
                        v_a_4256_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4268_) == 0 {
                        v_isSharedCheck_4281_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4268_)) as u8;
                        if v_isSharedCheck_4281_ == 0 {
                            v_unused_4282_ = crate::leanh::lean_ctor_get(v___x_4268_, 0);
                            crate::leanh::lean_dec(v_unused_4282_);
                            v___x_4270_ = v___x_4268_;
                            v_isShared_4271_ = v_isSharedCheck_4281_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_4268_);
                            v___x_4270_ = crate::leanh::lean_box(0);
                            v_isShared_4271_ = v_isSharedCheck_4281_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_4265_);
                        return v___x_4268_;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4265_);
                    v_val_4283_ = crate::leanh::lean_ctor_get(v___x_4266_, 0);
                    v_isSharedCheck_4290_ = (!crate::leanh::lean_is_exclusive(v___x_4266_)) as u8;
                    if v_isSharedCheck_4290_ == 0 {
                        v___x_4285_ = v___x_4266_;
                        v_isShared_4286_ = v_isSharedCheck_4290_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4283_);
                        crate::leanh::lean_dec(v___x_4266_);
                        v___x_4285_ = crate::leanh::lean_box(0);
                        v_isShared_4286_ = v_isSharedCheck_4290_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4272_ = lean_st_ref_get(v___x_4265_);
                crate::leanh::lean_dec(v___x_4265_);
                if crate::leanh::lean_obj_tag(v___x_4272_) == 0 {
                    v___x_4273_ = l_Lean_Meta_LibrarySearch_getStarLemmas___closed__3;
                    if v_isShared_4271_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4270_, 0, v___x_4273_);
                        v___x_4275_ = v___x_4270_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4276_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4276_, 0, v___x_4273_);
                        v___x_4275_ = v_reuseFailAlloc_4276_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_val_4277_ = crate::leanh::lean_ctor_get(v___x_4272_, 0);
                    crate::leanh::lean_inc(v_val_4277_);
                    crate::leanh::lean_dec_ref_known(v___x_4272_, 1);
                    if v_isShared_4271_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4270_, 0, v_val_4277_);
                        v___x_4279_ = v___x_4270_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4280_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4280_, 0, v_val_4277_);
                        v___x_4279_ = v_reuseFailAlloc_4280_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4275_;
            }
            3 => {
                return v___x_4279_;
            }
            4 => {
                if v_isShared_4286_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4285_, 0);
                    v___x_4288_ = v___x_4285_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4289_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4289_, 0, v_val_4283_);
                    v___x_4288_ = v_reuseFailAlloc_4289_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4288_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_LibrarySearch_getStarLemmas___boxed(
    mut v_a_4291_: *mut crate::leanh::LeanObject,
    mut v_a_4292_: *mut crate::leanh::LeanObject,
    mut v_a_4293_: *mut crate::leanh::LeanObject,
    mut v_a_4294_: *mut crate::leanh::LeanObject,
    mut v_a_4295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4296_ =
        l_Lean_Meta_LibrarySearch_getStarLemmas(v_a_4291_, v_a_4292_, v_a_4293_, v_a_4294_);
    crate::leanh::lean_dec(v_a_4294_);
    crate::leanh::lean_dec_ref(v_a_4293_);
    crate::leanh::lean_dec(v_a_4292_);
    crate::leanh::lean_dec_ref(v_a_4291_);
    return v_res_4296_;
}
pub unsafe fn l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg___lam__0(
    mut v___x_4297_: u8,
    mut v___x_4298_: *mut crate::leanh::LeanObject,
    mut v___y_4299_: *mut crate::leanh::LeanObject,
    mut v___y_4300_: *mut crate::leanh::LeanObject,
    mut v___y_4301_: *mut crate::leanh::LeanObject,
    mut v___y_4302_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4308_: u8 = 0;
    let mut v___x_4309_: u8 = 0;
    let mut v___x_4310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4314_: u8 = 0;
    let mut v_a_4315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4318_: u8 = 0;
    let mut v___x_4320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4322_: u8 = 0;
    let mut v___x_4323_: u8 = 0;
    let mut v___x_4324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v___x_4297_ == 0 {
                    v___x_4304_ = l_Lean_getRemainingHeartbeats___redArg(v___y_4301_);
                    if crate::leanh::lean_obj_tag(v___x_4304_) == 0 {
                        v_a_4305_ = crate::leanh::lean_ctor_get(v___x_4304_, 0);
                        v_isSharedCheck_4314_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4304_)) as u8;
                        if v_isSharedCheck_4314_ == 0 {
                            v___x_4307_ = v___x_4304_;
                            v_isShared_4308_ = v_isSharedCheck_4314_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4305_);
                            crate::leanh::lean_dec(v___x_4304_);
                            v___x_4307_ = crate::leanh::lean_box(0);
                            v_isShared_4308_ = v_isSharedCheck_4314_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4315_ = crate::leanh::lean_ctor_get(v___x_4304_, 0);
                        v_isSharedCheck_4322_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4304_)) as u8;
                        if v_isSharedCheck_4322_ == 0 {
                            v___x_4317_ = v___x_4304_;
                            v_isShared_4318_ = v_isSharedCheck_4322_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4315_);
                            crate::leanh::lean_dec(v___x_4304_);
                            v___x_4317_ = crate::leanh::lean_box(0);
                            v_isShared_4318_ = v_isSharedCheck_4322_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v___x_4323_ = 0;
                    v___x_4324_ = crate::leanh::lean_box((v___x_4323_) as usize);
                    v___x_4325_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4325_, 0, v___x_4324_);
                    return v___x_4325_;
                }
            }
            1 => {
                v___x_4309_ = lean_nat_dec_lt(v_a_4305_, v___x_4298_);
                crate::leanh::lean_dec(v_a_4305_);
                v___x_4310_ = crate::leanh::lean_box((v___x_4309_) as usize);
                if v_isShared_4308_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4307_, 0, v___x_4310_);
                    v___x_4312_ = v___x_4307_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4313_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4313_, 0, v___x_4310_);
                    v___x_4312_ = v_reuseFailAlloc_4313_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4312_;
            }
            3 => {
                if v_isShared_4318_ == 0 {
                    v___x_4320_ = v___x_4317_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4321_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4321_, 0, v_a_4315_);
                    v___x_4320_ = v_reuseFailAlloc_4321_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4320_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg___lam__0___boxed(
    mut v___x_4326_: *mut crate::leanh::LeanObject,
    mut v___x_4327_: *mut crate::leanh::LeanObject,
    mut v___y_4328_: *mut crate::leanh::LeanObject,
    mut v___y_4329_: *mut crate::leanh::LeanObject,
    mut v___y_4330_: *mut crate::leanh::LeanObject,
    mut v___y_4331_: *mut crate::leanh::LeanObject,
    mut v___y_4332_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_643__boxed_4333_: u8 = 0;
    let mut v_res_4334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_643__boxed_4333_ = (crate::leanh::lean_unbox(v___x_4326_) as u8);
    v_res_4334_ = l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg___lam__0(
        v___x_643__boxed_4333_,
        v___x_4327_,
        v___y_4328_,
        v___y_4329_,
        v___y_4330_,
        v___y_4331_,
    );
    crate::leanh::lean_dec(v___y_4331_);
    crate::leanh::lean_dec_ref(v___y_4330_);
    crate::leanh::lean_dec(v___y_4329_);
    crate::leanh::lean_dec_ref(v___y_4328_);
    crate::leanh::lean_dec(v___x_4327_);
    return v_res_4334_;
}
pub unsafe fn l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg(
    mut v_leavePercent_4335_: *mut crate::leanh::LeanObject,
    mut v_a_4336_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4344_: u8 = 0;
    let mut v___x_4345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4349_: u8 = 0;
    let mut v___x_4350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4355_: u8 = 0;
    let mut v_a_4356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4359_: u8 = 0;
    let mut v___x_4361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4363_: u8 = 0;
    let mut v_a_4364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4367_: u8 = 0;
    let mut v___x_4369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4371_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4338_ = l_Lean_getMaxHeartbeats___redArg(v_a_4336_);
                if crate::leanh::lean_obj_tag(v___x_4338_) == 0 {
                    v_a_4339_ = crate::leanh::lean_ctor_get(v___x_4338_, 0);
                    crate::leanh::lean_inc(v_a_4339_);
                    crate::leanh::lean_dec_ref_known(v___x_4338_, 1);
                    v___x_4340_ = l_Lean_getRemainingHeartbeats___redArg(v_a_4336_);
                    if crate::leanh::lean_obj_tag(v___x_4340_) == 0 {
                        v_a_4341_ = crate::leanh::lean_ctor_get(v___x_4340_, 0);
                        v_isSharedCheck_4355_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4340_)) as u8;
                        if v_isSharedCheck_4355_ == 0 {
                            v___x_4343_ = v___x_4340_;
                            v_isShared_4344_ = v_isSharedCheck_4355_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4341_);
                            crate::leanh::lean_dec(v___x_4340_);
                            v___x_4343_ = crate::leanh::lean_box(0);
                            v_isShared_4344_ = v_isSharedCheck_4355_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_4339_);
                        v_a_4356_ = crate::leanh::lean_ctor_get(v___x_4340_, 0);
                        v_isSharedCheck_4363_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4340_)) as u8;
                        if v_isSharedCheck_4363_ == 0 {
                            v___x_4358_ = v___x_4340_;
                            v_isShared_4359_ = v_isSharedCheck_4363_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4356_);
                            crate::leanh::lean_dec(v___x_4340_);
                            v___x_4358_ = crate::leanh::lean_box(0);
                            v_isShared_4359_ = v_isSharedCheck_4363_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_4364_ = crate::leanh::lean_ctor_get(v___x_4338_, 0);
                    v_isSharedCheck_4371_ = (!crate::leanh::lean_is_exclusive(v___x_4338_)) as u8;
                    if v_isSharedCheck_4371_ == 0 {
                        v___x_4366_ = v___x_4338_;
                        v_isShared_4367_ = v_isSharedCheck_4371_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4364_);
                        crate::leanh::lean_dec(v___x_4338_);
                        v___x_4366_ = crate::leanh::lean_box(0);
                        v_isShared_4367_ = v_isSharedCheck_4371_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4345_ = lean_nat_mul(v_a_4341_, v_leavePercent_4335_);
                crate::leanh::lean_dec(v_a_4341_);
                v___x_4346_ = crate::leanh::lean_unsigned_to_nat(100);
                v___x_4347_ = lean_nat_div(v___x_4345_, v___x_4346_);
                crate::leanh::lean_dec(v___x_4345_);
                v___x_4348_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4349_ = lean_nat_dec_eq(v_a_4339_, v___x_4348_);
                crate::leanh::lean_dec(v_a_4339_);
                v___x_4350_ = crate::leanh::lean_box((v___x_4349_) as usize);
                v___y_4351_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    7,
                    2,
                );
                crate::leanh::lean_closure_set(v___y_4351_, 0, v___x_4350_);
                crate::leanh::lean_closure_set(v___y_4351_, 1, v___x_4347_);
                if v_isShared_4344_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4343_, 0, v___y_4351_);
                    v___x_4353_ = v___x_4343_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4354_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4354_, 0, v___y_4351_);
                    v___x_4353_ = v_reuseFailAlloc_4354_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4353_;
            }
            3 => {
                if v_isShared_4359_ == 0 {
                    v___x_4361_ = v___x_4358_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4362_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4362_, 0, v_a_4356_);
                    v___x_4361_ = v_reuseFailAlloc_4362_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4361_;
            }
            5 => {
                if v_isShared_4367_ == 0 {
                    v___x_4369_ = v___x_4366_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4370_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4370_, 0, v_a_4364_);
                    v___x_4369_ = v_reuseFailAlloc_4370_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4369_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg___boxed(
    mut v_leavePercent_4372_: *mut crate::leanh::LeanObject,
    mut v_a_4373_: *mut crate::leanh::LeanObject,
    mut v_a_4374_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4375_ =
        l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg(v_leavePercent_4372_, v_a_4373_);
    crate::leanh::lean_dec_ref(v_a_4373_);
    crate::leanh::lean_dec(v_leavePercent_4372_);
    return v_res_4375_;
}
pub unsafe fn l_Lean_Meta_LibrarySearch_mkHeartbeatCheck(
    mut v_leavePercent_4376_: *mut crate::leanh::LeanObject,
    mut v_a_4377_: *mut crate::leanh::LeanObject,
    mut v_a_4378_: *mut crate::leanh::LeanObject,
    mut v_a_4379_: *mut crate::leanh::LeanObject,
    mut v_a_4380_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4382_ =
        l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg(v_leavePercent_4376_, v_a_4379_);
    return v___x_4382_;
}
pub unsafe fn l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___boxed(
    mut v_leavePercent_4383_: *mut crate::leanh::LeanObject,
    mut v_a_4384_: *mut crate::leanh::LeanObject,
    mut v_a_4385_: *mut crate::leanh::LeanObject,
    mut v_a_4386_: *mut crate::leanh::LeanObject,
    mut v_a_4387_: *mut crate::leanh::LeanObject,
    mut v_a_4388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4389_ = l_Lean_Meta_LibrarySearch_mkHeartbeatCheck(
        v_leavePercent_4383_,
        v_a_4384_,
        v_a_4385_,
        v_a_4386_,
        v_a_4387_,
    );
    crate::leanh::lean_dec(v_a_4387_);
    crate::leanh::lean_dec_ref(v_a_4386_);
    crate::leanh::lean_dec(v_a_4385_);
    crate::leanh::lean_dec_ref(v_a_4384_);
    crate::leanh::lean_dec(v_leavePercent_4383_);
    return v_res_4389_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1___redArg(
    mut v_upperBound_4390_: *mut crate::leanh::LeanObject,
    mut v_x_4391_: *mut crate::leanh::LeanObject,
    mut v_f_4392_: *mut crate::leanh::LeanObject,
    mut v_y_4393_: *mut crate::leanh::LeanObject,
    mut v_g_4394_: *mut crate::leanh::LeanObject,
    mut v_a_4395_: *mut crate::leanh::LeanObject,
    mut v_b_4396_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4397_: u8 = 0;
    let mut v___x_4398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4397_ = lean_nat_dec_lt(v_a_4395_, v_upperBound_4390_);
                if v___x_4397_ == 0 {
                    crate::leanh::lean_dec(v_a_4395_);
                    crate::leanh::lean_dec(v_g_4394_);
                    crate::leanh::lean_dec(v_f_4392_);
                    return v_b_4396_;
                } else {
                    v___x_4398_ = lean_array_fget_borrowed(v_x_4391_, v_a_4395_);
                    crate::leanh::lean_inc(v_f_4392_);
                    crate::leanh::lean_inc(v___x_4398_);
                    v___x_4399_ = crate::leanh::lean_apply_1(v_f_4392_, v___x_4398_);
                    v___x_4400_ = lean_array_push(v_b_4396_, v___x_4399_);
                    v___x_4401_ = lean_array_fget_borrowed(v_y_4393_, v_a_4395_);
                    crate::leanh::lean_inc(v_g_4394_);
                    crate::leanh::lean_inc(v___x_4401_);
                    v___x_4402_ = crate::leanh::lean_apply_1(v_g_4394_, v___x_4401_);
                    v___x_4403_ = lean_array_push(v___x_4400_, v___x_4402_);
                    v___x_4404_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4405_ = lean_nat_add(v_a_4395_, v___x_4404_);
                    crate::leanh::lean_dec(v_a_4395_);
                    v_a_4395_ = v___x_4405_;
                    v_b_4396_ = v___x_4403_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1___redArg___boxed(
    mut v_upperBound_4407_: *mut crate::leanh::LeanObject,
    mut v_x_4408_: *mut crate::leanh::LeanObject,
    mut v_f_4409_: *mut crate::leanh::LeanObject,
    mut v_y_4410_: *mut crate::leanh::LeanObject,
    mut v_g_4411_: *mut crate::leanh::LeanObject,
    mut v_a_4412_: *mut crate::leanh::LeanObject,
    mut v_b_4413_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4414_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1___redArg(v_upperBound_4407_, v_x_4408_, v_f_4409_, v_y_4410_, v_g_4411_, v_a_4412_, v_b_4413_);
    crate::leanh::lean_dec_ref(v_y_4410_);
    crate::leanh::lean_dec_ref(v_x_4408_);
    crate::leanh::lean_dec(v_upperBound_4407_);
    return v_res_4414_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___redArg(
    mut v_g_4415_: *mut crate::leanh::LeanObject,
    mut v_sz_4416_: usize,
    mut v_i_4417_: usize,
    mut v_bs_4418_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4419_: u8 = 0;
    let mut v_v_4420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4424_: usize = 0;
    let mut v___x_4425_: usize = 0;
    let mut v___x_4426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4419_ = lean_usize_dec_lt(v_i_4417_, v_sz_4416_);
                if v___x_4419_ == 0 {
                    crate::leanh::lean_dec(v_g_4415_);
                    return v_bs_4418_;
                } else {
                    v_v_4420_ = lean_array_uget(v_bs_4418_, v_i_4417_);
                    v___x_4421_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_4422_ = lean_array_uset(v_bs_4418_, v_i_4417_, v___x_4421_);
                    crate::leanh::lean_inc(v_g_4415_);
                    v___x_4423_ = crate::leanh::lean_apply_1(v_g_4415_, v_v_4420_);
                    v___x_4424_ = 1usize;
                    v___x_4425_ = lean_usize_add(v_i_4417_, v___x_4424_);
                    v___x_4426_ = lean_array_uset(v_bs_x27_4422_, v_i_4417_, v___x_4423_);
                    v_i_4417_ = v___x_4425_;
                    v_bs_4418_ = v___x_4426_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___redArg___boxed(
    mut v_g_4428_: *mut crate::leanh::LeanObject,
    mut v_sz_4429_: *mut crate::leanh::LeanObject,
    mut v_i_4430_: *mut crate::leanh::LeanObject,
    mut v_bs_4431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4432_: usize = 0;
    let mut v_i_boxed_4433_: usize = 0;
    let mut v_res_4434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4432_ = crate::leanh::lean_unbox_usize(v_sz_4429_);
    crate::leanh::lean_dec(v_sz_4429_);
    v_i_boxed_4433_ = crate::leanh::lean_unbox_usize(v_i_4430_);
    crate::leanh::lean_dec(v_i_4430_);
    v_res_4434_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___redArg(v_g_4428_, v_sz_boxed_4432_, v_i_boxed_4433_, v_bs_4431_);
    return v_res_4434_;
}
pub unsafe fn l_Lean_Meta_LibrarySearch_interleaveWith___redArg(
    mut v_f_4435_: *mut crate::leanh::LeanObject,
    mut v_x_4436_: *mut crate::leanh::LeanObject,
    mut v_g_4437_: *mut crate::leanh::LeanObject,
    mut v_y_4438_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_4442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4445_: u8 = 0;
    let mut v___x_4446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4449_: usize = 0;
    let mut v___x_4450_: usize = 0;
    let mut v___x_4451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4454_: usize = 0;
    let mut v___x_4455_: usize = 0;
    let mut v___x_4456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4458_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4439_ = lean_array_get_size(v_x_4436_);
                v___x_4440_ = lean_array_get_size(v_y_4438_);
                v___x_4441_ = lean_nat_add(v___x_4439_, v___x_4440_);
                v_res_4442_ = lean_mk_empty_array_with_capacity(v___x_4441_);
                crate::leanh::lean_dec(v___x_4441_);
                v___x_4458_ = lean_nat_dec_le(v___x_4439_, v___x_4440_);
                if v___x_4458_ == 0 {
                    v___y_4444_ = v___x_4440_;
                    state = 1;
                    continue;
                } else {
                    v___y_4444_ = v___x_4439_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4445_ = lean_nat_dec_lt(v___y_4444_, v___x_4439_);
                v___x_4446_ = crate::leanh::lean_unsigned_to_nat(0);
                crate::leanh::lean_inc(v_g_4437_);
                crate::leanh::lean_inc(v_f_4435_);
                v___x_4447_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1___redArg(v___y_4444_, v_x_4436_, v_f_4435_, v_y_4438_, v_g_4437_, v___x_4446_, v_res_4442_);
                if v___x_4445_ == 0 {
                    crate::leanh::lean_dec(v_f_4435_);
                    v___x_4448_ = l_Array_extract___redArg(v_y_4438_, v___y_4444_, v___x_4440_);
                    v_sz_4449_ = lean_array_size(v___x_4448_);
                    v___x_4450_ = 0usize;
                    v___x_4451_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___redArg(v_g_4437_, v_sz_4449_, v___x_4450_, v___x_4448_);
                    v___x_4452_ = l_Array_append___redArg(v___x_4447_, v___x_4451_);
                    crate::leanh::lean_dec_ref(v___x_4451_);
                    return v___x_4452_;
                } else {
                    crate::leanh::lean_dec(v_g_4437_);
                    v___x_4453_ = l_Array_extract___redArg(v_x_4436_, v___y_4444_, v___x_4439_);
                    v_sz_4454_ = lean_array_size(v___x_4453_);
                    v___x_4455_ = 0usize;
                    v___x_4456_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___redArg(v_f_4435_, v_sz_4454_, v___x_4455_, v___x_4453_);
                    v___x_4457_ = l_Array_append___redArg(v___x_4447_, v___x_4456_);
                    crate::leanh::lean_dec_ref(v___x_4456_);
                    return v___x_4457_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_LibrarySearch_interleaveWith___redArg___boxed(
    mut v_f_4459_: *mut crate::leanh::LeanObject,
    mut v_x_4460_: *mut crate::leanh::LeanObject,
    mut v_g_4461_: *mut crate::leanh::LeanObject,
    mut v_y_4462_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4463_ = l_Lean_Meta_LibrarySearch_interleaveWith___redArg(
        v_f_4459_, v_x_4460_, v_g_4461_, v_y_4462_,
    );
    crate::leanh::lean_dec_ref(v_y_4462_);
    crate::leanh::lean_dec_ref(v_x_4460_);
    return v_res_4463_;
}
pub unsafe fn l_Lean_Meta_LibrarySearch_interleaveWith(
    mut v_00_u03b1_4464_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4465_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_4466_: *mut crate::leanh::LeanObject,
    mut v_f_4467_: *mut crate::leanh::LeanObject,
    mut v_x_4468_: *mut crate::leanh::LeanObject,
    mut v_g_4469_: *mut crate::leanh::LeanObject,
    mut v_y_4470_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4471_ = l_Lean_Meta_LibrarySearch_interleaveWith___redArg(
        v_f_4467_, v_x_4468_, v_g_4469_, v_y_4470_,
    );
    return v___x_4471_;
}
pub unsafe fn l_Lean_Meta_LibrarySearch_interleaveWith___boxed(
    mut v_00_u03b1_4472_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4473_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_4474_: *mut crate::leanh::LeanObject,
    mut v_f_4475_: *mut crate::leanh::LeanObject,
    mut v_x_4476_: *mut crate::leanh::LeanObject,
    mut v_g_4477_: *mut crate::leanh::LeanObject,
    mut v_y_4478_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4479_ = l_Lean_Meta_LibrarySearch_interleaveWith(
        v_00_u03b1_4472_,
        v_00_u03b2_4473_,
        v_00_u03b3_4474_,
        v_f_4475_,
        v_x_4476_,
        v_g_4477_,
        v_y_4478_,
    );
    crate::leanh::lean_dec_ref(v_y_4478_);
    crate::leanh::lean_dec_ref(v_x_4476_);
    return v_res_4479_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0(
    mut v_00_u03b2_4480_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_4481_: *mut crate::leanh::LeanObject,
    mut v_g_4482_: *mut crate::leanh::LeanObject,
    mut v_sz_4483_: usize,
    mut v_i_4484_: usize,
    mut v_bs_4485_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4486_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___redArg(v_g_4482_, v_sz_4483_, v_i_4484_, v_bs_4485_);
    return v___x_4486_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___boxed(
    mut v_00_u03b2_4487_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_4488_: *mut crate::leanh::LeanObject,
    mut v_g_4489_: *mut crate::leanh::LeanObject,
    mut v_sz_4490_: *mut crate::leanh::LeanObject,
    mut v_i_4491_: *mut crate::leanh::LeanObject,
    mut v_bs_4492_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4493_: usize = 0;
    let mut v_i_boxed_4494_: usize = 0;
    let mut v_res_4495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4493_ = crate::leanh::lean_unbox_usize(v_sz_4490_);
    crate::leanh::lean_dec(v_sz_4490_);
    v_i_boxed_4494_ = crate::leanh::lean_unbox_usize(v_i_4491_);
    crate::leanh::lean_dec(v_i_4491_);
    v_res_4495_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0(v_00_u03b2_4487_, v_00_u03b3_4488_, v_g_4489_, v_sz_boxed_4493_, v_i_boxed_4494_, v_bs_4492_);
    return v_res_4495_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1(
    mut v_00_u03b3_4496_: *mut crate::leanh::LeanObject,
    mut v_upperBound_4497_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_4498_: *mut crate::leanh::LeanObject,
    mut v_x_4499_: *mut crate::leanh::LeanObject,
    mut v_f_4500_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4501_: *mut crate::leanh::LeanObject,
    mut v_y_4502_: *mut crate::leanh::LeanObject,
    mut v_g_4503_: *mut crate::leanh::LeanObject,
    mut v_inst_4504_: *mut crate::leanh::LeanObject,
    mut v_R_4505_: *mut crate::leanh::LeanObject,
    mut v_a_4506_: *mut crate::leanh::LeanObject,
    mut v_b_4507_: *mut crate::leanh::LeanObject,
    mut v_c_4508_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4509_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1___redArg(v_upperBound_4497_, v_x_4499_, v_f_4500_, v_y_4502_, v_g_4503_, v_a_4506_, v_b_4507_);
    return v___x_4509_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1___boxed(
    mut v_00_u03b3_4510_: *mut crate::leanh::LeanObject,
    mut v_upperBound_4511_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_4512_: *mut crate::leanh::LeanObject,
    mut v_x_4513_: *mut crate::leanh::LeanObject,
    mut v_f_4514_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4515_: *mut crate::leanh::LeanObject,
    mut v_y_4516_: *mut crate::leanh::LeanObject,
    mut v_g_4517_: *mut crate::leanh::LeanObject,
    mut v_inst_4518_: *mut crate::leanh::LeanObject,
    mut v_R_4519_: *mut crate::leanh::LeanObject,
    mut v_a_4520_: *mut crate::leanh::LeanObject,
    mut v_b_4521_: *mut crate::leanh::LeanObject,
    mut v_c_4522_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4523_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1(
            v_00_u03b3_4510_,
            v_upperBound_4511_,
            v_00_u03b1_4512_,
            v_x_4513_,
            v_f_4514_,
            v_00_u03b2_4515_,
            v_y_4516_,
            v_g_4517_,
            v_inst_4518_,
            v_R_4519_,
            v_a_4520_,
            v_b_4521_,
            v_c_4522_,
        );
    crate::leanh::lean_dec_ref(v_y_4516_);
    crate::leanh::lean_dec_ref(v_x_4513_);
    crate::leanh::lean_dec(v_upperBound_4511_);
    return v_res_4523_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_989218885____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4531_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__1_00___x40_Lean_Meta_Tactic_LibrarySearch_989218885____hygCtx___hyg_2_;
    v___x_4532_ = l_Lean_registerInternalExceptionId(v___x_4531_);
    return v___x_4532_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_989218885____hygCtx___hyg_2____boxed(
    mut v_a_4533_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4534_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_989218885____hygCtx___hyg_2_();
    return v_res_4534_;
}
pub unsafe fn _init_l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4535_ = crate::leanh::lean_box(0);
    v___x_4536_ =
        l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_abortSpeculationId;
    v___x_4537_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4537_, 0, v___x_4536_);
    crate::leanh::lean_ctor_set(v___x_4537_, 1, v___x_4535_);
    return v___x_4537_;
}
pub unsafe fn l_Lean_Meta_LibrarySearch_abortSpeculation___redArg(
    mut v_inst_4538_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_throw_4539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_throw_4539_ = crate::leanh::lean_ctor_get(v_inst_4538_, 0);
    crate::leanh::lean_inc(v_throw_4539_);
    crate::leanh::lean_dec_ref(v_inst_4538_);
    v___x_4540_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0_once
        ),
        _init_l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0,
    );
    v___x_4541_ = crate::leanh::lean_apply_2(v_throw_4539_, crate::leanh::lean_box(0), v___x_4540_);
    return v___x_4541_;
}
pub unsafe fn l_Lean_Meta_LibrarySearch_abortSpeculation(
    mut v_m_4542_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_4543_: *mut crate::leanh::LeanObject,
    mut v_inst_4544_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4545_ = l_Lean_Meta_LibrarySearch_abortSpeculation___redArg(v_inst_4544_);
    return v___x_4545_;
}
pub unsafe fn l_Lean_Meta_LibrarySearch_isAbortSpeculation(
    mut v_x_4546_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_4546_) == 1 {
        let mut v_id_4547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4549_: u8 = 0;
        v_id_4547_ = crate::leanh::lean_ctor_get(v_x_4546_, 0);
        v___x_4548_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_abortSpeculationId;
        v___x_4549_ = l_Lean_instBEqInternalExceptionId_beq(v_id_4547_, v___x_4548_);
        return v___x_4549_;
    } else {
        let mut v___x_4550_: u8 = 0;
        v___x_4550_ = 0;
        return v___x_4550_;
    }
}
pub unsafe fn l_Lean_Meta_LibrarySearch_isAbortSpeculation___boxed(
    mut v_x_4551_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4552_: u8 = 0;
    let mut v_r_4553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4552_ = l_Lean_Meta_LibrarySearch_isAbortSpeculation(v_x_4551_);
    crate::leanh::lean_dec_ref(v_x_4551_);
    v_r_4553_ = crate::leanh::lean_box((v_res_4552_) as usize);
    return v_r_4553_;
}
pub unsafe fn l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0___redArg(
    mut v_x_4554_: *mut crate::leanh::LeanObject,
    mut v___y_4555_: *mut crate::leanh::LeanObject,
    mut v___y_4556_: *mut crate::leanh::LeanObject,
    mut v___y_4557_: *mut crate::leanh::LeanObject,
    mut v___y_4558_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4566_: u8 = 0;
    let mut v___x_4567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4571_: u8 = 0;
    let mut v_a_4572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4575_: u8 = 0;
    let mut v___y_4577_: u8 = 0;
    let mut v___x_4578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4581_: u8 = 0;
    let mut v___x_4582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4586_: u8 = 0;
    let mut v_unused_4587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4591_: u8 = 0;
    let mut v___x_4593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4595_: u8 = 0;
    let mut v___x_4597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4599_: u8 = 0;
    let mut v___x_4600_: u8 = 0;
    let mut v_isSharedCheck_4601_: u8 = 0;
    let mut v_a_4602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4605_: u8 = 0;
    let mut v___x_4607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4609_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4560_ = l_Lean_Meta_saveState___redArg(v___y_4556_, v___y_4558_);
                if crate::leanh::lean_obj_tag(v___x_4560_) == 0 {
                    v_a_4561_ = crate::leanh::lean_ctor_get(v___x_4560_, 0);
                    crate::leanh::lean_inc(v_a_4561_);
                    crate::leanh::lean_dec_ref_known(v___x_4560_, 1);
                    crate::leanh::lean_inc(v___y_4558_);
                    crate::leanh::lean_inc_ref(v___y_4557_);
                    crate::leanh::lean_inc(v___y_4556_);
                    crate::leanh::lean_inc_ref(v___y_4555_);
                    v___x_4562_ = crate::leanh::lean_apply_5(
                        v_x_4554_,
                        v___y_4555_,
                        v___y_4556_,
                        v___y_4557_,
                        v___y_4558_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_4562_) == 0 {
                        crate::leanh::lean_dec(v_a_4561_);
                        v_a_4563_ = crate::leanh::lean_ctor_get(v___x_4562_, 0);
                        v_isSharedCheck_4571_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4562_)) as u8;
                        if v_isSharedCheck_4571_ == 0 {
                            v___x_4565_ = v___x_4562_;
                            v_isShared_4566_ = v_isSharedCheck_4571_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4563_);
                            crate::leanh::lean_dec(v___x_4562_);
                            v___x_4565_ = crate::leanh::lean_box(0);
                            v_isShared_4566_ = v_isSharedCheck_4571_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4572_ = crate::leanh::lean_ctor_get(v___x_4562_, 0);
                        v_isSharedCheck_4601_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4562_)) as u8;
                        if v_isSharedCheck_4601_ == 0 {
                            v___x_4574_ = v___x_4562_;
                            v_isShared_4575_ = v_isSharedCheck_4601_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4572_);
                            crate::leanh::lean_dec(v___x_4562_);
                            v___x_4574_ = crate::leanh::lean_box(0);
                            v_isShared_4575_ = v_isSharedCheck_4601_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_x_4554_);
                    v_a_4602_ = crate::leanh::lean_ctor_get(v___x_4560_, 0);
                    v_isSharedCheck_4609_ = (!crate::leanh::lean_is_exclusive(v___x_4560_)) as u8;
                    if v_isSharedCheck_4609_ == 0 {
                        v___x_4604_ = v___x_4560_;
                        v_isShared_4605_ = v_isSharedCheck_4609_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4602_);
                        crate::leanh::lean_dec(v___x_4560_);
                        v___x_4604_ = crate::leanh::lean_box(0);
                        v_isShared_4605_ = v_isSharedCheck_4609_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4567_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4567_, 0, v_a_4563_);
                if v_isShared_4566_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4565_, 0, v___x_4567_);
                    v___x_4569_ = v___x_4565_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4570_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4570_, 0, v___x_4567_);
                    v___x_4569_ = v_reuseFailAlloc_4570_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4569_;
            }
            3 => {
                v___x_4599_ = l_Lean_Exception_isInterrupt(v_a_4572_);
                if v___x_4599_ == 0 {
                    crate::leanh::lean_inc(v_a_4572_);
                    v___x_4600_ = l_Lean_Exception_isRuntime(v_a_4572_);
                    v___y_4577_ = v___x_4600_;
                    state = 4;
                    continue;
                } else {
                    v___y_4577_ = v___x_4599_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v___y_4577_ == 0 {
                    crate::leanh::lean_del_object(v___x_4574_);
                    crate::leanh::lean_dec(v_a_4572_);
                    v___x_4578_ = l_Lean_Meta_SavedState_restore___redArg(
                        v_a_4561_,
                        v___y_4556_,
                        v___y_4558_,
                    );
                    crate::leanh::lean_dec(v_a_4561_);
                    if crate::leanh::lean_obj_tag(v___x_4578_) == 0 {
                        v_isSharedCheck_4586_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4578_)) as u8;
                        if v_isSharedCheck_4586_ == 0 {
                            v_unused_4587_ = crate::leanh::lean_ctor_get(v___x_4578_, 0);
                            crate::leanh::lean_dec(v_unused_4587_);
                            v___x_4580_ = v___x_4578_;
                            v_isShared_4581_ = v_isSharedCheck_4586_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_4578_);
                            v___x_4580_ = crate::leanh::lean_box(0);
                            v_isShared_4581_ = v_isSharedCheck_4586_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v_a_4588_ = crate::leanh::lean_ctor_get(v___x_4578_, 0);
                        v_isSharedCheck_4595_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4578_)) as u8;
                        if v_isSharedCheck_4595_ == 0 {
                            v___x_4590_ = v___x_4578_;
                            v_isShared_4591_ = v_isSharedCheck_4595_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4588_);
                            crate::leanh::lean_dec(v___x_4578_);
                            v___x_4590_ = crate::leanh::lean_box(0);
                            v_isShared_4591_ = v_isSharedCheck_4595_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4561_);
                    if v_isShared_4575_ == 0 {
                        v___x_4597_ = v___x_4574_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_4598_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4598_, 0, v_a_4572_);
                        v___x_4597_ = v_reuseFailAlloc_4598_;
                        state = 9;
                        continue;
                    }
                }
            }
            5 => {
                v___x_4582_ = crate::leanh::lean_box(0);
                if v_isShared_4581_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4580_, 0, v___x_4582_);
                    v___x_4584_ = v___x_4580_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4585_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4585_, 0, v___x_4582_);
                    v___x_4584_ = v_reuseFailAlloc_4585_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4584_;
            }
            7 => {
                if v_isShared_4591_ == 0 {
                    v___x_4593_ = v___x_4590_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4594_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4594_, 0, v_a_4588_);
                    v___x_4593_ = v_reuseFailAlloc_4594_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4593_;
            }
            9 => {
                return v___x_4597_;
            }
            10 => {
                if v_isShared_4605_ == 0 {
                    v___x_4607_ = v___x_4604_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4608_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4608_, 0, v_a_4602_);
                    v___x_4607_ = v_reuseFailAlloc_4608_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4607_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0___redArg___boxed(
    mut v_x_4610_: *mut crate::leanh::LeanObject,
    mut v___y_4611_: *mut crate::leanh::LeanObject,
    mut v___y_4612_: *mut crate::leanh::LeanObject,
    mut v___y_4613_: *mut crate::leanh::LeanObject,
    mut v___y_4614_: *mut crate::leanh::LeanObject,
    mut v___y_4615_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4616_ =
        l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0___redArg(
            v_x_4610_,
            v___y_4611_,
            v___y_4612_,
            v___y_4613_,
            v___y_4614_,
        );
    crate::leanh::lean_dec(v___y_4614_);
    crate::leanh::lean_dec_ref(v___y_4613_);
    crate::leanh::lean_dec(v___y_4612_);
    crate::leanh::lean_dec_ref(v___y_4611_);
    return v_res_4616_;
}
pub unsafe fn l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0(
    mut v_00_u03b1_4617_: *mut crate::leanh::LeanObject,
    mut v_x_4618_: *mut crate::leanh::LeanObject,
    mut v___y_4619_: *mut crate::leanh::LeanObject,
    mut v___y_4620_: *mut crate::leanh::LeanObject,
    mut v___y_4621_: *mut crate::leanh::LeanObject,
    mut v___y_4622_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4624_ =
        l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0___redArg(
            v_x_4618_,
            v___y_4619_,
            v___y_4620_,
            v___y_4621_,
            v___y_4622_,
        );
    return v___x_4624_;
}
pub unsafe fn l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0___boxed(
    mut v_00_u03b1_4625_: *mut crate::leanh::LeanObject,
    mut v_x_4626_: *mut crate::leanh::LeanObject,
    mut v___y_4627_: *mut crate::leanh::LeanObject,
    mut v___y_4628_: *mut crate::leanh::LeanObject,
    mut v___y_4629_: *mut crate::leanh::LeanObject,
    mut v___y_4630_: *mut crate::leanh::LeanObject,
    mut v___y_4631_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4632_ = l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0(
        v_00_u03b1_4625_,
        v_x_4626_,
        v___y_4627_,
        v___y_4628_,
        v___y_4629_,
        v___y_4630_,
    );
    crate::leanh::lean_dec(v___y_4630_);
    crate::leanh::lean_dec_ref(v___y_4629_);
    crate::leanh::lean_dec(v___y_4628_);
    crate::leanh::lean_dec_ref(v___y_4627_);
    return v_res_4632_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1___redArg(
    mut v_e_4633_: *mut crate::leanh::LeanObject,
    mut v___y_4634_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4636_: u8 = 0;
    let mut v___x_4637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_4644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_4646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4650_: u8 = 0;
    let mut v___x_4652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4656_: u8 = 0;
    let mut v_unused_4657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4636_ = l_Lean_Expr_hasMVar(v_e_4633_);
                if v___x_4636_ == 0 {
                    v___x_4637_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4637_, 0, v_e_4633_);
                    return v___x_4637_;
                } else {
                    v___x_4638_ = lean_st_ref_get(v___y_4634_);
                    v_mctx_4639_ = crate::leanh::lean_ctor_get(v___x_4638_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_4639_);
                    crate::leanh::lean_dec(v___x_4638_);
                    v___x_4640_ = l_Lean_instantiateMVarsCore(v_mctx_4639_, v_e_4633_);
                    v_fst_4641_ = crate::leanh::lean_ctor_get(v___x_4640_, 0);
                    crate::leanh::lean_inc(v_fst_4641_);
                    v_snd_4642_ = crate::leanh::lean_ctor_get(v___x_4640_, 1);
                    crate::leanh::lean_inc(v_snd_4642_);
                    crate::leanh::lean_dec_ref(v___x_4640_);
                    v___x_4643_ = lean_st_ref_take(v___y_4634_);
                    v_cache_4644_ = crate::leanh::lean_ctor_get(v___x_4643_, 1);
                    v_zetaDeltaFVarIds_4645_ = crate::leanh::lean_ctor_get(v___x_4643_, 2);
                    v_postponed_4646_ = crate::leanh::lean_ctor_get(v___x_4643_, 3);
                    v_diag_4647_ = crate::leanh::lean_ctor_get(v___x_4643_, 4);
                    v_isSharedCheck_4656_ = (!crate::leanh::lean_is_exclusive(v___x_4643_)) as u8;
                    if v_isSharedCheck_4656_ == 0 {
                        v_unused_4657_ = crate::leanh::lean_ctor_get(v___x_4643_, 0);
                        crate::leanh::lean_dec(v_unused_4657_);
                        v___x_4649_ = v___x_4643_;
                        v_isShared_4650_ = v_isSharedCheck_4656_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_4647_);
                        crate::leanh::lean_inc(v_postponed_4646_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_4645_);
                        crate::leanh::lean_inc(v_cache_4644_);
                        crate::leanh::lean_dec(v___x_4643_);
                        v___x_4649_ = crate::leanh::lean_box(0);
                        v_isShared_4650_ = v_isSharedCheck_4656_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4650_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4649_, 0, v_snd_4642_);
                    v___x_4652_ = v___x_4649_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4655_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4655_, 0, v_snd_4642_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4655_, 1, v_cache_4644_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4655_,
                        2,
                        v_zetaDeltaFVarIds_4645_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4655_, 3, v_postponed_4646_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4655_, 4, v_diag_4647_);
                    v___x_4652_ = v_reuseFailAlloc_4655_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4653_ = lean_st_ref_set(v___y_4634_, v___x_4652_);
                v___x_4654_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4654_, 0, v_fst_4641_);
                return v___x_4654_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1___redArg___boxed(
    mut v_e_4658_: *mut crate::leanh::LeanObject,
    mut v___y_4659_: *mut crate::leanh::LeanObject,
    mut v___y_4660_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4661_ =
        l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1___redArg(
            v_e_4658_,
            v___y_4659_,
        );
    crate::leanh::lean_dec(v___y_4659_);
    return v_res_4661_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1(
    mut v_e_4662_: *mut crate::leanh::LeanObject,
    mut v___y_4663_: *mut crate::leanh::LeanObject,
    mut v___y_4664_: *mut crate::leanh::LeanObject,
    mut v___y_4665_: *mut crate::leanh::LeanObject,
    mut v___y_4666_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4668_ =
        l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1___redArg(
            v_e_4662_,
            v___y_4664_,
        );
    return v___x_4668_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1___boxed(
    mut v_e_4669_: *mut crate::leanh::LeanObject,
    mut v___y_4670_: *mut crate::leanh::LeanObject,
    mut v___y_4671_: *mut crate::leanh::LeanObject,
    mut v___y_4672_: *mut crate::leanh::LeanObject,
    mut v___y_4673_: *mut crate::leanh::LeanObject,
    mut v___y_4674_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4675_ =
        l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1(
            v_e_4669_,
            v___y_4670_,
            v___y_4671_,
            v___y_4672_,
            v___y_4673_,
        );
    crate::leanh::lean_dec(v___y_4673_);
    crate::leanh::lean_dec_ref(v___y_4672_);
    crate::leanh::lean_dec(v___y_4671_);
    crate::leanh::lean_dec_ref(v___y_4670_);
    return v_res_4675_;
}
pub unsafe fn l_Lean_Meta_LibrarySearch_librarySearchSymm___lam__0(
    mut v___x_4676_: *mut crate::leanh::LeanObject,
    mut v_x_4677_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4678_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4678_, 0, v___x_4676_);
    crate::leanh::lean_ctor_set(v___x_4678_, 1, v_x_4677_);
    return v___x_4678_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__2(
    mut v___x_4679_: *mut crate::leanh::LeanObject,
    mut v_sz_4680_: usize,
    mut v_i_4681_: usize,
    mut v_bs_4682_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4683_: u8 = 0;
    let mut v_v_4684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4688_: usize = 0;
    let mut v___x_4689_: usize = 0;
    let mut v___x_4690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4683_ = lean_usize_dec_lt(v_i_4681_, v_sz_4680_);
                if v___x_4683_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_4679_);
                    return v_bs_4682_;
                } else {
                    v_v_4684_ = lean_array_uget(v_bs_4682_, v_i_4681_);
                    v___x_4685_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_4686_ = lean_array_uset(v_bs_4682_, v_i_4681_, v___x_4685_);
                    crate::leanh::lean_inc_ref(v___x_4679_);
                    v___x_4687_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4687_, 0, v___x_4679_);
                    crate::leanh::lean_ctor_set(v___x_4687_, 1, v_v_4684_);
                    v___x_4688_ = 1usize;
                    v___x_4689_ = lean_usize_add(v_i_4681_, v___x_4688_);
                    v___x_4690_ = lean_array_uset(v_bs_x27_4686_, v_i_4681_, v___x_4687_);
                    v_i_4681_ = v___x_4689_;
                    v_bs_4682_ = v___x_4690_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__2___boxed(
    mut v___x_4692_: *mut crate::leanh::LeanObject,
    mut v_sz_4693_: *mut crate::leanh::LeanObject,
    mut v_i_4694_: *mut crate::leanh::LeanObject,
    mut v_bs_4695_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4696_: usize = 0;
    let mut v_i_boxed_4697_: usize = 0;
    let mut v_res_4698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4696_ = crate::leanh::lean_unbox_usize(v_sz_4693_);
    crate::leanh::lean_dec(v_sz_4693_);
    v_i_boxed_4697_ = crate::leanh::lean_unbox_usize(v_i_4694_);
    crate::leanh::lean_dec(v_i_4694_);
    v_res_4698_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__2(v___x_4692_, v_sz_boxed_4696_, v_i_boxed_4697_, v_bs_4695_);
    return v_res_4698_;
}
pub unsafe fn l_Lean_Meta_LibrarySearch_librarySearchSymm(
    mut v_searchFn_4699_: *mut crate::leanh::LeanObject,
    mut v_goal_4700_: *mut crate::leanh::LeanObject,
    mut v_a_4701_: *mut crate::leanh::LeanObject,
    mut v_a_4702_: *mut crate::leanh::LeanObject,
    mut v_a_4703_: *mut crate::leanh::LeanObject,
    mut v_a_4704_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4718_: u8 = 0;
    let mut v_val_4719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4728_: u8 = 0;
    let mut v___x_4729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_4731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_4733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4737_: u8 = 0;
    let mut v___x_4739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4750_: u8 = 0;
    let mut v_unused_4751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4752_: u8 = 0;
    let mut v_a_4753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4756_: u8 = 0;
    let mut v___x_4758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4760_: u8 = 0;
    let mut v_a_4761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4764_: u8 = 0;
    let mut v___x_4766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4768_: u8 = 0;
    let mut v_sz_4769_: usize = 0;
    let mut v___x_4770_: usize = 0;
    let mut v___x_4771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4775_: u8 = 0;
    let mut v_a_4776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4779_: u8 = 0;
    let mut v___x_4781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4783_: u8 = 0;
    let mut v_a_4784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4787_: u8 = 0;
    let mut v___x_4789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4791_: u8 = 0;
    let mut v_a_4792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4795_: u8 = 0;
    let mut v___x_4797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4799_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_goal_4700_);
                v___x_4706_ =
                    l_Lean_MVarId_getType(v_goal_4700_, v_a_4701_, v_a_4702_, v_a_4703_, v_a_4704_);
                if crate::leanh::lean_obj_tag(v___x_4706_) == 0 {
                    v_a_4707_ = crate::leanh::lean_ctor_get(v___x_4706_, 0);
                    crate::leanh::lean_inc(v_a_4707_);
                    crate::leanh::lean_dec_ref_known(v___x_4706_, 1);
                    crate::leanh::lean_inc_ref(v_searchFn_4699_);
                    crate::leanh::lean_inc(v_a_4704_);
                    crate::leanh::lean_inc_ref(v_a_4703_);
                    crate::leanh::lean_inc(v_a_4702_);
                    crate::leanh::lean_inc_ref(v_a_4701_);
                    v___x_4708_ = crate::leanh::lean_apply_6(
                        v_searchFn_4699_,
                        v_a_4707_,
                        v_a_4701_,
                        v_a_4702_,
                        v_a_4703_,
                        v_a_4704_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_4708_) == 0 {
                        v_a_4709_ = crate::leanh::lean_ctor_get(v___x_4708_, 0);
                        crate::leanh::lean_inc(v_a_4709_);
                        crate::leanh::lean_dec_ref_known(v___x_4708_, 1);
                        v___x_4710_ = lean_st_ref_get(v_a_4702_);
                        v_mctx_4711_ = crate::leanh::lean_ctor_get(v___x_4710_, 0);
                        crate::leanh::lean_inc_ref_n(v_mctx_4711_, 2);
                        crate::leanh::lean_dec(v___x_4710_);
                        crate::leanh::lean_inc(v_goal_4700_);
                        v___x_4712_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4712_, 0, v_goal_4700_);
                        crate::leanh::lean_ctor_set(v___x_4712_, 1, v_mctx_4711_);
                        v___x_4713_ = crate::leanh::lean_alloc_closure(
                            l_Lean_MVarId_applySymm___boxed as *mut core::ffi::c_void,
                            6,
                            1,
                        );
                        crate::leanh::lean_closure_set(v___x_4713_, 0, v_goal_4700_);
                        v___x_4714_ = l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0___redArg(v___x_4713_, v_a_4701_, v_a_4702_, v_a_4703_, v_a_4704_);
                        if crate::leanh::lean_obj_tag(v___x_4714_) == 0 {
                            v_a_4715_ = crate::leanh::lean_ctor_get(v___x_4714_, 0);
                            v_isSharedCheck_4775_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4714_)) as u8;
                            if v_isSharedCheck_4775_ == 0 {
                                v___x_4717_ = v___x_4714_;
                                v_isShared_4718_ = v_isSharedCheck_4775_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4715_);
                                crate::leanh::lean_dec(v___x_4714_);
                                v___x_4717_ = crate::leanh::lean_box(0);
                                v_isShared_4718_ = v_isSharedCheck_4775_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v___x_4712_, 2);
                            crate::leanh::lean_dec_ref(v_mctx_4711_);
                            crate::leanh::lean_dec(v_a_4709_);
                            crate::leanh::lean_dec_ref(v_searchFn_4699_);
                            v_a_4776_ = crate::leanh::lean_ctor_get(v___x_4714_, 0);
                            v_isSharedCheck_4783_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4714_)) as u8;
                            if v_isSharedCheck_4783_ == 0 {
                                v___x_4778_ = v___x_4714_;
                                v_isShared_4779_ = v_isSharedCheck_4783_;
                                state = 11;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4776_);
                                crate::leanh::lean_dec(v___x_4714_);
                                v___x_4778_ = crate::leanh::lean_box(0);
                                v_isShared_4779_ = v_isSharedCheck_4783_;
                                state = 11;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_goal_4700_);
                        crate::leanh::lean_dec_ref(v_searchFn_4699_);
                        v_a_4784_ = crate::leanh::lean_ctor_get(v___x_4708_, 0);
                        v_isSharedCheck_4791_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4708_)) as u8;
                        if v_isSharedCheck_4791_ == 0 {
                            v___x_4786_ = v___x_4708_;
                            v_isShared_4787_ = v_isSharedCheck_4791_;
                            state = 13;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4784_);
                            crate::leanh::lean_dec(v___x_4708_);
                            v___x_4786_ = crate::leanh::lean_box(0);
                            v_isShared_4787_ = v_isSharedCheck_4791_;
                            state = 13;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_goal_4700_);
                    crate::leanh::lean_dec_ref(v_searchFn_4699_);
                    v_a_4792_ = crate::leanh::lean_ctor_get(v___x_4706_, 0);
                    v_isSharedCheck_4799_ = (!crate::leanh::lean_is_exclusive(v___x_4706_)) as u8;
                    if v_isSharedCheck_4799_ == 0 {
                        v___x_4794_ = v___x_4706_;
                        v_isShared_4795_ = v_isSharedCheck_4799_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4792_);
                        crate::leanh::lean_dec(v___x_4706_);
                        v___x_4794_ = crate::leanh::lean_box(0);
                        v_isShared_4795_ = v_isSharedCheck_4799_;
                        state = 15;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_4715_) == 1 {
                    crate::leanh::lean_del_object(v___x_4717_);
                    v_val_4719_ = crate::leanh::lean_ctor_get(v_a_4715_, 0);
                    crate::leanh::lean_inc_n(v_val_4719_, 2);
                    crate::leanh::lean_dec_ref_known(v_a_4715_, 1);
                    v___x_4720_ = l_Lean_MVarId_getType(
                        v_val_4719_,
                        v_a_4701_,
                        v_a_4702_,
                        v_a_4703_,
                        v_a_4704_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4720_) == 0 {
                        v_a_4721_ = crate::leanh::lean_ctor_get(v___x_4720_, 0);
                        crate::leanh::lean_inc(v_a_4721_);
                        crate::leanh::lean_dec_ref_known(v___x_4720_, 1);
                        v___x_4722_ = l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1___redArg(v_a_4721_, v_a_4702_);
                        v_a_4723_ = crate::leanh::lean_ctor_get(v___x_4722_, 0);
                        crate::leanh::lean_inc(v_a_4723_);
                        crate::leanh::lean_dec_ref(v___x_4722_);
                        crate::leanh::lean_inc(v_a_4704_);
                        crate::leanh::lean_inc_ref(v_a_4703_);
                        crate::leanh::lean_inc(v_a_4702_);
                        crate::leanh::lean_inc_ref(v_a_4701_);
                        v___x_4724_ = crate::leanh::lean_apply_6(
                            v_searchFn_4699_,
                            v_a_4723_,
                            v_a_4701_,
                            v_a_4702_,
                            v_a_4703_,
                            v_a_4704_,
                            crate::leanh::lean_box(0),
                        );
                        if crate::leanh::lean_obj_tag(v___x_4724_) == 0 {
                            v_a_4725_ = crate::leanh::lean_ctor_get(v___x_4724_, 0);
                            v_isSharedCheck_4752_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4724_)) as u8;
                            if v_isSharedCheck_4752_ == 0 {
                                v___x_4727_ = v___x_4724_;
                                v_isShared_4728_ = v_isSharedCheck_4752_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4725_);
                                crate::leanh::lean_dec(v___x_4724_);
                                v___x_4727_ = crate::leanh::lean_box(0);
                                v_isShared_4728_ = v_isSharedCheck_4752_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_val_4719_);
                            crate::leanh::lean_dec_ref_known(v___x_4712_, 2);
                            crate::leanh::lean_dec_ref(v_mctx_4711_);
                            crate::leanh::lean_dec(v_a_4709_);
                            v_a_4753_ = crate::leanh::lean_ctor_get(v___x_4724_, 0);
                            v_isSharedCheck_4760_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4724_)) as u8;
                            if v_isSharedCheck_4760_ == 0 {
                                v___x_4755_ = v___x_4724_;
                                v_isShared_4756_ = v_isSharedCheck_4760_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4753_);
                                crate::leanh::lean_dec(v___x_4724_);
                                v___x_4755_ = crate::leanh::lean_box(0);
                                v_isShared_4756_ = v_isSharedCheck_4760_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_4719_);
                        crate::leanh::lean_dec_ref_known(v___x_4712_, 2);
                        crate::leanh::lean_dec_ref(v_mctx_4711_);
                        crate::leanh::lean_dec(v_a_4709_);
                        crate::leanh::lean_dec_ref(v_searchFn_4699_);
                        v_a_4761_ = crate::leanh::lean_ctor_get(v___x_4720_, 0);
                        v_isSharedCheck_4768_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4720_)) as u8;
                        if v_isSharedCheck_4768_ == 0 {
                            v___x_4763_ = v___x_4720_;
                            v_isShared_4764_ = v_isSharedCheck_4768_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4761_);
                            crate::leanh::lean_dec(v___x_4720_);
                            v___x_4763_ = crate::leanh::lean_box(0);
                            v_isShared_4764_ = v_isSharedCheck_4768_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4715_);
                    crate::leanh::lean_dec_ref(v_mctx_4711_);
                    crate::leanh::lean_dec_ref(v_searchFn_4699_);
                    v_sz_4769_ = lean_array_size(v_a_4709_);
                    v___x_4770_ = 0usize;
                    v___x_4771_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__2(v___x_4712_, v_sz_4769_, v___x_4770_, v_a_4709_);
                    if v_isShared_4718_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4717_, 0, v___x_4771_);
                        v___x_4773_ = v___x_4717_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_4774_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4774_, 0, v___x_4771_);
                        v___x_4773_ = v_reuseFailAlloc_4774_;
                        state = 10;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4729_ = lean_st_ref_get(v_a_4702_);
                v___x_4730_ = lean_st_ref_take(v_a_4702_);
                v_cache_4731_ = crate::leanh::lean_ctor_get(v___x_4730_, 1);
                v_zetaDeltaFVarIds_4732_ = crate::leanh::lean_ctor_get(v___x_4730_, 2);
                v_postponed_4733_ = crate::leanh::lean_ctor_get(v___x_4730_, 3);
                v_diag_4734_ = crate::leanh::lean_ctor_get(v___x_4730_, 4);
                v_isSharedCheck_4750_ = (!crate::leanh::lean_is_exclusive(v___x_4730_)) as u8;
                if v_isSharedCheck_4750_ == 0 {
                    v_unused_4751_ = crate::leanh::lean_ctor_get(v___x_4730_, 0);
                    crate::leanh::lean_dec(v_unused_4751_);
                    v___x_4736_ = v___x_4730_;
                    v_isShared_4737_ = v_isSharedCheck_4750_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_4734_);
                    crate::leanh::lean_inc(v_postponed_4733_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_4732_);
                    crate::leanh::lean_inc(v_cache_4731_);
                    crate::leanh::lean_dec(v___x_4730_);
                    v___x_4736_ = crate::leanh::lean_box(0);
                    v_isShared_4737_ = v_isSharedCheck_4750_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4737_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4736_, 0, v_mctx_4711_);
                    v___x_4739_ = v___x_4736_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4749_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4749_, 0, v_mctx_4711_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4749_, 1, v_cache_4731_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4749_,
                        2,
                        v_zetaDeltaFVarIds_4732_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4749_, 3, v_postponed_4733_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4749_, 4, v_diag_4734_);
                    v___x_4739_ = v_reuseFailAlloc_4749_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4740_ = lean_st_ref_set(v_a_4702_, v___x_4739_);
                v_mctx_4741_ = crate::leanh::lean_ctor_get(v___x_4729_, 0);
                crate::leanh::lean_inc_ref(v_mctx_4741_);
                crate::leanh::lean_dec(v___x_4729_);
                v___f_4742_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Meta_LibrarySearch_librarySearchSymm___lam__0 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4742_, 0, v___x_4712_);
                v___x_4743_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4743_, 0, v_val_4719_);
                crate::leanh::lean_ctor_set(v___x_4743_, 1, v_mctx_4741_);
                v___f_4744_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Meta_LibrarySearch_librarySearchSymm___lam__0 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4744_, 0, v___x_4743_);
                v___x_4745_ = l_Lean_Meta_LibrarySearch_interleaveWith___redArg(
                    v___f_4742_,
                    v_a_4709_,
                    v___f_4744_,
                    v_a_4725_,
                );
                crate::leanh::lean_dec(v_a_4725_);
                crate::leanh::lean_dec(v_a_4709_);
                if v_isShared_4728_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4727_, 0, v___x_4745_);
                    v___x_4747_ = v___x_4727_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4748_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4748_, 0, v___x_4745_);
                    v___x_4747_ = v_reuseFailAlloc_4748_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4747_;
            }
            6 => {
                if v_isShared_4756_ == 0 {
                    v___x_4758_ = v___x_4755_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4759_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4759_, 0, v_a_4753_);
                    v___x_4758_ = v_reuseFailAlloc_4759_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4758_;
            }
            8 => {
                if v_isShared_4764_ == 0 {
                    v___x_4766_ = v___x_4763_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4767_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4767_, 0, v_a_4761_);
                    v___x_4766_ = v_reuseFailAlloc_4767_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4766_;
            }
            10 => {
                return v___x_4773_;
            }
            11 => {
                if v_isShared_4779_ == 0 {
                    v___x_4781_ = v___x_4778_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4782_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4782_, 0, v_a_4776_);
                    v___x_4781_ = v_reuseFailAlloc_4782_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4781_;
            }
            13 => {
                if v_isShared_4787_ == 0 {
                    v___x_4789_ = v___x_4786_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4790_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4790_, 0, v_a_4784_);
                    v___x_4789_ = v_reuseFailAlloc_4790_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4789_;
            }
            15 => {
                if v_isShared_4795_ == 0 {
                    v___x_4797_ = v___x_4794_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4798_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4798_, 0, v_a_4792_);
                    v___x_4797_ = v_reuseFailAlloc_4798_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_4797_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_LibrarySearch_librarySearchSymm___boxed(
    mut v_searchFn_4800_: *mut crate::leanh::LeanObject,
    mut v_goal_4801_: *mut crate::leanh::LeanObject,
    mut v_a_4802_: *mut crate::leanh::LeanObject,
    mut v_a_4803_: *mut crate::leanh::LeanObject,
    mut v_a_4804_: *mut crate::leanh::LeanObject,
    mut v_a_4805_: *mut crate::leanh::LeanObject,
    mut v_a_4806_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4807_ = l_Lean_Meta_LibrarySearch_librarySearchSymm(
        v_searchFn_4800_,
        v_goal_4801_,
        v_a_4802_,
        v_a_4803_,
        v_a_4804_,
        v_a_4805_,
    );
    crate::leanh::lean_dec(v_a_4805_);
    crate::leanh::lean_dec_ref(v_a_4804_);
    crate::leanh::lean_dec(v_a_4803_);
    crate::leanh::lean_dec_ref(v_a_4802_);
    return v_res_4807_;
}
pub unsafe fn l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__0(
    mut v_e_4812_: *mut crate::leanh::LeanObject,
    mut v___y_4813_: *mut crate::leanh::LeanObject,
    mut v___y_4814_: *mut crate::leanh::LeanObject,
    mut v___y_4815_: *mut crate::leanh::LeanObject,
    mut v___y_4816_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4818_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__0___closed__1;
    v___x_4819_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_4820_ = lean_mk_empty_array_with_capacity(v___x_4819_);
    v___x_4821_ = lean_array_push(v___x_4820_, v_e_4812_);
    v___x_4822_ = l_Lean_Meta_mkAppM(
        v___x_4818_,
        v___x_4821_,
        v___y_4813_,
        v___y_4814_,
        v___y_4815_,
        v___y_4816_,
    );
    return v___x_4822_;
}
pub unsafe fn l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__0___boxed(
    mut v_e_4823_: *mut crate::leanh::LeanObject,
    mut v___y_4824_: *mut crate::leanh::LeanObject,
    mut v___y_4825_: *mut crate::leanh::LeanObject,
    mut v___y_4826_: *mut crate::leanh::LeanObject,
    mut v___y_4827_: *mut crate::leanh::LeanObject,
    mut v___y_4828_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4829_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__0(
        v_e_4823_,
        v___y_4824_,
        v___y_4825_,
        v___y_4826_,
        v___y_4827_,
    );
    crate::leanh::lean_dec(v___y_4827_);
    crate::leanh::lean_dec_ref(v___y_4826_);
    crate::leanh::lean_dec(v___y_4825_);
    crate::leanh::lean_dec_ref(v___y_4824_);
    return v_res_4829_;
}
pub unsafe fn l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__1(
    mut v_e_4834_: *mut crate::leanh::LeanObject,
    mut v___y_4835_: *mut crate::leanh::LeanObject,
    mut v___y_4836_: *mut crate::leanh::LeanObject,
    mut v___y_4837_: *mut crate::leanh::LeanObject,
    mut v___y_4838_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4840_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__1___closed__1;
    v___x_4841_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_4842_ = lean_mk_empty_array_with_capacity(v___x_4841_);
    v___x_4843_ = lean_array_push(v___x_4842_, v_e_4834_);
    v___x_4844_ = l_Lean_Meta_mkAppM(
        v___x_4840_,
        v___x_4843_,
        v___y_4835_,
        v___y_4836_,
        v___y_4837_,
        v___y_4838_,
    );
    return v___x_4844_;
}
pub unsafe fn l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__1___boxed(
    mut v_e_4845_: *mut crate::leanh::LeanObject,
    mut v___y_4846_: *mut crate::leanh::LeanObject,
    mut v___y_4847_: *mut crate::leanh::LeanObject,
    mut v___y_4848_: *mut crate::leanh::LeanObject,
    mut v___y_4849_: *mut crate::leanh::LeanObject,
    mut v___y_4850_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4851_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__1(
        v_e_4845_,
        v___y_4846_,
        v___y_4847_,
        v___y_4848_,
        v___y_4849_,
    );
    crate::leanh::lean_dec(v___y_4849_);
    crate::leanh::lean_dec_ref(v___y_4848_);
    crate::leanh::lean_dec(v___y_4847_);
    crate::leanh::lean_dec_ref(v___y_4846_);
    return v_res_4851_;
}
pub unsafe fn l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma(
    mut v_lem_4854_: *mut crate::leanh::LeanObject,
    mut v_mod_4855_: u8,
    mut v_a_4856_: *mut crate::leanh::LeanObject,
    mut v_a_4857_: *mut crate::leanh::LeanObject,
    mut v_a_4858_: *mut crate::leanh::LeanObject,
    mut v_a_4859_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4861_ = l_Lean_Meta_mkConstWithFreshMVarLevels(
        v_lem_4854_,
        v_a_4856_,
        v_a_4857_,
        v_a_4858_,
        v_a_4859_,
    );
    if crate::leanh::lean_obj_tag(v___x_4861_) == 0 {
        match v_mod_4855_ {
            0 => {
                return v___x_4861_;
            }
            1 => {
                let mut v_a_4862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___f_4863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_a_4862_ = crate::leanh::lean_ctor_get(v___x_4861_, 0);
                crate::leanh::lean_inc(v_a_4862_);
                crate::leanh::lean_dec_ref_known(v___x_4861_, 1);
                v___f_4863_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___closed__0;
                v___x_4864_ = l_Lean_Meta_mapForallTelescope(
                    v___f_4863_,
                    v_a_4862_,
                    v_a_4856_,
                    v_a_4857_,
                    v_a_4858_,
                    v_a_4859_,
                );
                return v___x_4864_;
            }
            _ => {
                let mut v_a_4865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___f_4866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_a_4865_ = crate::leanh::lean_ctor_get(v___x_4861_, 0);
                crate::leanh::lean_inc(v_a_4865_);
                crate::leanh::lean_dec_ref_known(v___x_4861_, 1);
                v___f_4866_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___closed__1;
                v___x_4867_ = l_Lean_Meta_mapForallTelescope(
                    v___f_4866_,
                    v_a_4865_,
                    v_a_4856_,
                    v_a_4857_,
                    v_a_4858_,
                    v_a_4859_,
                );
                return v___x_4867_;
            }
        }
    } else {
        return v___x_4861_;
    }
}
pub unsafe fn l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___boxed(
    mut v_lem_4868_: *mut crate::leanh::LeanObject,
    mut v_mod_4869_: *mut crate::leanh::LeanObject,
    mut v_a_4870_: *mut crate::leanh::LeanObject,
    mut v_a_4871_: *mut crate::leanh::LeanObject,
    mut v_a_4872_: *mut crate::leanh::LeanObject,
    mut v_a_4873_: *mut crate::leanh::LeanObject,
    mut v_a_4874_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_mod_boxed_4875_: u8 = 0;
    let mut v_res_4876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_mod_boxed_4875_ = (crate::leanh::lean_unbox(v_mod_4869_) as u8);
    v_res_4876_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma(
        v_lem_4868_,
        v_mod_boxed_4875_,
        v_a_4870_,
        v_a_4871_,
        v_a_4872_,
        v_a_4873_,
    );
    crate::leanh::lean_dec(v_a_4873_);
    crate::leanh::lean_dec_ref(v_a_4872_);
    crate::leanh::lean_dec(v_a_4871_);
    crate::leanh::lean_dec_ref(v_a_4870_);
    return v_res_4876_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_isVar(
    mut v_e_4877_: *mut crate::leanh::LeanObject,
) -> u8 {
    match crate::leanh::lean_obj_tag(v_e_4877_) {
        0 => {
            let mut v___x_4878_: u8 = 0;
            v___x_4878_ = 1;
            return v___x_4878_;
        }
        1 => {
            let mut v___x_4879_: u8 = 0;
            v___x_4879_ = 1;
            return v___x_4879_;
        }
        2 => {
            let mut v___x_4880_: u8 = 0;
            v___x_4880_ = 1;
            return v___x_4880_;
        }
        _ => {
            let mut v___x_4881_: u8 = 0;
            v___x_4881_ = 0;
            return v___x_4881_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_isVar___boxed(
    mut v_e_4882_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4883_: u8 = 0;
    let mut v_r_4884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4883_ =
        l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_isVar(v_e_4882_);
    crate::leanh::lean_dec_ref(v_e_4882_);
    v_r_4884_ = crate::leanh::lean_box((v_res_4883_) as usize);
    return v_r_4884_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4885_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_4886_ = lean_mk_empty_array_with_capacity(v___x_4885_);
    v___x_4887_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4887_, 0, v___x_4886_);
    return v___x_4887_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4888_: usize = 0;
    let mut v___x_4889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4888_ = 5usize;
    v___x_4889_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4890_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_4891_ = lean_mk_empty_array_with_capacity(v___x_4890_);
    v___x_4892_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__0_once), _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__0);
    v___x_4893_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_4893_, 0, v___x_4892_);
    crate::leanh::lean_ctor_set(v___x_4893_, 1, v___x_4891_);
    crate::leanh::lean_ctor_set(v___x_4893_, 2, v___x_4889_);
    crate::leanh::lean_ctor_set(v___x_4893_, 3, v___x_4889_);
    crate::leanh::lean_ctor_set_usize(v___x_4893_, 4, v___x_4888_);
    return v___x_4893_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg(
    mut v___y_4894_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traces_4898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_4905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4911_: u8 = 0;
    let mut v_tid_4912_: u64 = 0;
    let mut v___x_4914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4915_: u8 = 0;
    let mut v___x_4916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4925_: u8 = 0;
    let mut v_unused_4926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4927_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4896_ = lean_st_ref_get(v___y_4894_);
                v_traceState_4897_ = crate::leanh::lean_ctor_get(v___x_4896_, 4);
                crate::leanh::lean_inc_ref(v_traceState_4897_);
                crate::leanh::lean_dec(v___x_4896_);
                v_traces_4898_ = crate::leanh::lean_ctor_get(v_traceState_4897_, 0);
                crate::leanh::lean_inc_ref(v_traces_4898_);
                crate::leanh::lean_dec_ref(v_traceState_4897_);
                v___x_4899_ = lean_st_ref_take(v___y_4894_);
                v_traceState_4900_ = crate::leanh::lean_ctor_get(v___x_4899_, 4);
                v_env_4901_ = crate::leanh::lean_ctor_get(v___x_4899_, 0);
                v_nextMacroScope_4902_ = crate::leanh::lean_ctor_get(v___x_4899_, 1);
                v_ngen_4903_ = crate::leanh::lean_ctor_get(v___x_4899_, 2);
                v_auxDeclNGen_4904_ = crate::leanh::lean_ctor_get(v___x_4899_, 3);
                v_cache_4905_ = crate::leanh::lean_ctor_get(v___x_4899_, 5);
                v_messages_4906_ = crate::leanh::lean_ctor_get(v___x_4899_, 6);
                v_infoState_4907_ = crate::leanh::lean_ctor_get(v___x_4899_, 7);
                v_snapshotTasks_4908_ = crate::leanh::lean_ctor_get(v___x_4899_, 8);
                v_isSharedCheck_4927_ = (!crate::leanh::lean_is_exclusive(v___x_4899_)) as u8;
                if v_isSharedCheck_4927_ == 0 {
                    v___x_4910_ = v___x_4899_;
                    v_isShared_4911_ = v_isSharedCheck_4927_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_4908_);
                    crate::leanh::lean_inc(v_infoState_4907_);
                    crate::leanh::lean_inc(v_messages_4906_);
                    crate::leanh::lean_inc(v_cache_4905_);
                    crate::leanh::lean_inc(v_traceState_4900_);
                    crate::leanh::lean_inc(v_auxDeclNGen_4904_);
                    crate::leanh::lean_inc(v_ngen_4903_);
                    crate::leanh::lean_inc(v_nextMacroScope_4902_);
                    crate::leanh::lean_inc(v_env_4901_);
                    crate::leanh::lean_dec(v___x_4899_);
                    v___x_4910_ = crate::leanh::lean_box(0);
                    v_isShared_4911_ = v_isSharedCheck_4927_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_tid_4912_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_4900_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_4925_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_4900_)) as u8;
                if v_isSharedCheck_4925_ == 0 {
                    v_unused_4926_ = crate::leanh::lean_ctor_get(v_traceState_4900_, 0);
                    crate::leanh::lean_dec(v_unused_4926_);
                    v___x_4914_ = v_traceState_4900_;
                    v_isShared_4915_ = v_isSharedCheck_4925_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_traceState_4900_);
                    v___x_4914_ = crate::leanh::lean_box(0);
                    v_isShared_4915_ = v_isSharedCheck_4925_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4916_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__1_once), _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__1);
                if v_isShared_4915_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4914_, 0, v___x_4916_);
                    v___x_4918_ = v___x_4914_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4924_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4924_, 0, v___x_4916_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_4924_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_4912_,
                    );
                    v___x_4918_ = v_reuseFailAlloc_4924_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4911_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4910_, 4, v___x_4918_);
                    v___x_4920_ = v___x_4910_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4923_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4923_, 0, v_env_4901_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4923_, 1, v_nextMacroScope_4902_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4923_, 2, v_ngen_4903_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4923_, 3, v_auxDeclNGen_4904_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4923_, 4, v___x_4918_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4923_, 5, v_cache_4905_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4923_, 6, v_messages_4906_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4923_, 7, v_infoState_4907_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4923_, 8, v_snapshotTasks_4908_);
                    v___x_4920_ = v_reuseFailAlloc_4923_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4921_ = lean_st_ref_set(v___y_4894_, v___x_4920_);
                v___x_4922_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4922_, 0, v_traces_4898_);
                return v___x_4922_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___boxed(
    mut v___y_4928_: *mut crate::leanh::LeanObject,
    mut v___y_4929_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4930_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg(v___y_4928_);
    crate::leanh::lean_dec(v___y_4928_);
    return v_res_4930_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0(
    mut v___y_4931_: *mut crate::leanh::LeanObject,
    mut v___y_4932_: *mut crate::leanh::LeanObject,
    mut v___y_4933_: *mut crate::leanh::LeanObject,
    mut v___y_4934_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4936_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg(v___y_4934_);
    return v___x_4936_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___boxed(
    mut v___y_4937_: *mut crate::leanh::LeanObject,
    mut v___y_4938_: *mut crate::leanh::LeanObject,
    mut v___y_4939_: *mut crate::leanh::LeanObject,
    mut v___y_4940_: *mut crate::leanh::LeanObject,
    mut v___y_4941_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4942_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0(v___y_4937_, v___y_4938_, v___y_4939_, v___y_4940_);
    crate::leanh::lean_dec(v___y_4940_);
    crate::leanh::lean_dec_ref(v___y_4939_);
    crate::leanh::lean_dec(v___y_4938_);
    crate::leanh::lean_dec_ref(v___y_4937_);
    return v_res_4942_;
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(
    mut v_opts_4943_: *mut crate::leanh::LeanObject,
    mut v_opt_4944_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_4945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_4946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_4947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_4945_ = crate::leanh::lean_ctor_get(v_opt_4944_, 0);
    v_defValue_4946_ = crate::leanh::lean_ctor_get(v_opt_4944_, 1);
    v_map_4947_ = crate::leanh::lean_ctor_get(v_opts_4943_, 0);
    v___x_4948_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_4947_,
            v_name_4945_,
        );
    if crate::leanh::lean_obj_tag(v___x_4948_) == 0 {
        let mut v___x_4949_: u8 = 0;
        v___x_4949_ = (crate::leanh::lean_unbox(v_defValue_4946_) as u8);
        return v___x_4949_;
    } else {
        let mut v_val_4950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_4950_ = crate::leanh::lean_ctor_get(v___x_4948_, 0);
        crate::leanh::lean_inc(v_val_4950_);
        crate::leanh::lean_dec_ref_known(v___x_4948_, 1);
        if crate::leanh::lean_obj_tag(v_val_4950_) == 1 {
            let mut v_v_4951_: u8 = 0;
            v_v_4951_ = crate::leanh::lean_ctor_get_uint8(v_val_4950_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_4950_, 0);
            return v_v_4951_;
        } else {
            let mut v___x_4952_: u8 = 0;
            crate::leanh::lean_dec(v_val_4950_);
            v___x_4952_ = (crate::leanh::lean_unbox(v_defValue_4946_) as u8);
            return v___x_4952_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1___boxed(
    mut v_opts_4953_: *mut crate::leanh::LeanObject,
    mut v_opt_4954_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4955_: u8 = 0;
    let mut v_r_4956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4955_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_opts_4953_, v_opt_4954_);
    crate::leanh::lean_dec_ref(v_opt_4954_);
    crate::leanh::lean_dec_ref(v_opts_4953_);
    v_r_4956_ = crate::leanh::lean_box((v_res_4955_) as usize);
    return v_r_4956_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4958_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__0;
    v___x_4959_ = l_Lean_stringToMessageData(v___x_4958_);
    return v___x_4959_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4961_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__2;
    v___x_4962_ = l_Lean_stringToMessageData(v___x_4961_);
    return v___x_4962_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4966_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__5;
    v___x_4967_ = l_Lean_MessageData_ofFormat(v___x_4966_);
    return v___x_4967_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4971_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__8;
    v___x_4972_ = l_Lean_MessageData_ofFormat(v___x_4971_);
    return v___x_4972_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4976_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__11;
    v___x_4977_ = l_Lean_MessageData_ofFormat(v___x_4976_);
    return v___x_4977_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0(
    mut v_fst_4978_: *mut crate::leanh::LeanObject,
    mut v_snd_4979_: u8,
    mut v_x_4980_: *mut crate::leanh::LeanObject,
    mut v___y_4981_: *mut crate::leanh::LeanObject,
    mut v___y_4982_: *mut crate::leanh::LeanObject,
    mut v___y_4983_: *mut crate::leanh::LeanObject,
    mut v___y_4984_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4986_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__1_once), _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__1);
                v___x_4987_ = l_Lean_MessageData_ofName(v_fst_4978_);
                v___x_4988_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4988_, 0, v___x_4986_);
                crate::leanh::lean_ctor_set(v___x_4988_, 1, v___x_4987_);
                match v_snd_4979_ {
                    0 => {
                        v___x_4995_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__6_once), _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__6);
                        v___y_4990_ = v___x_4995_;
                        state = 1;
                        continue;
                    }
                    1 => {
                        v___x_4996_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__9_once), _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__9);
                        v___y_4990_ = v___x_4996_;
                        state = 1;
                        continue;
                    }
                    _ => {
                        v___x_4997_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__12), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__12_once), _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__12);
                        v___y_4990_ = v___x_4997_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v___y_4990_);
                v___x_4991_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4991_, 0, v___x_4988_);
                crate::leanh::lean_ctor_set(v___x_4991_, 1, v___y_4990_);
                v___x_4992_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__3_once), _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__3);
                v___x_4993_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4993_, 0, v___x_4991_);
                crate::leanh::lean_ctor_set(v___x_4993_, 1, v___x_4992_);
                v___x_4994_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4994_, 0, v___x_4993_);
                return v___x_4994_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___boxed(
    mut v_fst_4998_: *mut crate::leanh::LeanObject,
    mut v_snd_4999_: *mut crate::leanh::LeanObject,
    mut v_x_5000_: *mut crate::leanh::LeanObject,
    mut v___y_5001_: *mut crate::leanh::LeanObject,
    mut v___y_5002_: *mut crate::leanh::LeanObject,
    mut v___y_5003_: *mut crate::leanh::LeanObject,
    mut v___y_5004_: *mut crate::leanh::LeanObject,
    mut v___y_5005_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_snd_11731__boxed_5006_: u8 = 0;
    let mut v_res_5007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_snd_11731__boxed_5006_ = (crate::leanh::lean_unbox(v_snd_4999_) as u8);
    v_res_5007_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0(v_fst_4998_, v_snd_11731__boxed_5006_, v_x_5000_, v___y_5001_, v___y_5002_, v___y_5003_, v___y_5004_);
    crate::leanh::lean_dec(v___y_5004_);
    crate::leanh::lean_dec_ref(v___y_5003_);
    crate::leanh::lean_dec(v___y_5002_);
    crate::leanh::lean_dec_ref(v___y_5001_);
    crate::leanh::lean_dec_ref(v_x_5000_);
    return v_res_5007_;
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5(
    mut v_opts_5008_: *mut crate::leanh::LeanObject,
    mut v_opt_5009_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_5010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_5011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_5012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_5010_ = crate::leanh::lean_ctor_get(v_opt_5009_, 0);
    v_defValue_5011_ = crate::leanh::lean_ctor_get(v_opt_5009_, 1);
    v_map_5012_ = crate::leanh::lean_ctor_get(v_opts_5008_, 0);
    v___x_5013_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_5012_,
            v_name_5010_,
        );
    if crate::leanh::lean_obj_tag(v___x_5013_) == 0 {
        crate::leanh::lean_inc(v_defValue_5011_);
        return v_defValue_5011_;
    } else {
        let mut v_val_5014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_5014_ = crate::leanh::lean_ctor_get(v___x_5013_, 0);
        crate::leanh::lean_inc(v_val_5014_);
        crate::leanh::lean_dec_ref_known(v___x_5013_, 1);
        if crate::leanh::lean_obj_tag(v_val_5014_) == 3 {
            let mut v_v_5015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_v_5015_ = crate::leanh::lean_ctor_get(v_val_5014_, 0);
            crate::leanh::lean_inc(v_v_5015_);
            crate::leanh::lean_dec_ref_known(v_val_5014_, 1);
            return v_v_5015_;
        } else {
            crate::leanh::lean_dec(v_val_5014_);
            crate::leanh::lean_inc(v_defValue_5011_);
            return v_defValue_5011_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5___boxed(
    mut v_opts_5016_: *mut crate::leanh::LeanObject,
    mut v_opt_5017_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5018_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5(v_opts_5016_, v_opt_5017_);
    crate::leanh::lean_dec_ref(v_opt_5017_);
    crate::leanh::lean_dec_ref(v_opts_5016_);
    return v_res_5018_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__4___redArg(
    mut v_x_5019_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_5021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5024_: u8 = 0;
    let mut v___x_5026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5028_: u8 = 0;
    let mut v_a_5029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5032_: u8 = 0;
    let mut v___x_5034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5036_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5019_) == 0 {
                    v_a_5021_ = crate::leanh::lean_ctor_get(v_x_5019_, 0);
                    v_isSharedCheck_5028_ = (!crate::leanh::lean_is_exclusive(v_x_5019_)) as u8;
                    if v_isSharedCheck_5028_ == 0 {
                        v___x_5023_ = v_x_5019_;
                        v_isShared_5024_ = v_isSharedCheck_5028_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5021_);
                        crate::leanh::lean_dec(v_x_5019_);
                        v___x_5023_ = crate::leanh::lean_box(0);
                        v_isShared_5024_ = v_isSharedCheck_5028_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5029_ = crate::leanh::lean_ctor_get(v_x_5019_, 0);
                    v_isSharedCheck_5036_ = (!crate::leanh::lean_is_exclusive(v_x_5019_)) as u8;
                    if v_isSharedCheck_5036_ == 0 {
                        v___x_5031_ = v_x_5019_;
                        v_isShared_5032_ = v_isSharedCheck_5036_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5029_);
                        crate::leanh::lean_dec(v_x_5019_);
                        v___x_5031_ = crate::leanh::lean_box(0);
                        v_isShared_5032_ = v_isSharedCheck_5036_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5024_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5023_, 1);
                    v___x_5026_ = v___x_5023_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5027_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5027_, 0, v_a_5021_);
                    v___x_5026_ = v_reuseFailAlloc_5027_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5026_;
            }
            3 => {
                if v_isShared_5032_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5031_, 0);
                    v___x_5034_ = v___x_5031_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5035_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5035_, 0, v_a_5029_);
                    v___x_5034_ = v_reuseFailAlloc_5035_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5034_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__4___redArg___boxed(
    mut v_x_5037_: *mut crate::leanh::LeanObject,
    mut v___y_5038_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5039_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__4___redArg(v_x_5037_);
    return v_res_5039_;
}
pub unsafe fn l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2(
    mut v_e_5040_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_e_5040_) == 0 {
        let mut v___x_5041_: u8 = 0;
        v___x_5041_ = 2;
        return v___x_5041_;
    } else {
        let mut v___x_5042_: u8 = 0;
        v___x_5042_ = 0;
        return v___x_5042_;
    }
}
pub unsafe fn l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2___boxed(
    mut v_e_5043_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5044_: u8 = 0;
    let mut v_r_5045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5044_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2(v_e_5043_);
    crate::leanh::lean_dec_ref(v_e_5043_);
    v_r_5045_ = crate::leanh::lean_box((v_res_5044_) as usize);
    return v_r_5045_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3_spec__4(
    mut v_sz_5046_: usize,
    mut v_i_5047_: usize,
    mut v_bs_5048_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5049_: u8 = 0;
    let mut v_v_5050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_5051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5054_: usize = 0;
    let mut v___x_5055_: usize = 0;
    let mut v___x_5056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5049_ = lean_usize_dec_lt(v_i_5047_, v_sz_5046_);
                if v___x_5049_ == 0 {
                    return v_bs_5048_;
                } else {
                    v_v_5050_ = lean_array_uget_borrowed(v_bs_5048_, v_i_5047_);
                    v_msg_5051_ = crate::leanh::lean_ctor_get(v_v_5050_, 1);
                    crate::leanh::lean_inc_ref(v_msg_5051_);
                    v___x_5052_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_5053_ = lean_array_uset(v_bs_5048_, v_i_5047_, v___x_5052_);
                    v___x_5054_ = 1usize;
                    v___x_5055_ = lean_usize_add(v_i_5047_, v___x_5054_);
                    v___x_5056_ = lean_array_uset(v_bs_x27_5053_, v_i_5047_, v_msg_5051_);
                    v_i_5047_ = v___x_5055_;
                    v_bs_5048_ = v___x_5056_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3_spec__4___boxed(
    mut v_sz_5058_: *mut crate::leanh::LeanObject,
    mut v_i_5059_: *mut crate::leanh::LeanObject,
    mut v_bs_5060_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5061_: usize = 0;
    let mut v_i_boxed_5062_: usize = 0;
    let mut v_res_5063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5061_ = crate::leanh::lean_unbox_usize(v_sz_5058_);
    crate::leanh::lean_dec(v_sz_5058_);
    v_i_boxed_5062_ = crate::leanh::lean_unbox_usize(v_i_5059_);
    crate::leanh::lean_dec(v_i_5059_);
    v_res_5063_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3_spec__4(v_sz_boxed_5061_, v_i_boxed_5062_, v_bs_5060_);
    return v_res_5063_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3(
    mut v_oldTraces_5064_: *mut crate::leanh::LeanObject,
    mut v_data_5065_: *mut crate::leanh::LeanObject,
    mut v_ref_5066_: *mut crate::leanh::LeanObject,
    mut v_msg_5067_: *mut crate::leanh::LeanObject,
    mut v___y_5068_: *mut crate::leanh::LeanObject,
    mut v___y_5069_: *mut crate::leanh::LeanObject,
    mut v___y_5070_: *mut crate::leanh::LeanObject,
    mut v___y_5071_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_5073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_5074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_5075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_5076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_5077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_5081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_5082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_5083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5085_: u8 = 0;
    let mut v_cancelTk_x3f_5086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_5087_: u8 = 0;
    let mut v_inheritedTraceOptions_5088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traces_5091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5095_: usize = 0;
    let mut v___x_5096_: usize = 0;
    let mut v___x_5097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_5098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5103_: u8 = 0;
    let mut v___x_5104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_5110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5116_: u8 = 0;
    let mut v_tid_5117_: u64 = 0;
    let mut v___x_5119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5120_: u8 = 0;
    let mut v___x_5121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5134_: u8 = 0;
    let mut v_unused_5135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5136_: u8 = 0;
    let mut v_isSharedCheck_5137_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_5073_ = crate::leanh::lean_ctor_get(v___y_5070_, 0);
                v_fileMap_5074_ = crate::leanh::lean_ctor_get(v___y_5070_, 1);
                v_options_5075_ = crate::leanh::lean_ctor_get(v___y_5070_, 2);
                v_currRecDepth_5076_ = crate::leanh::lean_ctor_get(v___y_5070_, 3);
                v_maxRecDepth_5077_ = crate::leanh::lean_ctor_get(v___y_5070_, 4);
                v_ref_5078_ = crate::leanh::lean_ctor_get(v___y_5070_, 5);
                v_currNamespace_5079_ = crate::leanh::lean_ctor_get(v___y_5070_, 6);
                v_openDecls_5080_ = crate::leanh::lean_ctor_get(v___y_5070_, 7);
                v_initHeartbeats_5081_ = crate::leanh::lean_ctor_get(v___y_5070_, 8);
                v_maxHeartbeats_5082_ = crate::leanh::lean_ctor_get(v___y_5070_, 9);
                v_quotContext_5083_ = crate::leanh::lean_ctor_get(v___y_5070_, 10);
                v_currMacroScope_5084_ = crate::leanh::lean_ctor_get(v___y_5070_, 11);
                v_diag_5085_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_5070_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_5086_ = crate::leanh::lean_ctor_get(v___y_5070_, 12);
                v_suppressElabErrors_5087_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_5070_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_5088_ = crate::leanh::lean_ctor_get(v___y_5070_, 13);
                v___x_5089_ = lean_st_ref_get(v___y_5071_);
                v_traceState_5090_ = crate::leanh::lean_ctor_get(v___x_5089_, 4);
                crate::leanh::lean_inc_ref(v_traceState_5090_);
                crate::leanh::lean_dec(v___x_5089_);
                v_traces_5091_ = crate::leanh::lean_ctor_get(v_traceState_5090_, 0);
                crate::leanh::lean_inc_ref(v_traces_5091_);
                crate::leanh::lean_dec_ref(v_traceState_5090_);
                v_ref_5092_ = l_Lean_replaceRef(v_ref_5066_, v_ref_5078_);
                crate::leanh::lean_inc_ref(v_inheritedTraceOptions_5088_);
                crate::leanh::lean_inc(v_cancelTk_x3f_5086_);
                crate::leanh::lean_inc(v_currMacroScope_5084_);
                crate::leanh::lean_inc(v_quotContext_5083_);
                crate::leanh::lean_inc(v_maxHeartbeats_5082_);
                crate::leanh::lean_inc(v_initHeartbeats_5081_);
                crate::leanh::lean_inc(v_openDecls_5080_);
                crate::leanh::lean_inc(v_currNamespace_5079_);
                crate::leanh::lean_inc(v_maxRecDepth_5077_);
                crate::leanh::lean_inc(v_currRecDepth_5076_);
                crate::leanh::lean_inc_ref(v_options_5075_);
                crate::leanh::lean_inc_ref(v_fileMap_5074_);
                crate::leanh::lean_inc_ref(v_fileName_5073_);
                v___x_5093_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_5093_, 0, v_fileName_5073_);
                crate::leanh::lean_ctor_set(v___x_5093_, 1, v_fileMap_5074_);
                crate::leanh::lean_ctor_set(v___x_5093_, 2, v_options_5075_);
                crate::leanh::lean_ctor_set(v___x_5093_, 3, v_currRecDepth_5076_);
                crate::leanh::lean_ctor_set(v___x_5093_, 4, v_maxRecDepth_5077_);
                crate::leanh::lean_ctor_set(v___x_5093_, 5, v_ref_5092_);
                crate::leanh::lean_ctor_set(v___x_5093_, 6, v_currNamespace_5079_);
                crate::leanh::lean_ctor_set(v___x_5093_, 7, v_openDecls_5080_);
                crate::leanh::lean_ctor_set(v___x_5093_, 8, v_initHeartbeats_5081_);
                crate::leanh::lean_ctor_set(v___x_5093_, 9, v_maxHeartbeats_5082_);
                crate::leanh::lean_ctor_set(v___x_5093_, 10, v_quotContext_5083_);
                crate::leanh::lean_ctor_set(v___x_5093_, 11, v_currMacroScope_5084_);
                crate::leanh::lean_ctor_set(v___x_5093_, 12, v_cancelTk_x3f_5086_);
                crate::leanh::lean_ctor_set(v___x_5093_, 13, v_inheritedTraceOptions_5088_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5093_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                    v_diag_5085_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5093_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_5087_,
                );
                v___x_5094_ = l_Lean_PersistentArray_toArray___redArg(v_traces_5091_);
                crate::leanh::lean_dec_ref(v_traces_5091_);
                v_sz_5095_ = lean_array_size(v___x_5094_);
                v___x_5096_ = 0usize;
                v___x_5097_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3_spec__4(v_sz_5095_, v___x_5096_, v___x_5094_);
                v_msg_5098_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v_msg_5098_, 0, v_data_5065_);
                crate::leanh::lean_ctor_set(v_msg_5098_, 1, v_msg_5067_);
                crate::leanh::lean_ctor_set(v_msg_5098_, 2, v___x_5097_);
                v___x_5099_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0_spec__0(v_msg_5098_, v___y_5068_, v___y_5069_, v___x_5093_, v___y_5071_);
                crate::leanh::lean_dec_ref_known(v___x_5093_, 14);
                v_a_5100_ = crate::leanh::lean_ctor_get(v___x_5099_, 0);
                v_isSharedCheck_5137_ = (!crate::leanh::lean_is_exclusive(v___x_5099_)) as u8;
                if v_isSharedCheck_5137_ == 0 {
                    v___x_5102_ = v___x_5099_;
                    v_isShared_5103_ = v_isSharedCheck_5137_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_5100_);
                    crate::leanh::lean_dec(v___x_5099_);
                    v___x_5102_ = crate::leanh::lean_box(0);
                    v_isShared_5103_ = v_isSharedCheck_5137_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5104_ = lean_st_ref_take(v___y_5071_);
                v_traceState_5105_ = crate::leanh::lean_ctor_get(v___x_5104_, 4);
                v_env_5106_ = crate::leanh::lean_ctor_get(v___x_5104_, 0);
                v_nextMacroScope_5107_ = crate::leanh::lean_ctor_get(v___x_5104_, 1);
                v_ngen_5108_ = crate::leanh::lean_ctor_get(v___x_5104_, 2);
                v_auxDeclNGen_5109_ = crate::leanh::lean_ctor_get(v___x_5104_, 3);
                v_cache_5110_ = crate::leanh::lean_ctor_get(v___x_5104_, 5);
                v_messages_5111_ = crate::leanh::lean_ctor_get(v___x_5104_, 6);
                v_infoState_5112_ = crate::leanh::lean_ctor_get(v___x_5104_, 7);
                v_snapshotTasks_5113_ = crate::leanh::lean_ctor_get(v___x_5104_, 8);
                v_isSharedCheck_5136_ = (!crate::leanh::lean_is_exclusive(v___x_5104_)) as u8;
                if v_isSharedCheck_5136_ == 0 {
                    v___x_5115_ = v___x_5104_;
                    v_isShared_5116_ = v_isSharedCheck_5136_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_5113_);
                    crate::leanh::lean_inc(v_infoState_5112_);
                    crate::leanh::lean_inc(v_messages_5111_);
                    crate::leanh::lean_inc(v_cache_5110_);
                    crate::leanh::lean_inc(v_traceState_5105_);
                    crate::leanh::lean_inc(v_auxDeclNGen_5109_);
                    crate::leanh::lean_inc(v_ngen_5108_);
                    crate::leanh::lean_inc(v_nextMacroScope_5107_);
                    crate::leanh::lean_inc(v_env_5106_);
                    crate::leanh::lean_dec(v___x_5104_);
                    v___x_5115_ = crate::leanh::lean_box(0);
                    v_isShared_5116_ = v_isSharedCheck_5136_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_5117_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_5105_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_5134_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_5105_)) as u8;
                if v_isSharedCheck_5134_ == 0 {
                    v_unused_5135_ = crate::leanh::lean_ctor_get(v_traceState_5105_, 0);
                    crate::leanh::lean_dec(v_unused_5135_);
                    v___x_5119_ = v_traceState_5105_;
                    v_isShared_5120_ = v_isSharedCheck_5134_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_traceState_5105_);
                    v___x_5119_ = crate::leanh::lean_box(0);
                    v_isShared_5120_ = v_isSharedCheck_5134_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5121_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5121_, 0, v_ref_5066_);
                crate::leanh::lean_ctor_set(v___x_5121_, 1, v_a_5100_);
                v___x_5122_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_5064_, v___x_5121_);
                if v_isShared_5120_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5119_, 0, v___x_5122_);
                    v___x_5124_ = v___x_5119_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5133_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5133_, 0, v___x_5122_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_5133_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_5117_,
                    );
                    v___x_5124_ = v_reuseFailAlloc_5133_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_5116_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5115_, 4, v___x_5124_);
                    v___x_5126_ = v___x_5115_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5132_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5132_, 0, v_env_5106_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5132_, 1, v_nextMacroScope_5107_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5132_, 2, v_ngen_5108_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5132_, 3, v_auxDeclNGen_5109_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5132_, 4, v___x_5124_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5132_, 5, v_cache_5110_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5132_, 6, v_messages_5111_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5132_, 7, v_infoState_5112_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5132_, 8, v_snapshotTasks_5113_);
                    v___x_5126_ = v_reuseFailAlloc_5132_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5127_ = lean_st_ref_set(v___y_5071_, v___x_5126_);
                v___x_5128_ = crate::leanh::lean_box(0);
                if v_isShared_5103_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5102_, 0, v___x_5128_);
                    v___x_5130_ = v___x_5102_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5131_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5131_, 0, v___x_5128_);
                    v___x_5130_ = v_reuseFailAlloc_5131_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5130_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___boxed(
    mut v_oldTraces_5138_: *mut crate::leanh::LeanObject,
    mut v_data_5139_: *mut crate::leanh::LeanObject,
    mut v_ref_5140_: *mut crate::leanh::LeanObject,
    mut v_msg_5141_: *mut crate::leanh::LeanObject,
    mut v___y_5142_: *mut crate::leanh::LeanObject,
    mut v___y_5143_: *mut crate::leanh::LeanObject,
    mut v___y_5144_: *mut crate::leanh::LeanObject,
    mut v___y_5145_: *mut crate::leanh::LeanObject,
    mut v___y_5146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5147_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3(v_oldTraces_5138_, v_data_5139_, v_ref_5140_, v_msg_5141_, v___y_5142_, v___y_5143_, v___y_5144_, v___y_5145_);
    crate::leanh::lean_dec(v___y_5145_);
    crate::leanh::lean_dec_ref(v___y_5144_);
    crate::leanh::lean_dec(v___y_5143_);
    crate::leanh::lean_dec_ref(v___y_5142_);
    return v_res_5147_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0()
-> f64 {
    let mut v___x_5148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5149_: f64 = 0.0;
    v___x_5148_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5149_ = lean_float_of_nat(v___x_5148_);
    return v___x_5149_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5151_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__1;
    v___x_5152_ = l_Lean_stringToMessageData(v___x_5151_);
    return v___x_5152_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3()
-> f64 {
    let mut v___x_5153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5154_: f64 = 0.0;
    v___x_5153_ = crate::leanh::lean_unsigned_to_nat(1000);
    v___x_5154_ = lean_float_of_nat(v___x_5153_);
    return v___x_5154_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2(
    mut v_cls_5155_: *mut crate::leanh::LeanObject,
    mut v_collapsed_5156_: u8,
    mut v_tag_5157_: *mut crate::leanh::LeanObject,
    mut v_opts_5158_: *mut crate::leanh::LeanObject,
    mut v_clsEnabled_5159_: u8,
    mut v_oldTraces_5160_: *mut crate::leanh::LeanObject,
    mut v_msg_5161_: *mut crate::leanh::LeanObject,
    mut v_resStartStop_5162_: *mut crate::leanh::LeanObject,
    mut v___y_5163_: *mut crate::leanh::LeanObject,
    mut v___y_5164_: *mut crate::leanh::LeanObject,
    mut v___y_5165_: *mut crate::leanh::LeanObject,
    mut v___y_5166_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_5168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5172_: u8 = 0;
    let mut v___y_5174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_5176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5182_: u8 = 0;
    let mut v___x_5184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5186_: u8 = 0;
    let mut v_fst_5187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5191_: u8 = 0;
    let mut v___x_5192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5193_: u8 = 0;
    let mut v___y_5195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_5197_: u8 = 0;
    let mut v___x_5198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_5204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5207_: f64 = 0.0;
    let mut v_data_5208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_5209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5210_: f64 = 0.0;
    let mut v___x_5211_: f64 = 0.0;
    let mut v_reuseFailAlloc_5212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5220_: u8 = 0;
    let mut v___x_5221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_5227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5233_: u8 = 0;
    let mut v_tid_5234_: u64 = 0;
    let mut v_traces_5235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5238_: u8 = 0;
    let mut v___x_5239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5248_: u8 = 0;
    let mut v_isSharedCheck_5249_: u8 = 0;
    let mut v___y_5251_: f64 = 0.0;
    let mut v___x_5252_: f64 = 0.0;
    let mut v___x_5253_: f64 = 0.0;
    let mut v___x_5254_: f64 = 0.0;
    let mut v___x_5255_: u8 = 0;
    let mut v___x_5256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5257_: u8 = 0;
    let mut v___x_5258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5260_: f64 = 0.0;
    let mut v___x_5261_: f64 = 0.0;
    let mut v___x_5262_: f64 = 0.0;
    let mut v___x_5263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5265_: f64 = 0.0;
    let mut v_isSharedCheck_5266_: u8 = 0;
    let mut v_isSharedCheck_5267_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_5168_ = crate::leanh::lean_ctor_get(v_resStartStop_5162_, 0);
                v_snd_5169_ = crate::leanh::lean_ctor_get(v_resStartStop_5162_, 1);
                v_isSharedCheck_5267_ =
                    (!crate::leanh::lean_is_exclusive(v_resStartStop_5162_)) as u8;
                if v_isSharedCheck_5267_ == 0 {
                    v___x_5171_ = v_resStartStop_5162_;
                    v_isShared_5172_ = v_isSharedCheck_5267_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_5169_);
                    crate::leanh::lean_inc(v_fst_5168_);
                    crate::leanh::lean_dec(v_resStartStop_5162_);
                    v___x_5171_ = crate::leanh::lean_box(0);
                    v_isShared_5172_ = v_isSharedCheck_5267_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_5187_ = crate::leanh::lean_ctor_get(v_snd_5169_, 0);
                v_snd_5188_ = crate::leanh::lean_ctor_get(v_snd_5169_, 1);
                v_isSharedCheck_5266_ = (!crate::leanh::lean_is_exclusive(v_snd_5169_)) as u8;
                if v_isSharedCheck_5266_ == 0 {
                    v___x_5190_ = v_snd_5169_;
                    v_isShared_5191_ = v_isSharedCheck_5266_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_5188_);
                    crate::leanh::lean_inc(v_fst_5187_);
                    crate::leanh::lean_dec(v_snd_5169_);
                    v___x_5190_ = crate::leanh::lean_box(0);
                    v_isShared_5191_ = v_isSharedCheck_5266_;
                    state = 5;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v___y_5174_);
                v___x_5177_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3(v_oldTraces_5160_, v_data_5176_, v___y_5174_, v___y_5175_, v___y_5163_, v___y_5164_, v___y_5165_, v___y_5166_);
                if crate::leanh::lean_obj_tag(v___x_5177_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_5177_, 1);
                    v___x_5178_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__4___redArg(v_fst_5168_);
                    return v___x_5178_;
                } else {
                    crate::leanh::lean_dec(v_fst_5168_);
                    v_a_5179_ = crate::leanh::lean_ctor_get(v___x_5177_, 0);
                    v_isSharedCheck_5186_ = (!crate::leanh::lean_is_exclusive(v___x_5177_)) as u8;
                    if v_isSharedCheck_5186_ == 0 {
                        v___x_5181_ = v___x_5177_;
                        v_isShared_5182_ = v_isSharedCheck_5186_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5179_);
                        crate::leanh::lean_dec(v___x_5177_);
                        v___x_5181_ = crate::leanh::lean_box(0);
                        v_isShared_5182_ = v_isSharedCheck_5186_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_5182_ == 0 {
                    v___x_5184_ = v___x_5181_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5185_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5185_, 0, v_a_5179_);
                    v___x_5184_ = v_reuseFailAlloc_5185_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5184_;
            }
            5 => {
                v___x_5192_ = l_Lean_trace_profiler;
                v___x_5193_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_opts_5158_, v___x_5192_);
                if v___x_5193_ == 0 {
                    v___y_5220_ = v___x_5193_;
                    state = 10;
                    continue;
                } else {
                    v___x_5256_ = l_Lean_trace_profiler_useHeartbeats;
                    v___x_5257_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_opts_5158_, v___x_5256_);
                    if v___x_5257_ == 0 {
                        v___x_5258_ = l_Lean_trace_profiler_threshold;
                        v___x_5259_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5(v_opts_5158_, v___x_5258_);
                        v___x_5260_ = lean_float_of_nat(v___x_5259_);
                        v___x_5261_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3);
                        v___x_5262_ = lean_float_div(v___x_5260_, v___x_5261_);
                        v___y_5251_ = v___x_5262_;
                        state = 15;
                        continue;
                    } else {
                        v___x_5263_ = l_Lean_trace_profiler_threshold;
                        v___x_5264_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5(v_opts_5158_, v___x_5263_);
                        v___x_5265_ = lean_float_of_nat(v___x_5264_);
                        v___y_5251_ = v___x_5265_;
                        state = 15;
                        continue;
                    }
                }
            }
            6 => {
                v_result_5197_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2(v_fst_5168_);
                v___x_5198_ = l_Lean_TraceResult_toEmoji(v_result_5197_);
                v___x_5199_ = l_Lean_stringToMessageData(v___x_5198_);
                v___x_5200_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__3_once), _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__3);
                if v_isShared_5191_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5190_, 7);
                    crate::leanh::lean_ctor_set(v___x_5190_, 1, v___x_5200_);
                    crate::leanh::lean_ctor_set(v___x_5190_, 0, v___x_5199_);
                    v___x_5202_ = v___x_5190_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5213_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5213_, 0, v___x_5199_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5213_, 1, v___x_5200_);
                    v___x_5202_ = v_reuseFailAlloc_5213_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_5172_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5171_, 7);
                    crate::leanh::lean_ctor_set(v___x_5171_, 1, v_a_5196_);
                    crate::leanh::lean_ctor_set(v___x_5171_, 0, v___x_5202_);
                    v_m_5204_ = v___x_5171_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5212_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5212_, 0, v___x_5202_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5212_, 1, v_a_5196_);
                    v_m_5204_ = v_reuseFailAlloc_5212_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_5205_ = crate::leanh::lean_box((v_result_5197_) as usize);
                v___x_5206_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5206_, 0, v___x_5205_);
                v___x_5207_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0);
                crate::leanh::lean_inc_ref(v_tag_5157_);
                crate::leanh::lean_inc_ref(v___x_5206_);
                crate::leanh::lean_inc(v_cls_5155_);
                v_data_5208_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v_data_5208_, 0, v_cls_5155_);
                crate::leanh::lean_ctor_set(v_data_5208_, 1, v___x_5206_);
                crate::leanh::lean_ctor_set(v_data_5208_, 2, v_tag_5157_);
                crate::leanh::lean_ctor_set_float(
                    v_data_5208_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_5207_,
                );
                crate::leanh::lean_ctor_set_float(
                    v_data_5208_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_5207_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v_data_5208_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v_collapsed_5156_,
                );
                if v___x_5193_ == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_5206_, 1);
                    crate::leanh::lean_dec(v_snd_5188_);
                    crate::leanh::lean_dec(v_fst_5187_);
                    crate::leanh::lean_dec_ref(v_tag_5157_);
                    crate::leanh::lean_dec(v_cls_5155_);
                    v___y_5174_ = v___y_5195_;
                    v___y_5175_ = v_m_5204_;
                    v_data_5176_ = v_data_5208_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref_known(v_data_5208_, 3);
                    v_data_5209_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                    crate::leanh::lean_ctor_set(v_data_5209_, 0, v_cls_5155_);
                    crate::leanh::lean_ctor_set(v_data_5209_, 1, v___x_5206_);
                    crate::leanh::lean_ctor_set(v_data_5209_, 2, v_tag_5157_);
                    v___x_5210_ = crate::leanh::lean_unbox_float(v_fst_5187_);
                    crate::leanh::lean_dec(v_fst_5187_);
                    crate::leanh::lean_ctor_set_float(
                        v_data_5209_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v___x_5210_,
                    );
                    v___x_5211_ = crate::leanh::lean_unbox_float(v_snd_5188_);
                    crate::leanh::lean_dec(v_snd_5188_);
                    crate::leanh::lean_ctor_set_float(
                        v_data_5209_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                        v___x_5211_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_data_5209_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                        v_collapsed_5156_,
                    );
                    v___y_5174_ = v___y_5195_;
                    v___y_5175_ = v_m_5204_;
                    v_data_5176_ = v_data_5209_;
                    state = 2;
                    continue;
                }
            }
            9 => {
                v_ref_5215_ = crate::leanh::lean_ctor_get(v___y_5165_, 5);
                crate::leanh::lean_inc(v___y_5166_);
                crate::leanh::lean_inc_ref(v___y_5165_);
                crate::leanh::lean_inc(v___y_5164_);
                crate::leanh::lean_inc_ref(v___y_5163_);
                crate::leanh::lean_inc(v_fst_5168_);
                v___x_5216_ = crate::leanh::lean_apply_6(
                    v_msg_5161_,
                    v_fst_5168_,
                    v___y_5163_,
                    v___y_5164_,
                    v___y_5165_,
                    v___y_5166_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_5216_) == 0 {
                    v_a_5217_ = crate::leanh::lean_ctor_get(v___x_5216_, 0);
                    crate::leanh::lean_inc(v_a_5217_);
                    crate::leanh::lean_dec_ref_known(v___x_5216_, 1);
                    v___y_5195_ = v_ref_5215_;
                    v_a_5196_ = v_a_5217_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_5216_, 1);
                    v___x_5218_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2);
                    v___y_5195_ = v_ref_5215_;
                    v_a_5196_ = v___x_5218_;
                    state = 6;
                    continue;
                }
            }
            10 => {
                if v_clsEnabled_5159_ == 0 {
                    if v___y_5220_ == 0 {
                        crate::leanh::lean_del_object(v___x_5190_);
                        crate::leanh::lean_dec(v_snd_5188_);
                        crate::leanh::lean_dec(v_fst_5187_);
                        crate::leanh::lean_del_object(v___x_5171_);
                        crate::leanh::lean_dec_ref(v_msg_5161_);
                        crate::leanh::lean_dec_ref(v_tag_5157_);
                        crate::leanh::lean_dec(v_cls_5155_);
                        v___x_5221_ = lean_st_ref_take(v___y_5166_);
                        v_traceState_5222_ = crate::leanh::lean_ctor_get(v___x_5221_, 4);
                        v_env_5223_ = crate::leanh::lean_ctor_get(v___x_5221_, 0);
                        v_nextMacroScope_5224_ = crate::leanh::lean_ctor_get(v___x_5221_, 1);
                        v_ngen_5225_ = crate::leanh::lean_ctor_get(v___x_5221_, 2);
                        v_auxDeclNGen_5226_ = crate::leanh::lean_ctor_get(v___x_5221_, 3);
                        v_cache_5227_ = crate::leanh::lean_ctor_get(v___x_5221_, 5);
                        v_messages_5228_ = crate::leanh::lean_ctor_get(v___x_5221_, 6);
                        v_infoState_5229_ = crate::leanh::lean_ctor_get(v___x_5221_, 7);
                        v_snapshotTasks_5230_ = crate::leanh::lean_ctor_get(v___x_5221_, 8);
                        v_isSharedCheck_5249_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5221_)) as u8;
                        if v_isSharedCheck_5249_ == 0 {
                            v___x_5232_ = v___x_5221_;
                            v_isShared_5233_ = v_isSharedCheck_5249_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snapshotTasks_5230_);
                            crate::leanh::lean_inc(v_infoState_5229_);
                            crate::leanh::lean_inc(v_messages_5228_);
                            crate::leanh::lean_inc(v_cache_5227_);
                            crate::leanh::lean_inc(v_traceState_5222_);
                            crate::leanh::lean_inc(v_auxDeclNGen_5226_);
                            crate::leanh::lean_inc(v_ngen_5225_);
                            crate::leanh::lean_inc(v_nextMacroScope_5224_);
                            crate::leanh::lean_inc(v_env_5223_);
                            crate::leanh::lean_dec(v___x_5221_);
                            v___x_5232_ = crate::leanh::lean_box(0);
                            v_isShared_5233_ = v_isSharedCheck_5249_;
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
                v_tid_5234_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_5222_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_5235_ = crate::leanh::lean_ctor_get(v_traceState_5222_, 0);
                v_isSharedCheck_5248_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_5222_)) as u8;
                if v_isSharedCheck_5248_ == 0 {
                    v___x_5237_ = v_traceState_5222_;
                    v_isShared_5238_ = v_isSharedCheck_5248_;
                    state = 12;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_5235_);
                    crate::leanh::lean_dec(v_traceState_5222_);
                    v___x_5237_ = crate::leanh::lean_box(0);
                    v_isShared_5238_ = v_isSharedCheck_5248_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_5239_ =
                    l_Lean_PersistentArray_append___redArg(v_oldTraces_5160_, v_traces_5235_);
                crate::leanh::lean_dec_ref(v_traces_5235_);
                if v_isShared_5238_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5237_, 0, v___x_5239_);
                    v___x_5241_ = v___x_5237_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_5247_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5247_, 0, v___x_5239_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_5247_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_5234_,
                    );
                    v___x_5241_ = v_reuseFailAlloc_5247_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_5233_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5232_, 4, v___x_5241_);
                    v___x_5243_ = v___x_5232_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5246_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5246_, 0, v_env_5223_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5246_, 1, v_nextMacroScope_5224_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5246_, 2, v_ngen_5225_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5246_, 3, v_auxDeclNGen_5226_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5246_, 4, v___x_5241_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5246_, 5, v_cache_5227_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5246_, 6, v_messages_5228_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5246_, 7, v_infoState_5229_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5246_, 8, v_snapshotTasks_5230_);
                    v___x_5243_ = v_reuseFailAlloc_5246_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_5244_ = lean_st_ref_set(v___y_5166_, v___x_5243_);
                v___x_5245_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__4___redArg(v_fst_5168_);
                return v___x_5245_;
            }
            15 => {
                v___x_5252_ = crate::leanh::lean_unbox_float(v_snd_5188_);
                v___x_5253_ = crate::leanh::lean_unbox_float(v_fst_5187_);
                v___x_5254_ = lean_float_sub(v___x_5252_, v___x_5253_);
                v___x_5255_ = lean_float_decLt(v___y_5251_, v___x_5254_);
                v___y_5220_ = v___x_5255_;
                state = 10;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___boxed(
    mut v_cls_5268_: *mut crate::leanh::LeanObject,
    mut v_collapsed_5269_: *mut crate::leanh::LeanObject,
    mut v_tag_5270_: *mut crate::leanh::LeanObject,
    mut v_opts_5271_: *mut crate::leanh::LeanObject,
    mut v_clsEnabled_5272_: *mut crate::leanh::LeanObject,
    mut v_oldTraces_5273_: *mut crate::leanh::LeanObject,
    mut v_msg_5274_: *mut crate::leanh::LeanObject,
    mut v_resStartStop_5275_: *mut crate::leanh::LeanObject,
    mut v___y_5276_: *mut crate::leanh::LeanObject,
    mut v___y_5277_: *mut crate::leanh::LeanObject,
    mut v___y_5278_: *mut crate::leanh::LeanObject,
    mut v___y_5279_: *mut crate::leanh::LeanObject,
    mut v___y_5280_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_collapsed_boxed_5281_: u8 = 0;
    let mut v_clsEnabled_boxed_5282_: u8 = 0;
    let mut v_res_5283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_5281_ = (crate::leanh::lean_unbox(v_collapsed_5269_) as u8);
    v_clsEnabled_boxed_5282_ = (crate::leanh::lean_unbox(v_clsEnabled_5272_) as u8);
    v_res_5283_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2(v_cls_5268_, v_collapsed_boxed_5281_, v_tag_5270_, v_opts_5271_, v_clsEnabled_boxed_5282_, v_oldTraces_5273_, v_msg_5274_, v_resStartStop_5275_, v___y_5276_, v___y_5277_, v___y_5278_, v___y_5279_);
    crate::leanh::lean_dec(v___y_5279_);
    crate::leanh::lean_dec_ref(v___y_5278_);
    crate::leanh::lean_dec(v___y_5277_);
    crate::leanh::lean_dec_ref(v___y_5276_);
    crate::leanh::lean_dec_ref(v_opts_5271_);
    return v_res_5283_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5287_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__2_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_;
    v___x_5288_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__1;
    v___x_5289_ = l_Lean_Name_append(v___x_5288_, v___x_5287_);
    return v___x_5289_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3()
-> f64 {
    let mut v___x_5290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5291_: f64 = 0.0;
    v___x_5290_ = crate::leanh::lean_unsigned_to_nat(1000000000);
    v___x_5291_ = lean_float_of_nat(v___x_5290_);
    return v___x_5291_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma(
    mut v_cfg_5292_: *mut crate::leanh::LeanObject,
    mut v_act_5293_: *mut crate::leanh::LeanObject,
    mut v_allowFailure_5294_: *mut crate::leanh::LeanObject,
    mut v_cand_5295_: *mut crate::leanh::LeanObject,
    mut v_a_5296_: *mut crate::leanh::LeanObject,
    mut v_a_5297_: *mut crate::leanh::LeanObject,
    mut v_a_5298_: *mut crate::leanh::LeanObject,
    mut v_a_5299_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_5301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5305_: u8 = 0;
    let mut v_options_5306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_5307_: u8 = 0;
    let mut v_fst_5308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_5313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_5315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5319_: u8 = 0;
    let mut v___x_5321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5323_: u8 = 0;
    let mut v___x_5324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5332_: u8 = 0;
    let mut v___x_5333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5337_: u8 = 0;
    let mut v___x_5338_: u8 = 0;
    let mut v___x_5339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5344_: u8 = 0;
    let mut v_a_5345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5348_: u8 = 0;
    let mut v___x_5350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5352_: u8 = 0;
    let mut v___x_5353_: u8 = 0;
    let mut v___x_5354_: u8 = 0;
    let mut v_a_5355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5358_: u8 = 0;
    let mut v___x_5360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5362_: u8 = 0;
    let mut v_reuseFailAlloc_5363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5364_: u8 = 0;
    let mut v_unused_5365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5370_: u8 = 0;
    let mut v_fst_5371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5375_: u8 = 0;
    let mut v_inheritedTraceOptions_5376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5381_: u8 = 0;
    let mut v___y_5383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5387_: f64 = 0.0;
    let mut v___x_5388_: f64 = 0.0;
    let mut v___x_5389_: f64 = 0.0;
    let mut v___x_5390_: f64 = 0.0;
    let mut v___x_5391_: f64 = 0.0;
    let mut v___x_5392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5422_: u8 = 0;
    let mut v___x_5423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5425_: u8 = 0;
    let mut v___x_5426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5434_: f64 = 0.0;
    let mut v___x_5435_: f64 = 0.0;
    let mut v___x_5436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5464_: u8 = 0;
    let mut v___x_5465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5467_: u8 = 0;
    let mut v___x_5468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5475_: u8 = 0;
    let mut v___x_5476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_5478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_5480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5484_: u8 = 0;
    let mut v___x_5486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5488_: u8 = 0;
    let mut v___x_5489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5497_: u8 = 0;
    let mut v___x_5498_: u8 = 0;
    let mut v_a_5499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5501_: u8 = 0;
    let mut v_unused_5502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_5505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_5507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5511_: u8 = 0;
    let mut v___x_5513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5515_: u8 = 0;
    let mut v___x_5516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5524_: u8 = 0;
    let mut v___x_5525_: u8 = 0;
    let mut v_a_5526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5528_: u8 = 0;
    let mut v_unused_5529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5531_: u8 = 0;
    let mut v___x_5532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_5533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_5535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5539_: u8 = 0;
    let mut v___x_5541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5543_: u8 = 0;
    let mut v___x_5544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5552_: u8 = 0;
    let mut v___x_5553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5557_: u8 = 0;
    let mut v___x_5558_: u8 = 0;
    let mut v___x_5559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5564_: u8 = 0;
    let mut v_a_5565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5568_: u8 = 0;
    let mut v___x_5570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5572_: u8 = 0;
    let mut v___x_5573_: u8 = 0;
    let mut v___x_5574_: u8 = 0;
    let mut v_a_5575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5578_: u8 = 0;
    let mut v___x_5580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5582_: u8 = 0;
    let mut v_reuseFailAlloc_5583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5584_: u8 = 0;
    let mut v_unused_5585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5586_: u8 = 0;
    let mut v_isSharedCheck_5587_: u8 = 0;
    let mut v_isSharedCheck_5588_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_5301_ = crate::leanh::lean_ctor_get(v_cand_5295_, 0);
                v_snd_5302_ = crate::leanh::lean_ctor_get(v_cand_5295_, 1);
                v_isSharedCheck_5588_ = (!crate::leanh::lean_is_exclusive(v_cand_5295_)) as u8;
                if v_isSharedCheck_5588_ == 0 {
                    v___x_5304_ = v_cand_5295_;
                    v_isShared_5305_ = v_isSharedCheck_5588_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_5302_);
                    crate::leanh::lean_inc(v_fst_5301_);
                    crate::leanh::lean_dec(v_cand_5295_);
                    v___x_5304_ = crate::leanh::lean_box(0);
                    v_isShared_5305_ = v_isSharedCheck_5588_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_options_5306_ = crate::leanh::lean_ctor_get(v_a_5298_, 2);
                v_hasTrace_5307_ = crate::leanh::lean_ctor_get_uint8(
                    v_options_5306_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                if v_hasTrace_5307_ == 0 {
                    crate::leanh::lean_del_object(v___x_5304_);
                    v_fst_5308_ = crate::leanh::lean_ctor_get(v_fst_5301_, 0);
                    crate::leanh::lean_inc(v_fst_5308_);
                    v_snd_5309_ = crate::leanh::lean_ctor_get(v_fst_5301_, 1);
                    crate::leanh::lean_inc(v_snd_5309_);
                    crate::leanh::lean_dec(v_fst_5301_);
                    v_fst_5310_ = crate::leanh::lean_ctor_get(v_snd_5302_, 0);
                    crate::leanh::lean_inc(v_fst_5310_);
                    v_snd_5311_ = crate::leanh::lean_ctor_get(v_snd_5302_, 1);
                    crate::leanh::lean_inc(v_snd_5311_);
                    crate::leanh::lean_dec(v_snd_5302_);
                    v___x_5312_ = lean_st_ref_take(v_a_5297_);
                    v_cache_5313_ = crate::leanh::lean_ctor_get(v___x_5312_, 1);
                    v_zetaDeltaFVarIds_5314_ = crate::leanh::lean_ctor_get(v___x_5312_, 2);
                    v_postponed_5315_ = crate::leanh::lean_ctor_get(v___x_5312_, 3);
                    v_diag_5316_ = crate::leanh::lean_ctor_get(v___x_5312_, 4);
                    v_isSharedCheck_5364_ = (!crate::leanh::lean_is_exclusive(v___x_5312_)) as u8;
                    if v_isSharedCheck_5364_ == 0 {
                        v_unused_5365_ = crate::leanh::lean_ctor_get(v___x_5312_, 0);
                        crate::leanh::lean_dec(v_unused_5365_);
                        v___x_5318_ = v___x_5312_;
                        v_isShared_5319_ = v_isSharedCheck_5364_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_5316_);
                        crate::leanh::lean_inc(v_postponed_5315_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_5314_);
                        crate::leanh::lean_inc(v_cache_5313_);
                        crate::leanh::lean_dec(v___x_5312_);
                        v___x_5318_ = crate::leanh::lean_box(0);
                        v_isShared_5319_ = v_isSharedCheck_5364_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_fst_5366_ = crate::leanh::lean_ctor_get(v_fst_5301_, 0);
                    v_snd_5367_ = crate::leanh::lean_ctor_get(v_fst_5301_, 1);
                    v_isSharedCheck_5587_ = (!crate::leanh::lean_is_exclusive(v_fst_5301_)) as u8;
                    if v_isSharedCheck_5587_ == 0 {
                        v___x_5369_ = v_fst_5301_;
                        v_isShared_5370_ = v_isSharedCheck_5587_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_5367_);
                        crate::leanh::lean_inc(v_fst_5366_);
                        crate::leanh::lean_dec(v_fst_5301_);
                        v___x_5369_ = crate::leanh::lean_box(0);
                        v_isShared_5370_ = v_isSharedCheck_5587_;
                        state = 11;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_5319_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5318_, 0, v_snd_5309_);
                    v___x_5321_ = v___x_5318_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5363_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5363_, 0, v_snd_5309_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5363_, 1, v_cache_5313_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5363_,
                        2,
                        v_zetaDeltaFVarIds_5314_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5363_, 3, v_postponed_5315_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5363_, 4, v_diag_5316_);
                    v___x_5321_ = v_reuseFailAlloc_5363_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5322_ = lean_st_ref_set(v_a_5297_, v___x_5321_);
                v___x_5323_ = (crate::leanh::lean_unbox(v_snd_5311_) as u8);
                crate::leanh::lean_dec(v_snd_5311_);
                v___x_5324_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma(
                    v_fst_5310_,
                    v___x_5323_,
                    v_a_5296_,
                    v_a_5297_,
                    v_a_5298_,
                    v_a_5299_,
                );
                if crate::leanh::lean_obj_tag(v___x_5324_) == 0 {
                    v_a_5325_ = crate::leanh::lean_ctor_get(v___x_5324_, 0);
                    crate::leanh::lean_inc(v_a_5325_);
                    crate::leanh::lean_dec_ref_known(v___x_5324_, 1);
                    v___x_5326_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc(v_fst_5308_);
                    v___x_5327_ = l_Lean_MVarId_apply(
                        v_fst_5308_,
                        v_a_5325_,
                        v_cfg_5292_,
                        v___x_5326_,
                        v_a_5296_,
                        v_a_5297_,
                        v_a_5298_,
                        v_a_5299_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5327_) == 0 {
                        v_a_5328_ = crate::leanh::lean_ctor_get(v___x_5327_, 0);
                        crate::leanh::lean_inc_n(v_a_5328_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_5327_, 1);
                        crate::leanh::lean_inc(v_a_5299_);
                        crate::leanh::lean_inc_ref(v_a_5298_);
                        crate::leanh::lean_inc(v_a_5297_);
                        crate::leanh::lean_inc_ref(v_a_5296_);
                        v___x_5329_ = crate::leanh::lean_apply_6(
                            v_act_5293_,
                            v_a_5328_,
                            v_a_5296_,
                            v_a_5297_,
                            v_a_5298_,
                            v_a_5299_,
                            crate::leanh::lean_box(0),
                        );
                        if crate::leanh::lean_obj_tag(v___x_5329_) == 0 {
                            crate::leanh::lean_dec(v_a_5328_);
                            crate::leanh::lean_dec(v_fst_5308_);
                            crate::leanh::lean_dec_ref(v_allowFailure_5294_);
                            return v___x_5329_;
                        } else {
                            v_a_5330_ = crate::leanh::lean_ctor_get(v___x_5329_, 0);
                            crate::leanh::lean_inc(v_a_5330_);
                            v___x_5353_ = l_Lean_Exception_isInterrupt(v_a_5330_);
                            if v___x_5353_ == 0 {
                                v___x_5354_ = l_Lean_Exception_isRuntime(v_a_5330_);
                                v___y_5332_ = v___x_5354_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_a_5330_);
                                v___y_5332_ = v___x_5353_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_fst_5308_);
                        crate::leanh::lean_dec_ref(v_allowFailure_5294_);
                        crate::leanh::lean_dec_ref(v_act_5293_);
                        return v___x_5327_;
                    }
                } else {
                    crate::leanh::lean_dec(v_fst_5308_);
                    crate::leanh::lean_dec_ref(v_allowFailure_5294_);
                    crate::leanh::lean_dec_ref(v_act_5293_);
                    crate::leanh::lean_dec_ref(v_cfg_5292_);
                    v_a_5355_ = crate::leanh::lean_ctor_get(v___x_5324_, 0);
                    v_isSharedCheck_5362_ = (!crate::leanh::lean_is_exclusive(v___x_5324_)) as u8;
                    if v_isSharedCheck_5362_ == 0 {
                        v___x_5357_ = v___x_5324_;
                        v_isShared_5358_ = v_isSharedCheck_5362_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5355_);
                        crate::leanh::lean_dec(v___x_5324_);
                        v___x_5357_ = crate::leanh::lean_box(0);
                        v_isShared_5358_ = v_isSharedCheck_5362_;
                        state = 9;
                        continue;
                    }
                }
            }
            4 => {
                if v___y_5332_ == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_5329_, 1);
                    crate::leanh::lean_inc(v_a_5299_);
                    crate::leanh::lean_inc_ref(v_a_5298_);
                    crate::leanh::lean_inc(v_a_5297_);
                    crate::leanh::lean_inc_ref(v_a_5296_);
                    v___x_5333_ = crate::leanh::lean_apply_6(
                        v_allowFailure_5294_,
                        v_fst_5308_,
                        v_a_5296_,
                        v_a_5297_,
                        v_a_5298_,
                        v_a_5299_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_5333_) == 0 {
                        v_a_5334_ = crate::leanh::lean_ctor_get(v___x_5333_, 0);
                        v_isSharedCheck_5344_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5333_)) as u8;
                        if v_isSharedCheck_5344_ == 0 {
                            v___x_5336_ = v___x_5333_;
                            v_isShared_5337_ = v_isSharedCheck_5344_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5334_);
                            crate::leanh::lean_dec(v___x_5333_);
                            v___x_5336_ = crate::leanh::lean_box(0);
                            v_isShared_5337_ = v_isSharedCheck_5344_;
                            state = 5;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_5328_);
                        v_a_5345_ = crate::leanh::lean_ctor_get(v___x_5333_, 0);
                        v_isSharedCheck_5352_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5333_)) as u8;
                        if v_isSharedCheck_5352_ == 0 {
                            v___x_5347_ = v___x_5333_;
                            v_isShared_5348_ = v_isSharedCheck_5352_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5345_);
                            crate::leanh::lean_dec(v___x_5333_);
                            v___x_5347_ = crate::leanh::lean_box(0);
                            v_isShared_5348_ = v_isSharedCheck_5352_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_5328_);
                    crate::leanh::lean_dec(v_fst_5308_);
                    crate::leanh::lean_dec_ref(v_allowFailure_5294_);
                    return v___x_5329_;
                }
            }
            5 => {
                v___x_5338_ = (crate::leanh::lean_unbox(v_a_5334_) as u8);
                crate::leanh::lean_dec(v_a_5334_);
                if v___x_5338_ == 0 {
                    crate::leanh::lean_del_object(v___x_5336_);
                    crate::leanh::lean_dec(v_a_5328_);
                    v___x_5339_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1_once
                        ),
                        _init_l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1,
                    );
                    v___x_5340_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(v___x_5339_, v_a_5296_, v_a_5297_, v_a_5298_, v_a_5299_);
                    return v___x_5340_;
                } else {
                    if v_isShared_5337_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5336_, 0, v_a_5328_);
                        v___x_5342_ = v___x_5336_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_5343_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5343_, 0, v_a_5328_);
                        v___x_5342_ = v_reuseFailAlloc_5343_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_5342_;
            }
            7 => {
                if v_isShared_5348_ == 0 {
                    v___x_5350_ = v___x_5347_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5351_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5351_, 0, v_a_5345_);
                    v___x_5350_ = v_reuseFailAlloc_5351_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5350_;
            }
            9 => {
                if v_isShared_5358_ == 0 {
                    v___x_5360_ = v___x_5357_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5361_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5361_, 0, v_a_5355_);
                    v___x_5360_ = v_reuseFailAlloc_5361_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5360_;
            }
            11 => {
                v_fst_5371_ = crate::leanh::lean_ctor_get(v_snd_5302_, 0);
                v_snd_5372_ = crate::leanh::lean_ctor_get(v_snd_5302_, 1);
                v_isSharedCheck_5586_ = (!crate::leanh::lean_is_exclusive(v_snd_5302_)) as u8;
                if v_isSharedCheck_5586_ == 0 {
                    v___x_5374_ = v_snd_5302_;
                    v_isShared_5375_ = v_isSharedCheck_5586_;
                    state = 12;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_5372_);
                    crate::leanh::lean_inc(v_fst_5371_);
                    crate::leanh::lean_dec(v_snd_5302_);
                    v___x_5374_ = crate::leanh::lean_box(0);
                    v_isShared_5375_ = v_isSharedCheck_5586_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v_inheritedTraceOptions_5376_ = crate::leanh::lean_ctor_get(v_a_5298_, 13);
                crate::leanh::lean_inc(v_snd_5372_);
                crate::leanh::lean_inc(v_fst_5371_);
                v___f_5377_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___boxed as *mut core::ffi::c_void, 8, 2);
                crate::leanh::lean_closure_set(v___f_5377_, 0, v_fst_5371_);
                crate::leanh::lean_closure_set(v___f_5377_, 1, v_snd_5372_);
                v___x_5378_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__2_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_;
                v___x_5379_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__4;
                v___x_5380_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2_once), _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2);
                v___x_5381_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                    v_inheritedTraceOptions_5376_,
                    v_options_5306_,
                    v___x_5380_,
                );
                if v___x_5381_ == 0 {
                    v___x_5530_ = l_Lean_trace_profiler;
                    v___x_5531_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_options_5306_, v___x_5530_);
                    if v___x_5531_ == 0 {
                        crate::leanh::lean_dec_ref(v___f_5377_);
                        crate::leanh::lean_del_object(v___x_5374_);
                        crate::leanh::lean_del_object(v___x_5369_);
                        crate::leanh::lean_del_object(v___x_5304_);
                        v___x_5532_ = lean_st_ref_take(v_a_5297_);
                        v_cache_5533_ = crate::leanh::lean_ctor_get(v___x_5532_, 1);
                        v_zetaDeltaFVarIds_5534_ = crate::leanh::lean_ctor_get(v___x_5532_, 2);
                        v_postponed_5535_ = crate::leanh::lean_ctor_get(v___x_5532_, 3);
                        v_diag_5536_ = crate::leanh::lean_ctor_get(v___x_5532_, 4);
                        v_isSharedCheck_5584_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5532_)) as u8;
                        if v_isSharedCheck_5584_ == 0 {
                            v_unused_5585_ = crate::leanh::lean_ctor_get(v___x_5532_, 0);
                            crate::leanh::lean_dec(v_unused_5585_);
                            v___x_5538_ = v___x_5532_;
                            v_isShared_5539_ = v_isSharedCheck_5584_;
                            state = 31;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_diag_5536_);
                            crate::leanh::lean_inc(v_postponed_5535_);
                            crate::leanh::lean_inc(v_zetaDeltaFVarIds_5534_);
                            crate::leanh::lean_inc(v_cache_5533_);
                            crate::leanh::lean_dec(v___x_5532_);
                            v___x_5538_ = crate::leanh::lean_box(0);
                            v_isShared_5539_ = v_isSharedCheck_5584_;
                            state = 31;
                            continue;
                        }
                    } else {
                        state = 26;
                        continue;
                    }
                } else {
                    state = 26;
                    continue;
                }
            }
            13 => {
                v___x_5386_ = lean_io_mono_nanos_now();
                v___x_5387_ = lean_float_of_nat(v___y_5383_);
                v___x_5388_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3_once), _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3);
                v___x_5389_ = lean_float_div(v___x_5387_, v___x_5388_);
                v___x_5390_ = lean_float_of_nat(v___x_5386_);
                v___x_5391_ = lean_float_div(v___x_5390_, v___x_5388_);
                v___x_5392_ = crate::leanh::lean_box_float(v___x_5389_);
                v___x_5393_ = crate::leanh::lean_box_float(v___x_5391_);
                if v_isShared_5375_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5374_, 1, v___x_5393_);
                    crate::leanh::lean_ctor_set(v___x_5374_, 0, v___x_5392_);
                    v___x_5395_ = v___x_5374_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5400_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5400_, 0, v___x_5392_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5400_, 1, v___x_5393_);
                    v___x_5395_ = v_reuseFailAlloc_5400_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_5370_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5369_, 1, v___x_5395_);
                    crate::leanh::lean_ctor_set(v___x_5369_, 0, v_a_5385_);
                    v___x_5397_ = v___x_5369_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_5399_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5399_, 0, v_a_5385_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5399_, 1, v___x_5395_);
                    v___x_5397_ = v_reuseFailAlloc_5399_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v___x_5398_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2(v___x_5378_, v_hasTrace_5307_, v___x_5379_, v_options_5306_, v___x_5381_, v___y_5384_, v___f_5377_, v___x_5397_, v_a_5296_, v_a_5297_, v_a_5298_, v_a_5299_);
                return v___x_5398_;
            }
            16 => {
                v___x_5405_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5405_, 0, v_a_5404_);
                v___y_5383_ = v___y_5402_;
                v___y_5384_ = v___y_5403_;
                v_a_5385_ = v___x_5405_;
                state = 13;
                continue;
            }
            17 => {
                v___x_5410_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5410_, 0, v_a_5409_);
                v___y_5383_ = v___y_5407_;
                v___y_5384_ = v___y_5408_;
                v_a_5385_ = v___x_5410_;
                state = 13;
                continue;
            }
            18 => {
                if crate::leanh::lean_obj_tag(v___y_5414_) == 0 {
                    v_a_5415_ = crate::leanh::lean_ctor_get(v___y_5414_, 0);
                    crate::leanh::lean_inc(v_a_5415_);
                    crate::leanh::lean_dec_ref_known(v___y_5414_, 1);
                    v___y_5402_ = v___y_5412_;
                    v___y_5403_ = v___y_5413_;
                    v_a_5404_ = v_a_5415_;
                    state = 16;
                    continue;
                } else {
                    v_a_5416_ = crate::leanh::lean_ctor_get(v___y_5414_, 0);
                    crate::leanh::lean_inc(v_a_5416_);
                    crate::leanh::lean_dec_ref_known(v___y_5414_, 1);
                    v___y_5407_ = v___y_5412_;
                    v___y_5408_ = v___y_5413_;
                    v_a_5409_ = v_a_5416_;
                    state = 17;
                    continue;
                }
            }
            19 => {
                if v___y_5422_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_5420_);
                    crate::leanh::lean_inc(v_a_5299_);
                    crate::leanh::lean_inc_ref(v_a_5298_);
                    crate::leanh::lean_inc(v_a_5297_);
                    crate::leanh::lean_inc_ref(v_a_5296_);
                    v___x_5423_ = crate::leanh::lean_apply_6(
                        v_allowFailure_5294_,
                        v_fst_5366_,
                        v_a_5296_,
                        v_a_5297_,
                        v_a_5298_,
                        v_a_5299_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_5423_) == 0 {
                        v_a_5424_ = crate::leanh::lean_ctor_get(v___x_5423_, 0);
                        crate::leanh::lean_inc(v_a_5424_);
                        crate::leanh::lean_dec_ref_known(v___x_5423_, 1);
                        v___x_5425_ = (crate::leanh::lean_unbox(v_a_5424_) as u8);
                        crate::leanh::lean_dec(v_a_5424_);
                        if v___x_5425_ == 0 {
                            crate::leanh::lean_dec(v___y_5421_);
                            v___x_5426_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1_once
                                ),
                                _init_l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1,
                            );
                            v___x_5427_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(v___x_5426_, v_a_5296_, v_a_5297_, v_a_5298_, v_a_5299_);
                            v___y_5412_ = v___y_5418_;
                            v___y_5413_ = v___y_5419_;
                            v___y_5414_ = v___x_5427_;
                            state = 18;
                            continue;
                        } else {
                            v___y_5402_ = v___y_5418_;
                            v___y_5403_ = v___y_5419_;
                            v_a_5404_ = v___y_5421_;
                            state = 16;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___y_5421_);
                        v_a_5428_ = crate::leanh::lean_ctor_get(v___x_5423_, 0);
                        crate::leanh::lean_inc(v_a_5428_);
                        crate::leanh::lean_dec_ref_known(v___x_5423_, 1);
                        v___y_5407_ = v___y_5418_;
                        v___y_5408_ = v___y_5419_;
                        v_a_5409_ = v_a_5428_;
                        state = 17;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___y_5421_);
                    crate::leanh::lean_dec(v_fst_5366_);
                    crate::leanh::lean_dec_ref(v_allowFailure_5294_);
                    v___y_5407_ = v___y_5418_;
                    v___y_5408_ = v___y_5419_;
                    v_a_5409_ = v___y_5420_;
                    state = 17;
                    continue;
                }
            }
            20 => {
                v___x_5433_ = lean_io_get_num_heartbeats();
                v___x_5434_ = lean_float_of_nat(v___y_5431_);
                v___x_5435_ = lean_float_of_nat(v___x_5433_);
                v___x_5436_ = crate::leanh::lean_box_float(v___x_5434_);
                v___x_5437_ = crate::leanh::lean_box_float(v___x_5435_);
                if v_isShared_5305_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5304_, 1, v___x_5437_);
                    crate::leanh::lean_ctor_set(v___x_5304_, 0, v___x_5436_);
                    v___x_5439_ = v___x_5304_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_5442_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5442_, 0, v___x_5436_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5442_, 1, v___x_5437_);
                    v___x_5439_ = v_reuseFailAlloc_5442_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                v___x_5440_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5440_, 0, v_a_5432_);
                crate::leanh::lean_ctor_set(v___x_5440_, 1, v___x_5439_);
                v___x_5441_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2(v___x_5378_, v_hasTrace_5307_, v___x_5379_, v_options_5306_, v___x_5381_, v___y_5430_, v___f_5377_, v___x_5440_, v_a_5296_, v_a_5297_, v_a_5298_, v_a_5299_);
                return v___x_5441_;
            }
            22 => {
                v___x_5447_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5447_, 0, v_a_5446_);
                v___y_5430_ = v___y_5444_;
                v___y_5431_ = v___y_5445_;
                v_a_5432_ = v___x_5447_;
                state = 20;
                continue;
            }
            23 => {
                v___x_5452_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5452_, 0, v_a_5451_);
                v___y_5430_ = v___y_5449_;
                v___y_5431_ = v___y_5450_;
                v_a_5432_ = v___x_5452_;
                state = 20;
                continue;
            }
            24 => {
                if crate::leanh::lean_obj_tag(v___y_5456_) == 0 {
                    v_a_5457_ = crate::leanh::lean_ctor_get(v___y_5456_, 0);
                    crate::leanh::lean_inc(v_a_5457_);
                    crate::leanh::lean_dec_ref_known(v___y_5456_, 1);
                    v___y_5444_ = v___y_5454_;
                    v___y_5445_ = v___y_5455_;
                    v_a_5446_ = v_a_5457_;
                    state = 22;
                    continue;
                } else {
                    v_a_5458_ = crate::leanh::lean_ctor_get(v___y_5456_, 0);
                    crate::leanh::lean_inc(v_a_5458_);
                    crate::leanh::lean_dec_ref_known(v___y_5456_, 1);
                    v___y_5449_ = v___y_5454_;
                    v___y_5450_ = v___y_5455_;
                    v_a_5451_ = v_a_5458_;
                    state = 23;
                    continue;
                }
            }
            25 => {
                if v___y_5464_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_5463_);
                    crate::leanh::lean_inc(v_a_5299_);
                    crate::leanh::lean_inc_ref(v_a_5298_);
                    crate::leanh::lean_inc(v_a_5297_);
                    crate::leanh::lean_inc_ref(v_a_5296_);
                    v___x_5465_ = crate::leanh::lean_apply_6(
                        v_allowFailure_5294_,
                        v_fst_5366_,
                        v_a_5296_,
                        v_a_5297_,
                        v_a_5298_,
                        v_a_5299_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_5465_) == 0 {
                        v_a_5466_ = crate::leanh::lean_ctor_get(v___x_5465_, 0);
                        crate::leanh::lean_inc(v_a_5466_);
                        crate::leanh::lean_dec_ref_known(v___x_5465_, 1);
                        v___x_5467_ = (crate::leanh::lean_unbox(v_a_5466_) as u8);
                        crate::leanh::lean_dec(v_a_5466_);
                        if v___x_5467_ == 0 {
                            crate::leanh::lean_dec(v___y_5460_);
                            v___x_5468_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1_once
                                ),
                                _init_l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1,
                            );
                            v___x_5469_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(v___x_5468_, v_a_5296_, v_a_5297_, v_a_5298_, v_a_5299_);
                            v___y_5454_ = v___y_5461_;
                            v___y_5455_ = v___y_5462_;
                            v___y_5456_ = v___x_5469_;
                            state = 24;
                            continue;
                        } else {
                            v___y_5444_ = v___y_5461_;
                            v___y_5445_ = v___y_5462_;
                            v_a_5446_ = v___y_5460_;
                            state = 22;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___y_5460_);
                        v_a_5470_ = crate::leanh::lean_ctor_get(v___x_5465_, 0);
                        crate::leanh::lean_inc(v_a_5470_);
                        crate::leanh::lean_dec_ref_known(v___x_5465_, 1);
                        v___y_5449_ = v___y_5461_;
                        v___y_5450_ = v___y_5462_;
                        v_a_5451_ = v_a_5470_;
                        state = 23;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___y_5460_);
                    crate::leanh::lean_dec(v_fst_5366_);
                    crate::leanh::lean_dec_ref(v_allowFailure_5294_);
                    v___y_5449_ = v___y_5461_;
                    v___y_5450_ = v___y_5462_;
                    v_a_5451_ = v___y_5463_;
                    state = 23;
                    continue;
                }
            }
            26 => {
                v___x_5472_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg(v_a_5299_);
                v_a_5473_ = crate::leanh::lean_ctor_get(v___x_5472_, 0);
                crate::leanh::lean_inc(v_a_5473_);
                crate::leanh::lean_dec_ref(v___x_5472_);
                v___x_5474_ = l_Lean_trace_profiler_useHeartbeats;
                v___x_5475_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_options_5306_, v___x_5474_);
                if v___x_5475_ == 0 {
                    crate::leanh::lean_del_object(v___x_5304_);
                    v___x_5476_ = lean_io_mono_nanos_now();
                    v___x_5477_ = lean_st_ref_take(v_a_5297_);
                    v_cache_5478_ = crate::leanh::lean_ctor_get(v___x_5477_, 1);
                    v_zetaDeltaFVarIds_5479_ = crate::leanh::lean_ctor_get(v___x_5477_, 2);
                    v_postponed_5480_ = crate::leanh::lean_ctor_get(v___x_5477_, 3);
                    v_diag_5481_ = crate::leanh::lean_ctor_get(v___x_5477_, 4);
                    v_isSharedCheck_5501_ = (!crate::leanh::lean_is_exclusive(v___x_5477_)) as u8;
                    if v_isSharedCheck_5501_ == 0 {
                        v_unused_5502_ = crate::leanh::lean_ctor_get(v___x_5477_, 0);
                        crate::leanh::lean_dec(v_unused_5502_);
                        v___x_5483_ = v___x_5477_;
                        v_isShared_5484_ = v_isSharedCheck_5501_;
                        state = 27;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_5481_);
                        crate::leanh::lean_inc(v_postponed_5480_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_5479_);
                        crate::leanh::lean_inc(v_cache_5478_);
                        crate::leanh::lean_dec(v___x_5477_);
                        v___x_5483_ = crate::leanh::lean_box(0);
                        v_isShared_5484_ = v_isSharedCheck_5501_;
                        state = 27;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5374_);
                    crate::leanh::lean_del_object(v___x_5369_);
                    v___x_5503_ = lean_io_get_num_heartbeats();
                    v___x_5504_ = lean_st_ref_take(v_a_5297_);
                    v_cache_5505_ = crate::leanh::lean_ctor_get(v___x_5504_, 1);
                    v_zetaDeltaFVarIds_5506_ = crate::leanh::lean_ctor_get(v___x_5504_, 2);
                    v_postponed_5507_ = crate::leanh::lean_ctor_get(v___x_5504_, 3);
                    v_diag_5508_ = crate::leanh::lean_ctor_get(v___x_5504_, 4);
                    v_isSharedCheck_5528_ = (!crate::leanh::lean_is_exclusive(v___x_5504_)) as u8;
                    if v_isSharedCheck_5528_ == 0 {
                        v_unused_5529_ = crate::leanh::lean_ctor_get(v___x_5504_, 0);
                        crate::leanh::lean_dec(v_unused_5529_);
                        v___x_5510_ = v___x_5504_;
                        v_isShared_5511_ = v_isSharedCheck_5528_;
                        state = 29;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_5508_);
                        crate::leanh::lean_inc(v_postponed_5507_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_5506_);
                        crate::leanh::lean_inc(v_cache_5505_);
                        crate::leanh::lean_dec(v___x_5504_);
                        v___x_5510_ = crate::leanh::lean_box(0);
                        v_isShared_5511_ = v_isSharedCheck_5528_;
                        state = 29;
                        continue;
                    }
                }
            }
            27 => {
                if v_isShared_5484_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5483_, 0, v_snd_5367_);
                    v___x_5486_ = v___x_5483_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_5500_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5500_, 0, v_snd_5367_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5500_, 1, v_cache_5478_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5500_,
                        2,
                        v_zetaDeltaFVarIds_5479_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5500_, 3, v_postponed_5480_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5500_, 4, v_diag_5481_);
                    v___x_5486_ = v_reuseFailAlloc_5500_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                v___x_5487_ = lean_st_ref_set(v_a_5297_, v___x_5486_);
                v___x_5488_ = (crate::leanh::lean_unbox(v_snd_5372_) as u8);
                crate::leanh::lean_dec(v_snd_5372_);
                v___x_5489_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma(
                    v_fst_5371_,
                    v___x_5488_,
                    v_a_5296_,
                    v_a_5297_,
                    v_a_5298_,
                    v_a_5299_,
                );
                if crate::leanh::lean_obj_tag(v___x_5489_) == 0 {
                    v_a_5490_ = crate::leanh::lean_ctor_get(v___x_5489_, 0);
                    crate::leanh::lean_inc(v_a_5490_);
                    crate::leanh::lean_dec_ref_known(v___x_5489_, 1);
                    v___x_5491_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc(v_fst_5366_);
                    v___x_5492_ = l_Lean_MVarId_apply(
                        v_fst_5366_,
                        v_a_5490_,
                        v_cfg_5292_,
                        v___x_5491_,
                        v_a_5296_,
                        v_a_5297_,
                        v_a_5298_,
                        v_a_5299_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5492_) == 0 {
                        v_a_5493_ = crate::leanh::lean_ctor_get(v___x_5492_, 0);
                        crate::leanh::lean_inc_n(v_a_5493_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_5492_, 1);
                        crate::leanh::lean_inc(v_a_5299_);
                        crate::leanh::lean_inc_ref(v_a_5298_);
                        crate::leanh::lean_inc(v_a_5297_);
                        crate::leanh::lean_inc_ref(v_a_5296_);
                        v___x_5494_ = crate::leanh::lean_apply_6(
                            v_act_5293_,
                            v_a_5493_,
                            v_a_5296_,
                            v_a_5297_,
                            v_a_5298_,
                            v_a_5299_,
                            crate::leanh::lean_box(0),
                        );
                        if crate::leanh::lean_obj_tag(v___x_5494_) == 0 {
                            crate::leanh::lean_dec(v_a_5493_);
                            crate::leanh::lean_dec(v_fst_5366_);
                            crate::leanh::lean_dec_ref(v_allowFailure_5294_);
                            v_a_5495_ = crate::leanh::lean_ctor_get(v___x_5494_, 0);
                            crate::leanh::lean_inc(v_a_5495_);
                            crate::leanh::lean_dec_ref_known(v___x_5494_, 1);
                            v___y_5402_ = v___x_5476_;
                            v___y_5403_ = v_a_5473_;
                            v_a_5404_ = v_a_5495_;
                            state = 16;
                            continue;
                        } else {
                            v_a_5496_ = crate::leanh::lean_ctor_get(v___x_5494_, 0);
                            crate::leanh::lean_inc(v_a_5496_);
                            crate::leanh::lean_dec_ref_known(v___x_5494_, 1);
                            v___x_5497_ = l_Lean_Exception_isInterrupt(v_a_5496_);
                            if v___x_5497_ == 0 {
                                crate::leanh::lean_inc(v_a_5496_);
                                v___x_5498_ = l_Lean_Exception_isRuntime(v_a_5496_);
                                v___y_5418_ = v___x_5476_;
                                v___y_5419_ = v_a_5473_;
                                v___y_5420_ = v_a_5496_;
                                v___y_5421_ = v_a_5493_;
                                v___y_5422_ = v___x_5498_;
                                state = 19;
                                continue;
                            } else {
                                v___y_5418_ = v___x_5476_;
                                v___y_5419_ = v_a_5473_;
                                v___y_5420_ = v_a_5496_;
                                v___y_5421_ = v_a_5493_;
                                v___y_5422_ = v___x_5497_;
                                state = 19;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_fst_5366_);
                        crate::leanh::lean_dec_ref(v_allowFailure_5294_);
                        crate::leanh::lean_dec_ref(v_act_5293_);
                        v___y_5412_ = v___x_5476_;
                        v___y_5413_ = v_a_5473_;
                        v___y_5414_ = v___x_5492_;
                        state = 18;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_fst_5366_);
                    crate::leanh::lean_dec_ref(v_allowFailure_5294_);
                    crate::leanh::lean_dec_ref(v_act_5293_);
                    crate::leanh::lean_dec_ref(v_cfg_5292_);
                    v_a_5499_ = crate::leanh::lean_ctor_get(v___x_5489_, 0);
                    crate::leanh::lean_inc(v_a_5499_);
                    crate::leanh::lean_dec_ref_known(v___x_5489_, 1);
                    v___y_5407_ = v___x_5476_;
                    v___y_5408_ = v_a_5473_;
                    v_a_5409_ = v_a_5499_;
                    state = 17;
                    continue;
                }
            }
            29 => {
                if v_isShared_5511_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5510_, 0, v_snd_5367_);
                    v___x_5513_ = v___x_5510_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_5527_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5527_, 0, v_snd_5367_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5527_, 1, v_cache_5505_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5527_,
                        2,
                        v_zetaDeltaFVarIds_5506_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5527_, 3, v_postponed_5507_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5527_, 4, v_diag_5508_);
                    v___x_5513_ = v_reuseFailAlloc_5527_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                v___x_5514_ = lean_st_ref_set(v_a_5297_, v___x_5513_);
                v___x_5515_ = (crate::leanh::lean_unbox(v_snd_5372_) as u8);
                crate::leanh::lean_dec(v_snd_5372_);
                v___x_5516_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma(
                    v_fst_5371_,
                    v___x_5515_,
                    v_a_5296_,
                    v_a_5297_,
                    v_a_5298_,
                    v_a_5299_,
                );
                if crate::leanh::lean_obj_tag(v___x_5516_) == 0 {
                    v_a_5517_ = crate::leanh::lean_ctor_get(v___x_5516_, 0);
                    crate::leanh::lean_inc(v_a_5517_);
                    crate::leanh::lean_dec_ref_known(v___x_5516_, 1);
                    v___x_5518_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc(v_fst_5366_);
                    v___x_5519_ = l_Lean_MVarId_apply(
                        v_fst_5366_,
                        v_a_5517_,
                        v_cfg_5292_,
                        v___x_5518_,
                        v_a_5296_,
                        v_a_5297_,
                        v_a_5298_,
                        v_a_5299_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5519_) == 0 {
                        v_a_5520_ = crate::leanh::lean_ctor_get(v___x_5519_, 0);
                        crate::leanh::lean_inc_n(v_a_5520_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_5519_, 1);
                        crate::leanh::lean_inc(v_a_5299_);
                        crate::leanh::lean_inc_ref(v_a_5298_);
                        crate::leanh::lean_inc(v_a_5297_);
                        crate::leanh::lean_inc_ref(v_a_5296_);
                        v___x_5521_ = crate::leanh::lean_apply_6(
                            v_act_5293_,
                            v_a_5520_,
                            v_a_5296_,
                            v_a_5297_,
                            v_a_5298_,
                            v_a_5299_,
                            crate::leanh::lean_box(0),
                        );
                        if crate::leanh::lean_obj_tag(v___x_5521_) == 0 {
                            crate::leanh::lean_dec(v_a_5520_);
                            crate::leanh::lean_dec(v_fst_5366_);
                            crate::leanh::lean_dec_ref(v_allowFailure_5294_);
                            v_a_5522_ = crate::leanh::lean_ctor_get(v___x_5521_, 0);
                            crate::leanh::lean_inc(v_a_5522_);
                            crate::leanh::lean_dec_ref_known(v___x_5521_, 1);
                            v___y_5444_ = v_a_5473_;
                            v___y_5445_ = v___x_5503_;
                            v_a_5446_ = v_a_5522_;
                            state = 22;
                            continue;
                        } else {
                            v_a_5523_ = crate::leanh::lean_ctor_get(v___x_5521_, 0);
                            crate::leanh::lean_inc(v_a_5523_);
                            crate::leanh::lean_dec_ref_known(v___x_5521_, 1);
                            v___x_5524_ = l_Lean_Exception_isInterrupt(v_a_5523_);
                            if v___x_5524_ == 0 {
                                crate::leanh::lean_inc(v_a_5523_);
                                v___x_5525_ = l_Lean_Exception_isRuntime(v_a_5523_);
                                v___y_5460_ = v_a_5520_;
                                v___y_5461_ = v_a_5473_;
                                v___y_5462_ = v___x_5503_;
                                v___y_5463_ = v_a_5523_;
                                v___y_5464_ = v___x_5525_;
                                state = 25;
                                continue;
                            } else {
                                v___y_5460_ = v_a_5520_;
                                v___y_5461_ = v_a_5473_;
                                v___y_5462_ = v___x_5503_;
                                v___y_5463_ = v_a_5523_;
                                v___y_5464_ = v___x_5524_;
                                state = 25;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_fst_5366_);
                        crate::leanh::lean_dec_ref(v_allowFailure_5294_);
                        crate::leanh::lean_dec_ref(v_act_5293_);
                        v___y_5454_ = v_a_5473_;
                        v___y_5455_ = v___x_5503_;
                        v___y_5456_ = v___x_5519_;
                        state = 24;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_fst_5366_);
                    crate::leanh::lean_dec_ref(v_allowFailure_5294_);
                    crate::leanh::lean_dec_ref(v_act_5293_);
                    crate::leanh::lean_dec_ref(v_cfg_5292_);
                    v_a_5526_ = crate::leanh::lean_ctor_get(v___x_5516_, 0);
                    crate::leanh::lean_inc(v_a_5526_);
                    crate::leanh::lean_dec_ref_known(v___x_5516_, 1);
                    v___y_5449_ = v_a_5473_;
                    v___y_5450_ = v___x_5503_;
                    v_a_5451_ = v_a_5526_;
                    state = 23;
                    continue;
                }
            }
            31 => {
                if v_isShared_5539_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5538_, 0, v_snd_5367_);
                    v___x_5541_ = v___x_5538_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_5583_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5583_, 0, v_snd_5367_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5583_, 1, v_cache_5533_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5583_,
                        2,
                        v_zetaDeltaFVarIds_5534_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5583_, 3, v_postponed_5535_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5583_, 4, v_diag_5536_);
                    v___x_5541_ = v_reuseFailAlloc_5583_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                v___x_5542_ = lean_st_ref_set(v_a_5297_, v___x_5541_);
                v___x_5543_ = (crate::leanh::lean_unbox(v_snd_5372_) as u8);
                crate::leanh::lean_dec(v_snd_5372_);
                v___x_5544_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma(
                    v_fst_5371_,
                    v___x_5543_,
                    v_a_5296_,
                    v_a_5297_,
                    v_a_5298_,
                    v_a_5299_,
                );
                if crate::leanh::lean_obj_tag(v___x_5544_) == 0 {
                    v_a_5545_ = crate::leanh::lean_ctor_get(v___x_5544_, 0);
                    crate::leanh::lean_inc(v_a_5545_);
                    crate::leanh::lean_dec_ref_known(v___x_5544_, 1);
                    v___x_5546_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc(v_fst_5366_);
                    v___x_5547_ = l_Lean_MVarId_apply(
                        v_fst_5366_,
                        v_a_5545_,
                        v_cfg_5292_,
                        v___x_5546_,
                        v_a_5296_,
                        v_a_5297_,
                        v_a_5298_,
                        v_a_5299_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5547_) == 0 {
                        v_a_5548_ = crate::leanh::lean_ctor_get(v___x_5547_, 0);
                        crate::leanh::lean_inc_n(v_a_5548_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_5547_, 1);
                        crate::leanh::lean_inc(v_a_5299_);
                        crate::leanh::lean_inc_ref(v_a_5298_);
                        crate::leanh::lean_inc(v_a_5297_);
                        crate::leanh::lean_inc_ref(v_a_5296_);
                        v___x_5549_ = crate::leanh::lean_apply_6(
                            v_act_5293_,
                            v_a_5548_,
                            v_a_5296_,
                            v_a_5297_,
                            v_a_5298_,
                            v_a_5299_,
                            crate::leanh::lean_box(0),
                        );
                        if crate::leanh::lean_obj_tag(v___x_5549_) == 0 {
                            crate::leanh::lean_dec(v_a_5548_);
                            crate::leanh::lean_dec(v_fst_5366_);
                            crate::leanh::lean_dec_ref(v_allowFailure_5294_);
                            return v___x_5549_;
                        } else {
                            v_a_5550_ = crate::leanh::lean_ctor_get(v___x_5549_, 0);
                            crate::leanh::lean_inc(v_a_5550_);
                            v___x_5573_ = l_Lean_Exception_isInterrupt(v_a_5550_);
                            if v___x_5573_ == 0 {
                                v___x_5574_ = l_Lean_Exception_isRuntime(v_a_5550_);
                                v___y_5552_ = v___x_5574_;
                                state = 33;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_a_5550_);
                                v___y_5552_ = v___x_5573_;
                                state = 33;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_fst_5366_);
                        crate::leanh::lean_dec_ref(v_allowFailure_5294_);
                        crate::leanh::lean_dec_ref(v_act_5293_);
                        return v___x_5547_;
                    }
                } else {
                    crate::leanh::lean_dec(v_fst_5366_);
                    crate::leanh::lean_dec_ref(v_allowFailure_5294_);
                    crate::leanh::lean_dec_ref(v_act_5293_);
                    crate::leanh::lean_dec_ref(v_cfg_5292_);
                    v_a_5575_ = crate::leanh::lean_ctor_get(v___x_5544_, 0);
                    v_isSharedCheck_5582_ = (!crate::leanh::lean_is_exclusive(v___x_5544_)) as u8;
                    if v_isSharedCheck_5582_ == 0 {
                        v___x_5577_ = v___x_5544_;
                        v_isShared_5578_ = v_isSharedCheck_5582_;
                        state = 38;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5575_);
                        crate::leanh::lean_dec(v___x_5544_);
                        v___x_5577_ = crate::leanh::lean_box(0);
                        v_isShared_5578_ = v_isSharedCheck_5582_;
                        state = 38;
                        continue;
                    }
                }
            }
            33 => {
                if v___y_5552_ == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_5549_, 1);
                    crate::leanh::lean_inc(v_a_5299_);
                    crate::leanh::lean_inc_ref(v_a_5298_);
                    crate::leanh::lean_inc(v_a_5297_);
                    crate::leanh::lean_inc_ref(v_a_5296_);
                    v___x_5553_ = crate::leanh::lean_apply_6(
                        v_allowFailure_5294_,
                        v_fst_5366_,
                        v_a_5296_,
                        v_a_5297_,
                        v_a_5298_,
                        v_a_5299_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_5553_) == 0 {
                        v_a_5554_ = crate::leanh::lean_ctor_get(v___x_5553_, 0);
                        v_isSharedCheck_5564_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5553_)) as u8;
                        if v_isSharedCheck_5564_ == 0 {
                            v___x_5556_ = v___x_5553_;
                            v_isShared_5557_ = v_isSharedCheck_5564_;
                            state = 34;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5554_);
                            crate::leanh::lean_dec(v___x_5553_);
                            v___x_5556_ = crate::leanh::lean_box(0);
                            v_isShared_5557_ = v_isSharedCheck_5564_;
                            state = 34;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_5548_);
                        v_a_5565_ = crate::leanh::lean_ctor_get(v___x_5553_, 0);
                        v_isSharedCheck_5572_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5553_)) as u8;
                        if v_isSharedCheck_5572_ == 0 {
                            v___x_5567_ = v___x_5553_;
                            v_isShared_5568_ = v_isSharedCheck_5572_;
                            state = 36;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5565_);
                            crate::leanh::lean_dec(v___x_5553_);
                            v___x_5567_ = crate::leanh::lean_box(0);
                            v_isShared_5568_ = v_isSharedCheck_5572_;
                            state = 36;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_5548_);
                    crate::leanh::lean_dec(v_fst_5366_);
                    crate::leanh::lean_dec_ref(v_allowFailure_5294_);
                    return v___x_5549_;
                }
            }
            34 => {
                v___x_5558_ = (crate::leanh::lean_unbox(v_a_5554_) as u8);
                crate::leanh::lean_dec(v_a_5554_);
                if v___x_5558_ == 0 {
                    crate::leanh::lean_del_object(v___x_5556_);
                    crate::leanh::lean_dec(v_a_5548_);
                    v___x_5559_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1_once
                        ),
                        _init_l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1,
                    );
                    v___x_5560_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(v___x_5559_, v_a_5296_, v_a_5297_, v_a_5298_, v_a_5299_);
                    return v___x_5560_;
                } else {
                    if v_isShared_5557_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5556_, 0, v_a_5548_);
                        v___x_5562_ = v___x_5556_;
                        state = 35;
                        continue;
                    } else {
                        v_reuseFailAlloc_5563_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5563_, 0, v_a_5548_);
                        v___x_5562_ = v_reuseFailAlloc_5563_;
                        state = 35;
                        continue;
                    }
                }
            }
            35 => {
                return v___x_5562_;
            }
            36 => {
                if v_isShared_5568_ == 0 {
                    v___x_5570_ = v___x_5567_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_5571_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5571_, 0, v_a_5565_);
                    v___x_5570_ = v_reuseFailAlloc_5571_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_5570_;
            }
            38 => {
                if v_isShared_5578_ == 0 {
                    v___x_5580_ = v___x_5577_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_5581_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5581_, 0, v_a_5575_);
                    v___x_5580_ = v_reuseFailAlloc_5581_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                return v___x_5580_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___boxed(
    mut v_cfg_5589_: *mut crate::leanh::LeanObject,
    mut v_act_5590_: *mut crate::leanh::LeanObject,
    mut v_allowFailure_5591_: *mut crate::leanh::LeanObject,
    mut v_cand_5592_: *mut crate::leanh::LeanObject,
    mut v_a_5593_: *mut crate::leanh::LeanObject,
    mut v_a_5594_: *mut crate::leanh::LeanObject,
    mut v_a_5595_: *mut crate::leanh::LeanObject,
    mut v_a_5596_: *mut crate::leanh::LeanObject,
    mut v_a_5597_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5598_ =
        l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma(
            v_cfg_5589_,
            v_act_5590_,
            v_allowFailure_5591_,
            v_cand_5592_,
            v_a_5593_,
            v_a_5594_,
            v_a_5595_,
            v_a_5596_,
        );
    crate::leanh::lean_dec(v_a_5596_);
    crate::leanh::lean_dec_ref(v_a_5595_);
    crate::leanh::lean_dec(v_a_5594_);
    crate::leanh::lean_dec_ref(v_a_5593_);
    return v_res_5598_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__4(
    mut v_00_u03b1_5599_: *mut crate::leanh::LeanObject,
    mut v_x_5600_: *mut crate::leanh::LeanObject,
    mut v___y_5601_: *mut crate::leanh::LeanObject,
    mut v___y_5602_: *mut crate::leanh::LeanObject,
    mut v___y_5603_: *mut crate::leanh::LeanObject,
    mut v___y_5604_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5606_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__4___redArg(v_x_5600_);
    return v___x_5606_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__4___boxed(
    mut v_00_u03b1_5607_: *mut crate::leanh::LeanObject,
    mut v_x_5608_: *mut crate::leanh::LeanObject,
    mut v___y_5609_: *mut crate::leanh::LeanObject,
    mut v___y_5610_: *mut crate::leanh::LeanObject,
    mut v___y_5611_: *mut crate::leanh::LeanObject,
    mut v___y_5612_: *mut crate::leanh::LeanObject,
    mut v___y_5613_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5614_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__4(v_00_u03b1_5607_, v_x_5608_, v___y_5609_, v___y_5610_, v___y_5611_, v___y_5612_);
    crate::leanh::lean_dec(v___y_5612_);
    crate::leanh::lean_dec_ref(v___y_5611_);
    crate::leanh::lean_dec(v___y_5610_);
    crate::leanh::lean_dec_ref(v___y_5609_);
    return v_res_5614_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LibrarySearch_tryOnEach_spec__0(
    mut v_act_5617_: *mut crate::leanh::LeanObject,
    mut v_a_5618_: *mut crate::leanh::LeanObject,
    mut v_collectAll_5619_: u8,
    mut v_as_5620_: *mut crate::leanh::LeanObject,
    mut v_sz_5621_: usize,
    mut v_i_5622_: usize,
    mut v_b_5623_: *mut crate::leanh::LeanObject,
    mut v___y_5624_: *mut crate::leanh::LeanObject,
    mut v___y_5625_: *mut crate::leanh::LeanObject,
    mut v___y_5626_: *mut crate::leanh::LeanObject,
    mut v___y_5627_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_5630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5631_: usize = 0;
    let mut v___x_5632_: usize = 0;
    let mut v___x_5634_: u8 = 0;
    let mut v___x_5635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5639_: u8 = 0;
    let mut v___x_5640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5646_: u8 = 0;
    let mut v___x_5648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_5650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5659_: u8 = 0;
    let mut v___x_5661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5663_: u8 = 0;
    let mut v___y_5665_: u8 = 0;
    let mut v___x_5666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5671_: u8 = 0;
    let mut v_isSharedCheck_5672_: u8 = 0;
    let mut v_a_5673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5676_: u8 = 0;
    let mut v___y_5678_: u8 = 0;
    let mut v___x_5679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5682_: u8 = 0;
    let mut v___x_5683_: u8 = 0;
    let mut v___x_5685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5693_: u8 = 0;
    let mut v_unused_5694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5698_: u8 = 0;
    let mut v___x_5700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5702_: u8 = 0;
    let mut v___x_5704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5706_: u8 = 0;
    let mut v___x_5707_: u8 = 0;
    let mut v_isSharedCheck_5708_: u8 = 0;
    let mut v_isSharedCheck_5709_: u8 = 0;
    let mut v_unused_5710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5634_ = lean_usize_dec_lt(v_i_5622_, v_sz_5621_);
                if v___x_5634_ == 0 {
                    crate::leanh::lean_dec_ref(v_act_5617_);
                    v___x_5635_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5635_, 0, v_b_5623_);
                    return v___x_5635_;
                } else {
                    v_snd_5636_ = crate::leanh::lean_ctor_get(v_b_5623_, 1);
                    v_isSharedCheck_5709_ = (!crate::leanh::lean_is_exclusive(v_b_5623_)) as u8;
                    if v_isSharedCheck_5709_ == 0 {
                        v_unused_5710_ = crate::leanh::lean_ctor_get(v_b_5623_, 0);
                        crate::leanh::lean_dec(v_unused_5710_);
                        v___x_5638_ = v_b_5623_;
                        v_isShared_5639_ = v_isSharedCheck_5709_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_5636_);
                        crate::leanh::lean_dec(v_b_5623_);
                        v___x_5638_ = crate::leanh::lean_box(0);
                        v_isShared_5639_ = v_isSharedCheck_5709_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5631_ = 1usize;
                v___x_5632_ = lean_usize_add(v_i_5622_, v___x_5631_);
                v_i_5622_ = v___x_5632_;
                v_b_5623_ = v_a_5630_;
                state = 0;
                continue;
            }
            2 => {
                v___x_5640_ = crate::leanh::lean_box(0);
                v_a_5641_ = lean_array_uget_borrowed(v_as_5620_, v_i_5622_);
                crate::leanh::lean_inc_ref(v_act_5617_);
                crate::leanh::lean_inc(v___y_5627_);
                crate::leanh::lean_inc_ref(v___y_5626_);
                crate::leanh::lean_inc(v___y_5625_);
                crate::leanh::lean_inc_ref(v___y_5624_);
                crate::leanh::lean_inc(v_a_5641_);
                v___x_5642_ = crate::leanh::lean_apply_6(
                    v_act_5617_,
                    v_a_5641_,
                    v___y_5624_,
                    v___y_5625_,
                    v___y_5626_,
                    v___y_5627_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_5642_) == 0 {
                    v_a_5643_ = crate::leanh::lean_ctor_get(v___x_5642_, 0);
                    v_isSharedCheck_5672_ = (!crate::leanh::lean_is_exclusive(v___x_5642_)) as u8;
                    if v_isSharedCheck_5672_ == 0 {
                        v___x_5645_ = v___x_5642_;
                        v_isShared_5646_ = v_isSharedCheck_5672_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5643_);
                        crate::leanh::lean_dec(v___x_5642_);
                        v___x_5645_ = crate::leanh::lean_box(0);
                        v_isShared_5646_ = v_isSharedCheck_5672_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_5673_ = crate::leanh::lean_ctor_get(v___x_5642_, 0);
                    v_isSharedCheck_5708_ = (!crate::leanh::lean_is_exclusive(v___x_5642_)) as u8;
                    if v_isSharedCheck_5708_ == 0 {
                        v___x_5675_ = v___x_5642_;
                        v_isShared_5676_ = v_isSharedCheck_5708_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5673_);
                        crate::leanh::lean_dec(v___x_5642_);
                        v___x_5675_ = crate::leanh::lean_box(0);
                        v_isShared_5676_ = v_isSharedCheck_5708_;
                        state = 10;
                        continue;
                    }
                }
            }
            3 => {
                v___x_5671_ = l_List_isEmpty___redArg(v_a_5643_);
                if v___x_5671_ == 0 {
                    v___y_5665_ = v___x_5671_;
                    state = 8;
                    continue;
                } else {
                    if v_collectAll_5619_ == 0 {
                        v___y_5665_ = v___x_5671_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_del_object(v___x_5645_);
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                v___x_5648_ = lean_st_ref_get(v___y_5625_);
                v___x_5649_ =
                    l_Lean_Meta_SavedState_restore___redArg(v_a_5618_, v___y_5625_, v___y_5627_);
                if crate::leanh::lean_obj_tag(v___x_5649_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_5649_, 1);
                    v_mctx_5650_ = crate::leanh::lean_ctor_get(v___x_5648_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_5650_);
                    crate::leanh::lean_dec(v___x_5648_);
                    if v_isShared_5639_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5638_, 1, v_mctx_5650_);
                        crate::leanh::lean_ctor_set(v___x_5638_, 0, v_a_5643_);
                        v___x_5652_ = v___x_5638_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5655_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5655_, 0, v_a_5643_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5655_, 1, v_mctx_5650_);
                        v___x_5652_ = v_reuseFailAlloc_5655_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5648_);
                    crate::leanh::lean_dec(v_a_5643_);
                    crate::leanh::lean_del_object(v___x_5638_);
                    crate::leanh::lean_dec(v_snd_5636_);
                    crate::leanh::lean_dec_ref(v_act_5617_);
                    v_a_5656_ = crate::leanh::lean_ctor_get(v___x_5649_, 0);
                    v_isSharedCheck_5663_ = (!crate::leanh::lean_is_exclusive(v___x_5649_)) as u8;
                    if v_isSharedCheck_5663_ == 0 {
                        v___x_5658_ = v___x_5649_;
                        v_isShared_5659_ = v_isSharedCheck_5663_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5656_);
                        crate::leanh::lean_dec(v___x_5649_);
                        v___x_5658_ = crate::leanh::lean_box(0);
                        v_isShared_5659_ = v_isSharedCheck_5663_;
                        state = 6;
                        continue;
                    }
                }
            }
            5 => {
                v___x_5653_ = lean_array_push(v_snd_5636_, v___x_5652_);
                v___x_5654_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5654_, 0, v___x_5640_);
                crate::leanh::lean_ctor_set(v___x_5654_, 1, v___x_5653_);
                v_a_5630_ = v___x_5654_;
                state = 1;
                continue;
            }
            6 => {
                if v_isShared_5659_ == 0 {
                    v___x_5661_ = v___x_5658_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5662_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5662_, 0, v_a_5656_);
                    v___x_5661_ = v_reuseFailAlloc_5662_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5661_;
            }
            8 => {
                if v___y_5665_ == 0 {
                    crate::leanh::lean_del_object(v___x_5645_);
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_a_5643_);
                    crate::leanh::lean_del_object(v___x_5638_);
                    crate::leanh::lean_dec_ref(v_act_5617_);
                    v___x_5666_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LibrarySearch_tryOnEach_spec__0___closed__0;
                    v___x_5667_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5667_, 0, v___x_5666_);
                    crate::leanh::lean_ctor_set(v___x_5667_, 1, v_snd_5636_);
                    if v_isShared_5646_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5645_, 0, v___x_5667_);
                        v___x_5669_ = v___x_5645_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_5670_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5670_, 0, v___x_5667_);
                        v___x_5669_ = v_reuseFailAlloc_5670_;
                        state = 9;
                        continue;
                    }
                }
            }
            9 => {
                return v___x_5669_;
            }
            10 => {
                v___x_5706_ = l_Lean_Exception_isInterrupt(v_a_5673_);
                if v___x_5706_ == 0 {
                    crate::leanh::lean_inc(v_a_5673_);
                    v___x_5707_ = l_Lean_Exception_isRuntime(v_a_5673_);
                    v___y_5678_ = v___x_5707_;
                    state = 11;
                    continue;
                } else {
                    v___y_5678_ = v___x_5706_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v___y_5678_ == 0 {
                    crate::leanh::lean_del_object(v___x_5675_);
                    v___x_5679_ = l_Lean_Meta_SavedState_restore___redArg(
                        v_a_5618_,
                        v___y_5625_,
                        v___y_5627_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5679_) == 0 {
                        v_isSharedCheck_5693_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5679_)) as u8;
                        if v_isSharedCheck_5693_ == 0 {
                            v_unused_5694_ = crate::leanh::lean_ctor_get(v___x_5679_, 0);
                            crate::leanh::lean_dec(v_unused_5694_);
                            v___x_5681_ = v___x_5679_;
                            v_isShared_5682_ = v_isSharedCheck_5693_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_5679_);
                            v___x_5681_ = crate::leanh::lean_box(0);
                            v_isShared_5682_ = v_isSharedCheck_5693_;
                            state = 12;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_5673_);
                        crate::leanh::lean_del_object(v___x_5638_);
                        crate::leanh::lean_dec(v_snd_5636_);
                        crate::leanh::lean_dec_ref(v_act_5617_);
                        v_a_5695_ = crate::leanh::lean_ctor_get(v___x_5679_, 0);
                        v_isSharedCheck_5702_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5679_)) as u8;
                        if v_isSharedCheck_5702_ == 0 {
                            v___x_5697_ = v___x_5679_;
                            v_isShared_5698_ = v_isSharedCheck_5702_;
                            state = 16;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5695_);
                            crate::leanh::lean_dec(v___x_5679_);
                            v___x_5697_ = crate::leanh::lean_box(0);
                            v_isShared_5698_ = v_isSharedCheck_5702_;
                            state = 16;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5638_);
                    crate::leanh::lean_dec(v_snd_5636_);
                    crate::leanh::lean_dec_ref(v_act_5617_);
                    if v_isShared_5676_ == 0 {
                        v___x_5704_ = v___x_5675_;
                        state = 18;
                        continue;
                    } else {
                        v_reuseFailAlloc_5705_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5705_, 0, v_a_5673_);
                        v___x_5704_ = v_reuseFailAlloc_5705_;
                        state = 18;
                        continue;
                    }
                }
            }
            12 => {
                v___x_5683_ = l_Lean_Meta_LibrarySearch_isAbortSpeculation(v_a_5673_);
                crate::leanh::lean_dec(v_a_5673_);
                if v___x_5683_ == 0 {
                    crate::leanh::lean_del_object(v___x_5681_);
                    if v_isShared_5639_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5638_, 0, v___x_5640_);
                        v___x_5685_ = v___x_5638_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_5686_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5686_, 0, v___x_5640_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5686_, 1, v_snd_5636_);
                        v___x_5685_ = v_reuseFailAlloc_5686_;
                        state = 13;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_act_5617_);
                    if v_isShared_5639_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5638_, 0, v___x_5640_);
                        v___x_5688_ = v___x_5638_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_5692_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5692_, 0, v___x_5640_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5692_, 1, v_snd_5636_);
                        v___x_5688_ = v_reuseFailAlloc_5692_;
                        state = 14;
                        continue;
                    }
                }
            }
            13 => {
                v_a_5630_ = v___x_5685_;
                state = 1;
                continue;
            }
            14 => {
                if v_isShared_5682_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5681_, 0, v___x_5688_);
                    v___x_5690_ = v___x_5681_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_5691_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5691_, 0, v___x_5688_);
                    v___x_5690_ = v_reuseFailAlloc_5691_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_5690_;
            }
            16 => {
                if v_isShared_5698_ == 0 {
                    v___x_5700_ = v___x_5697_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_5701_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5701_, 0, v_a_5695_);
                    v___x_5700_ = v_reuseFailAlloc_5701_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_5700_;
            }
            18 => {
                return v___x_5704_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LibrarySearch_tryOnEach_spec__0___boxed(
    mut v_act_5711_: *mut crate::leanh::LeanObject,
    mut v_a_5712_: *mut crate::leanh::LeanObject,
    mut v_collectAll_5713_: *mut crate::leanh::LeanObject,
    mut v_as_5714_: *mut crate::leanh::LeanObject,
    mut v_sz_5715_: *mut crate::leanh::LeanObject,
    mut v_i_5716_: *mut crate::leanh::LeanObject,
    mut v_b_5717_: *mut crate::leanh::LeanObject,
    mut v___y_5718_: *mut crate::leanh::LeanObject,
    mut v___y_5719_: *mut crate::leanh::LeanObject,
    mut v___y_5720_: *mut crate::leanh::LeanObject,
    mut v___y_5721_: *mut crate::leanh::LeanObject,
    mut v___y_5722_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_collectAll_boxed_5723_: u8 = 0;
    let mut v_sz_boxed_5724_: usize = 0;
    let mut v_i_boxed_5725_: usize = 0;
    let mut v_res_5726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_collectAll_boxed_5723_ = (crate::leanh::lean_unbox(v_collectAll_5713_) as u8);
    v_sz_boxed_5724_ = crate::leanh::lean_unbox_usize(v_sz_5715_);
    crate::leanh::lean_dec(v_sz_5715_);
    v_i_boxed_5725_ = crate::leanh::lean_unbox_usize(v_i_5716_);
    crate::leanh::lean_dec(v_i_5716_);
    v_res_5726_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LibrarySearch_tryOnEach_spec__0(v_act_5711_, v_a_5712_, v_collectAll_boxed_5723_, v_as_5714_, v_sz_boxed_5724_, v_i_boxed_5725_, v_b_5717_, v___y_5718_, v___y_5719_, v___y_5720_, v___y_5721_);
    crate::leanh::lean_dec(v___y_5721_);
    crate::leanh::lean_dec_ref(v___y_5720_);
    crate::leanh::lean_dec(v___y_5719_);
    crate::leanh::lean_dec_ref(v___y_5718_);
    crate::leanh::lean_dec_ref(v_as_5714_);
    crate::leanh::lean_dec_ref(v_a_5712_);
    return v_res_5726_;
}
pub unsafe fn l_Lean_Meta_LibrarySearch_tryOnEach(
    mut v_act_5732_: *mut crate::leanh::LeanObject,
    mut v_candidates_5733_: *mut crate::leanh::LeanObject,
    mut v_collectAll_5734_: u8,
    mut v_a_5735_: *mut crate::leanh::LeanObject,
    mut v_a_5736_: *mut crate::leanh::LeanObject,
    mut v_a_5737_: *mut crate::leanh::LeanObject,
    mut v_a_5738_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5743_: usize = 0;
    let mut v___x_5744_: usize = 0;
    let mut v___x_5745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5749_: u8 = 0;
    let mut v_fst_5750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5760_: u8 = 0;
    let mut v_a_5761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5764_: u8 = 0;
    let mut v___x_5766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5768_: u8 = 0;
    let mut v_a_5769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5772_: u8 = 0;
    let mut v___x_5774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5776_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5740_ = l_Lean_Meta_saveState___redArg(v_a_5736_, v_a_5738_);
                if crate::leanh::lean_obj_tag(v___x_5740_) == 0 {
                    v_a_5741_ = crate::leanh::lean_ctor_get(v___x_5740_, 0);
                    crate::leanh::lean_inc(v_a_5741_);
                    crate::leanh::lean_dec_ref_known(v___x_5740_, 1);
                    v___x_5742_ = l_Lean_Meta_LibrarySearch_tryOnEach___closed__1;
                    v_sz_5743_ = lean_array_size(v_candidates_5733_);
                    v___x_5744_ = 0usize;
                    v___x_5745_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LibrarySearch_tryOnEach_spec__0(v_act_5732_, v_a_5741_, v_collectAll_5734_, v_candidates_5733_, v_sz_5743_, v___x_5744_, v___x_5742_, v_a_5735_, v_a_5736_, v_a_5737_, v_a_5738_);
                    crate::leanh::lean_dec(v_a_5741_);
                    if crate::leanh::lean_obj_tag(v___x_5745_) == 0 {
                        v_a_5746_ = crate::leanh::lean_ctor_get(v___x_5745_, 0);
                        v_isSharedCheck_5760_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5745_)) as u8;
                        if v_isSharedCheck_5760_ == 0 {
                            v___x_5748_ = v___x_5745_;
                            v_isShared_5749_ = v_isSharedCheck_5760_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5746_);
                            crate::leanh::lean_dec(v___x_5745_);
                            v___x_5748_ = crate::leanh::lean_box(0);
                            v_isShared_5749_ = v_isSharedCheck_5760_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_5761_ = crate::leanh::lean_ctor_get(v___x_5745_, 0);
                        v_isSharedCheck_5768_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5745_)) as u8;
                        if v_isSharedCheck_5768_ == 0 {
                            v___x_5763_ = v___x_5745_;
                            v_isShared_5764_ = v_isSharedCheck_5768_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5761_);
                            crate::leanh::lean_dec(v___x_5745_);
                            v___x_5763_ = crate::leanh::lean_box(0);
                            v_isShared_5764_ = v_isSharedCheck_5768_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_act_5732_);
                    v_a_5769_ = crate::leanh::lean_ctor_get(v___x_5740_, 0);
                    v_isSharedCheck_5776_ = (!crate::leanh::lean_is_exclusive(v___x_5740_)) as u8;
                    if v_isSharedCheck_5776_ == 0 {
                        v___x_5771_ = v___x_5740_;
                        v_isShared_5772_ = v_isSharedCheck_5776_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5769_);
                        crate::leanh::lean_dec(v___x_5740_);
                        v___x_5771_ = crate::leanh::lean_box(0);
                        v_isShared_5772_ = v_isSharedCheck_5776_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_5750_ = crate::leanh::lean_ctor_get(v_a_5746_, 0);
                if crate::leanh::lean_obj_tag(v_fst_5750_) == 0 {
                    v_snd_5751_ = crate::leanh::lean_ctor_get(v_a_5746_, 1);
                    crate::leanh::lean_inc(v_snd_5751_);
                    crate::leanh::lean_dec(v_a_5746_);
                    v___x_5752_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5752_, 0, v_snd_5751_);
                    if v_isShared_5749_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5748_, 0, v___x_5752_);
                        v___x_5754_ = v___x_5748_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5755_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5755_, 0, v___x_5752_);
                        v___x_5754_ = v_reuseFailAlloc_5755_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_5750_);
                    crate::leanh::lean_dec(v_a_5746_);
                    v_val_5756_ = crate::leanh::lean_ctor_get(v_fst_5750_, 0);
                    crate::leanh::lean_inc(v_val_5756_);
                    crate::leanh::lean_dec_ref_known(v_fst_5750_, 1);
                    if v_isShared_5749_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5748_, 0, v_val_5756_);
                        v___x_5758_ = v___x_5748_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5759_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5759_, 0, v_val_5756_);
                        v___x_5758_ = v_reuseFailAlloc_5759_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5754_;
            }
            3 => {
                return v___x_5758_;
            }
            4 => {
                if v_isShared_5764_ == 0 {
                    v___x_5766_ = v___x_5763_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5767_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5767_, 0, v_a_5761_);
                    v___x_5766_ = v_reuseFailAlloc_5767_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5766_;
            }
            6 => {
                if v_isShared_5772_ == 0 {
                    v___x_5774_ = v___x_5771_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5775_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5775_, 0, v_a_5769_);
                    v___x_5774_ = v_reuseFailAlloc_5775_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5774_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_LibrarySearch_tryOnEach___boxed(
    mut v_act_5777_: *mut crate::leanh::LeanObject,
    mut v_candidates_5778_: *mut crate::leanh::LeanObject,
    mut v_collectAll_5779_: *mut crate::leanh::LeanObject,
    mut v_a_5780_: *mut crate::leanh::LeanObject,
    mut v_a_5781_: *mut crate::leanh::LeanObject,
    mut v_a_5782_: *mut crate::leanh::LeanObject,
    mut v_a_5783_: *mut crate::leanh::LeanObject,
    mut v_a_5784_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_collectAll_boxed_5785_: u8 = 0;
    let mut v_res_5786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_collectAll_boxed_5785_ = (crate::leanh::lean_unbox(v_collectAll_5779_) as u8);
    v_res_5786_ = l_Lean_Meta_LibrarySearch_tryOnEach(
        v_act_5777_,
        v_candidates_5778_,
        v_collectAll_boxed_5785_,
        v_a_5780_,
        v_a_5781_,
        v_a_5782_,
        v_a_5783_,
    );
    crate::leanh::lean_dec(v_a_5783_);
    crate::leanh::lean_dec_ref(v_a_5782_);
    crate::leanh::lean_dec(v_a_5781_);
    crate::leanh::lean_dec_ref(v_a_5780_);
    crate::leanh::lean_dec_ref(v_candidates_5778_);
    return v_res_5786_;
}
pub unsafe fn l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5788_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0_once
        ),
        _init_l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0,
    );
    v___x_5789_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5789_, 0, v___x_5788_);
    return v___x_5789_;
}
pub unsafe fn l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0___redArg___boxed(
    mut v___y_5790_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5791_ = l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0___redArg();
    return v_res_5791_;
}
pub unsafe fn l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0(
    mut v_00_u03b1_5792_: *mut crate::leanh::LeanObject,
    mut v___y_5793_: *mut crate::leanh::LeanObject,
    mut v___y_5794_: *mut crate::leanh::LeanObject,
    mut v___y_5795_: *mut crate::leanh::LeanObject,
    mut v___y_5796_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5798_ = l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0___redArg();
    return v___x_5798_;
}
pub unsafe fn l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0___boxed(
    mut v_00_u03b1_5799_: *mut crate::leanh::LeanObject,
    mut v___y_5800_: *mut crate::leanh::LeanObject,
    mut v___y_5801_: *mut crate::leanh::LeanObject,
    mut v___y_5802_: *mut crate::leanh::LeanObject,
    mut v___y_5803_: *mut crate::leanh::LeanObject,
    mut v___y_5804_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5805_ = l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0(v_00_u03b1_5799_, v___y_5800_, v___y_5801_, v___y_5802_, v___y_5803_);
    crate::leanh::lean_dec(v___y_5803_);
    crate::leanh::lean_dec_ref(v___y_5802_);
    crate::leanh::lean_dec(v___y_5801_);
    crate::leanh::lean_dec_ref(v___y_5800_);
    return v_res_5805_;
}
pub unsafe fn l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(
    mut v_category_5806_: *mut crate::leanh::LeanObject,
    mut v_opts_5807_: *mut crate::leanh::LeanObject,
    mut v_act_5808_: *mut crate::leanh::LeanObject,
    mut v_decl_5809_: *mut crate::leanh::LeanObject,
    mut v___y_5810_: *mut crate::leanh::LeanObject,
    mut v___y_5811_: *mut crate::leanh::LeanObject,
    mut v___y_5812_: *mut crate::leanh::LeanObject,
    mut v___y_5813_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_5813_);
    crate::leanh::lean_inc_ref(v___y_5812_);
    crate::leanh::lean_inc(v___y_5811_);
    crate::leanh::lean_inc_ref(v___y_5810_);
    v___x_5815_ = crate::leanh::lean_apply_4(
        v_act_5808_,
        v___y_5810_,
        v___y_5811_,
        v___y_5812_,
        v___y_5813_,
    );
    v___x_5816_ = l_Lean_profileitIOUnsafe___redArg(
        v_category_5806_,
        v_opts_5807_,
        v___x_5815_,
        v_decl_5809_,
    );
    return v___x_5816_;
}
pub unsafe fn l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg___boxed(
    mut v_category_5817_: *mut crate::leanh::LeanObject,
    mut v_opts_5818_: *mut crate::leanh::LeanObject,
    mut v_act_5819_: *mut crate::leanh::LeanObject,
    mut v_decl_5820_: *mut crate::leanh::LeanObject,
    mut v___y_5821_: *mut crate::leanh::LeanObject,
    mut v___y_5822_: *mut crate::leanh::LeanObject,
    mut v___y_5823_: *mut crate::leanh::LeanObject,
    mut v___y_5824_: *mut crate::leanh::LeanObject,
    mut v___y_5825_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5826_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(v_category_5817_, v_opts_5818_, v_act_5819_, v_decl_5820_, v___y_5821_, v___y_5822_, v___y_5823_, v___y_5824_);
    crate::leanh::lean_dec(v___y_5824_);
    crate::leanh::lean_dec_ref(v___y_5823_);
    crate::leanh::lean_dec(v___y_5822_);
    crate::leanh::lean_dec_ref(v___y_5821_);
    crate::leanh::lean_dec_ref(v_opts_5818_);
    crate::leanh::lean_dec_ref(v_category_5817_);
    return v_res_5826_;
}
pub unsafe fn l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3(
    mut v_00_u03b1_5827_: *mut crate::leanh::LeanObject,
    mut v_category_5828_: *mut crate::leanh::LeanObject,
    mut v_opts_5829_: *mut crate::leanh::LeanObject,
    mut v_act_5830_: *mut crate::leanh::LeanObject,
    mut v_decl_5831_: *mut crate::leanh::LeanObject,
    mut v___y_5832_: *mut crate::leanh::LeanObject,
    mut v___y_5833_: *mut crate::leanh::LeanObject,
    mut v___y_5834_: *mut crate::leanh::LeanObject,
    mut v___y_5835_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5837_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(v_category_5828_, v_opts_5829_, v_act_5830_, v_decl_5831_, v___y_5832_, v___y_5833_, v___y_5834_, v___y_5835_);
    return v___x_5837_;
}
pub unsafe fn l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___boxed(
    mut v_00_u03b1_5838_: *mut crate::leanh::LeanObject,
    mut v_category_5839_: *mut crate::leanh::LeanObject,
    mut v_opts_5840_: *mut crate::leanh::LeanObject,
    mut v_act_5841_: *mut crate::leanh::LeanObject,
    mut v_decl_5842_: *mut crate::leanh::LeanObject,
    mut v___y_5843_: *mut crate::leanh::LeanObject,
    mut v___y_5844_: *mut crate::leanh::LeanObject,
    mut v___y_5845_: *mut crate::leanh::LeanObject,
    mut v___y_5846_: *mut crate::leanh::LeanObject,
    mut v___y_5847_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5848_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3(v_00_u03b1_5838_, v_category_5839_, v_opts_5840_, v_act_5841_, v_decl_5842_, v___y_5843_, v___y_5844_, v___y_5845_, v___y_5846_);
    crate::leanh::lean_dec(v___y_5846_);
    crate::leanh::lean_dec_ref(v___y_5845_);
    crate::leanh::lean_dec(v___y_5844_);
    crate::leanh::lean_dec_ref(v___y_5843_);
    crate::leanh::lean_dec_ref(v_opts_5840_);
    crate::leanh::lean_dec_ref(v_category_5839_);
    return v_res_5848_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__0(
    mut v_a_5849_: *mut crate::leanh::LeanObject,
    mut v___x_5850_: *mut crate::leanh::LeanObject,
    mut v_tactic_5851_: *mut crate::leanh::LeanObject,
    mut v_allowFailure_5852_: *mut crate::leanh::LeanObject,
    mut v_cand_5853_: *mut crate::leanh::LeanObject,
    mut v___y_5854_: *mut crate::leanh::LeanObject,
    mut v___y_5855_: *mut crate::leanh::LeanObject,
    mut v___y_5856_: *mut crate::leanh::LeanObject,
    mut v___y_5857_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5861_: u8 = 0;
    let mut v___x_5862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5867_: u8 = 0;
    let mut v___x_5869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5871_: u8 = 0;
    let mut v_a_5872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5875_: u8 = 0;
    let mut v___x_5877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5879_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_5857_);
                crate::leanh::lean_inc_ref(v___y_5856_);
                crate::leanh::lean_inc(v___y_5855_);
                crate::leanh::lean_inc_ref(v___y_5854_);
                v___x_5859_ = crate::leanh::lean_apply_5(
                    v_a_5849_,
                    v___y_5854_,
                    v___y_5855_,
                    v___y_5856_,
                    v___y_5857_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_5859_) == 0 {
                    v_a_5860_ = crate::leanh::lean_ctor_get(v___x_5859_, 0);
                    crate::leanh::lean_inc(v_a_5860_);
                    crate::leanh::lean_dec_ref_known(v___x_5859_, 1);
                    v___x_5861_ = (crate::leanh::lean_unbox(v_a_5860_) as u8);
                    crate::leanh::lean_dec(v_a_5860_);
                    if v___x_5861_ == 0 {
                        v___x_5862_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma(v___x_5850_, v_tactic_5851_, v_allowFailure_5852_, v_cand_5853_, v___y_5854_, v___y_5855_, v___y_5856_, v___y_5857_);
                        return v___x_5862_;
                    } else {
                        crate::leanh::lean_dec_ref(v_cand_5853_);
                        crate::leanh::lean_dec_ref(v_allowFailure_5852_);
                        crate::leanh::lean_dec_ref(v_tactic_5851_);
                        crate::leanh::lean_dec_ref(v___x_5850_);
                        v___x_5863_ = l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0___redArg();
                        v_a_5864_ = crate::leanh::lean_ctor_get(v___x_5863_, 0);
                        v_isSharedCheck_5871_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5863_)) as u8;
                        if v_isSharedCheck_5871_ == 0 {
                            v___x_5866_ = v___x_5863_;
                            v_isShared_5867_ = v_isSharedCheck_5871_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5864_);
                            crate::leanh::lean_dec(v___x_5863_);
                            v___x_5866_ = crate::leanh::lean_box(0);
                            v_isShared_5867_ = v_isSharedCheck_5871_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_cand_5853_);
                    crate::leanh::lean_dec_ref(v_allowFailure_5852_);
                    crate::leanh::lean_dec_ref(v_tactic_5851_);
                    crate::leanh::lean_dec_ref(v___x_5850_);
                    v_a_5872_ = crate::leanh::lean_ctor_get(v___x_5859_, 0);
                    v_isSharedCheck_5879_ = (!crate::leanh::lean_is_exclusive(v___x_5859_)) as u8;
                    if v_isSharedCheck_5879_ == 0 {
                        v___x_5874_ = v___x_5859_;
                        v_isShared_5875_ = v_isSharedCheck_5879_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5872_);
                        crate::leanh::lean_dec(v___x_5859_);
                        v___x_5874_ = crate::leanh::lean_box(0);
                        v_isShared_5875_ = v_isSharedCheck_5879_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5867_ == 0 {
                    v___x_5869_ = v___x_5866_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5870_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5870_, 0, v_a_5864_);
                    v___x_5869_ = v_reuseFailAlloc_5870_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5869_;
            }
            3 => {
                if v_isShared_5875_ == 0 {
                    v___x_5877_ = v___x_5874_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5878_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5878_, 0, v_a_5872_);
                    v___x_5877_ = v_reuseFailAlloc_5878_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5877_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__0___boxed(
    mut v_a_5880_: *mut crate::leanh::LeanObject,
    mut v___x_5881_: *mut crate::leanh::LeanObject,
    mut v_tactic_5882_: *mut crate::leanh::LeanObject,
    mut v_allowFailure_5883_: *mut crate::leanh::LeanObject,
    mut v_cand_5884_: *mut crate::leanh::LeanObject,
    mut v___y_5885_: *mut crate::leanh::LeanObject,
    mut v___y_5886_: *mut crate::leanh::LeanObject,
    mut v___y_5887_: *mut crate::leanh::LeanObject,
    mut v___y_5888_: *mut crate::leanh::LeanObject,
    mut v___y_5889_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5890_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__0(v_a_5880_, v___x_5881_, v_tactic_5882_, v_allowFailure_5883_, v_cand_5884_, v___y_5885_, v___y_5886_, v___y_5887_, v___y_5888_);
    crate::leanh::lean_dec(v___y_5888_);
    crate::leanh::lean_dec_ref(v___y_5887_);
    crate::leanh::lean_dec(v___y_5886_);
    crate::leanh::lean_dec_ref(v___y_5885_);
    return v_res_5890_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__2(
    mut v_as_5891_: *mut crate::leanh::LeanObject,
    mut v_i_5892_: usize,
    mut v_stop_5893_: usize,
) -> u8 {
    let mut v___x_5894_: u8 = 0;
    let mut v___x_5895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5897_: u8 = 0;
    let mut v___x_5898_: usize = 0;
    let mut v___x_5899_: usize = 0;
    let mut v___x_5901_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5894_ = lean_usize_dec_eq(v_i_5892_, v_stop_5893_);
                if v___x_5894_ == 0 {
                    v___x_5895_ = lean_array_uget_borrowed(v_as_5891_, v_i_5892_);
                    v_fst_5896_ = crate::leanh::lean_ctor_get(v___x_5895_, 0);
                    v___x_5897_ = l_List_isEmpty___redArg(v_fst_5896_);
                    if v___x_5897_ == 0 {
                        v___x_5898_ = 1usize;
                        v___x_5899_ = lean_usize_add(v_i_5892_, v___x_5898_);
                        v_i_5892_ = v___x_5899_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_5897_;
                    }
                } else {
                    v___x_5901_ = 0;
                    return v___x_5901_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__2___boxed(
    mut v_as_5902_: *mut crate::leanh::LeanObject,
    mut v_i_5903_: *mut crate::leanh::LeanObject,
    mut v_stop_5904_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_5905_: usize = 0;
    let mut v_stop_boxed_5906_: usize = 0;
    let mut v_res_5907_: u8 = 0;
    let mut v_r_5908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5905_ = crate::leanh::lean_unbox_usize(v_i_5903_);
    crate::leanh::lean_dec(v_i_5903_);
    v_stop_boxed_5906_ = crate::leanh::lean_unbox_usize(v_stop_5904_);
    crate::leanh::lean_dec(v_stop_5904_);
    v_res_5907_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__2(v_as_5902_, v_i_boxed_5905_, v_stop_boxed_5906_);
    crate::leanh::lean_dec_ref(v_as_5902_);
    v_r_5908_ = crate::leanh::lean_box((v_res_5907_) as usize);
    return v_r_5908_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1(
    mut v_goal_5909_: *mut crate::leanh::LeanObject,
    mut v___x_5910_: *mut crate::leanh::LeanObject,
    mut v_sz_5911_: usize,
    mut v_i_5912_: usize,
    mut v_bs_5913_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5914_: u8 = 0;
    let mut v_v_5915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5920_: usize = 0;
    let mut v___x_5921_: usize = 0;
    let mut v___x_5922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5914_ = lean_usize_dec_lt(v_i_5912_, v_sz_5911_);
                if v___x_5914_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_5910_);
                    crate::leanh::lean_dec(v_goal_5909_);
                    return v_bs_5913_;
                } else {
                    v_v_5915_ = lean_array_uget(v_bs_5913_, v_i_5912_);
                    v___x_5916_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_5917_ = lean_array_uset(v_bs_5913_, v_i_5912_, v___x_5916_);
                    crate::leanh::lean_inc_ref(v___x_5910_);
                    crate::leanh::lean_inc(v_goal_5909_);
                    v___x_5918_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5918_, 0, v_goal_5909_);
                    crate::leanh::lean_ctor_set(v___x_5918_, 1, v___x_5910_);
                    v___x_5919_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5919_, 0, v___x_5918_);
                    crate::leanh::lean_ctor_set(v___x_5919_, 1, v_v_5915_);
                    v___x_5920_ = 1usize;
                    v___x_5921_ = lean_usize_add(v_i_5912_, v___x_5920_);
                    v___x_5922_ = lean_array_uset(v_bs_x27_5917_, v_i_5912_, v___x_5919_);
                    v_i_5912_ = v___x_5921_;
                    v_bs_5913_ = v___x_5922_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1___boxed(
    mut v_goal_5924_: *mut crate::leanh::LeanObject,
    mut v___x_5925_: *mut crate::leanh::LeanObject,
    mut v_sz_5926_: *mut crate::leanh::LeanObject,
    mut v_i_5927_: *mut crate::leanh::LeanObject,
    mut v_bs_5928_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5929_: usize = 0;
    let mut v_i_boxed_5930_: usize = 0;
    let mut v_res_5931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5929_ = crate::leanh::lean_unbox_usize(v_sz_5926_);
    crate::leanh::lean_dec(v_sz_5926_);
    v_i_boxed_5930_ = crate::leanh::lean_unbox_usize(v_i_5927_);
    crate::leanh::lean_dec(v_i_5927_);
    v_res_5931_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1(v_goal_5924_, v___x_5925_, v_sz_boxed_5929_, v_i_boxed_5930_, v_bs_5928_);
    return v_res_5931_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1(
    mut v_leavePercentHeartbeats_5933_: *mut crate::leanh::LeanObject,
    mut v_goal_5934_: *mut crate::leanh::LeanObject,
    mut v___x_5935_: *mut crate::leanh::LeanObject,
    mut v_tactic_5936_: *mut crate::leanh::LeanObject,
    mut v_allowFailure_5937_: *mut crate::leanh::LeanObject,
    mut v_collectAll_5938_: u8,
    mut v_includeStar_5939_: u8,
    mut v___y_5940_: *mut crate::leanh::LeanObject,
    mut v___y_5941_: *mut crate::leanh::LeanObject,
    mut v___y_5942_: *mut crate::leanh::LeanObject,
    mut v___y_5943_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5962_: u8 = 0;
    let mut v___x_5963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5965_: u8 = 0;
    let mut v___x_5966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_5967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5968_: usize = 0;
    let mut v___x_5969_: usize = 0;
    let mut v___x_5970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5975_: u8 = 0;
    let mut v_val_5976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5979_: u8 = 0;
    let mut v___x_5980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5987_: u8 = 0;
    let mut v_isSharedCheck_5988_: u8 = 0;
    let mut v___x_5990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5992_: u8 = 0;
    let mut v_a_5993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5996_: u8 = 0;
    let mut v___x_5998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6000_: u8 = 0;
    let mut v___x_6002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6004_: u8 = 0;
    let mut v___x_6005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6007_: u8 = 0;
    let mut v___x_6008_: usize = 0;
    let mut v___x_6009_: usize = 0;
    let mut v___x_6010_: u8 = 0;
    let mut v_a_6011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6014_: u8 = 0;
    let mut v___x_6016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6018_: u8 = 0;
    let mut v_a_6019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6022_: u8 = 0;
    let mut v___x_6024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6026_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5948_ = l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg(
                    v_leavePercentHeartbeats_5933_,
                    v___y_5942_,
                );
                if crate::leanh::lean_obj_tag(v___x_5948_) == 0 {
                    v_a_5949_ = crate::leanh::lean_ctor_get(v___x_5948_, 0);
                    crate::leanh::lean_inc(v_a_5949_);
                    crate::leanh::lean_dec_ref_known(v___x_5948_, 1);
                    v___x_5950_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1___closed__0;
                    crate::leanh::lean_inc(v_goal_5934_);
                    v___x_5951_ = l_Lean_Meta_LibrarySearch_librarySearchSymm(
                        v___x_5950_,
                        v_goal_5934_,
                        v___y_5940_,
                        v___y_5941_,
                        v___y_5942_,
                        v___y_5943_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5951_) == 0 {
                        v_a_5952_ = crate::leanh::lean_ctor_get(v___x_5951_, 0);
                        crate::leanh::lean_inc(v_a_5952_);
                        crate::leanh::lean_dec_ref_known(v___x_5951_, 1);
                        v___f_5953_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__0___boxed as *mut core::ffi::c_void, 10, 4);
                        crate::leanh::lean_closure_set(v___f_5953_, 0, v_a_5949_);
                        crate::leanh::lean_closure_set(v___f_5953_, 1, v___x_5935_);
                        crate::leanh::lean_closure_set(v___f_5953_, 2, v_tactic_5936_);
                        crate::leanh::lean_closure_set(v___f_5953_, 3, v_allowFailure_5937_);
                        crate::leanh::lean_inc_ref(v___f_5953_);
                        v___x_5954_ = l_Lean_Meta_LibrarySearch_tryOnEach(
                            v___f_5953_,
                            v_a_5952_,
                            v_collectAll_5938_,
                            v___y_5940_,
                            v___y_5941_,
                            v___y_5942_,
                            v___y_5943_,
                        );
                        crate::leanh::lean_dec(v_a_5952_);
                        if crate::leanh::lean_obj_tag(v___x_5954_) == 0 {
                            v_a_5955_ = crate::leanh::lean_ctor_get(v___x_5954_, 0);
                            crate::leanh::lean_inc(v_a_5955_);
                            if crate::leanh::lean_obj_tag(v_a_5955_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_5954_, 1);
                                crate::leanh::lean_dec_ref(v___f_5953_);
                                crate::leanh::lean_dec(v_goal_5934_);
                                state = 1;
                                continue;
                            } else {
                                v_val_5956_ = crate::leanh::lean_ctor_get(v_a_5955_, 0);
                                v___x_6005_ = crate::leanh::lean_unsigned_to_nat(0);
                                v___x_6006_ = lean_array_get_size(v_val_5956_);
                                v___x_6007_ = lean_nat_dec_lt(v___x_6005_, v___x_6006_);
                                if v___x_6007_ == 0 {
                                    state = 11;
                                    continue;
                                } else {
                                    if v___x_6007_ == 0 {
                                        state = 11;
                                        continue;
                                    } else {
                                        v___x_6008_ = 0usize;
                                        v___x_6009_ = lean_usize_of_nat(v___x_6006_);
                                        v___x_6010_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__2(v_val_5956_, v___x_6008_, v___x_6009_);
                                        if v___x_6010_ == 0 {
                                            state = 11;
                                            continue;
                                        } else {
                                            crate::leanh::lean_dec_ref_known(v_a_5955_, 1);
                                            crate::leanh::lean_dec_ref(v___f_5953_);
                                            crate::leanh::lean_dec(v_goal_5934_);
                                            return v___x_5954_;
                                        }
                                    }
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___f_5953_);
                            crate::leanh::lean_dec(v_goal_5934_);
                            return v___x_5954_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_5949_);
                        crate::leanh::lean_dec_ref(v_allowFailure_5937_);
                        crate::leanh::lean_dec_ref(v_tactic_5936_);
                        crate::leanh::lean_dec_ref(v___x_5935_);
                        crate::leanh::lean_dec(v_goal_5934_);
                        v_a_6011_ = crate::leanh::lean_ctor_get(v___x_5951_, 0);
                        v_isSharedCheck_6018_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5951_)) as u8;
                        if v_isSharedCheck_6018_ == 0 {
                            v___x_6013_ = v___x_5951_;
                            v_isShared_6014_ = v_isSharedCheck_6018_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6011_);
                            crate::leanh::lean_dec(v___x_5951_);
                            v___x_6013_ = crate::leanh::lean_box(0);
                            v_isShared_6014_ = v_isSharedCheck_6018_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_allowFailure_5937_);
                    crate::leanh::lean_dec_ref(v_tactic_5936_);
                    crate::leanh::lean_dec_ref(v___x_5935_);
                    crate::leanh::lean_dec(v_goal_5934_);
                    v_a_6019_ = crate::leanh::lean_ctor_get(v___x_5948_, 0);
                    v_isSharedCheck_6026_ = (!crate::leanh::lean_is_exclusive(v___x_5948_)) as u8;
                    if v_isSharedCheck_6026_ == 0 {
                        v___x_6021_ = v___x_5948_;
                        v_isShared_6022_ = v_isSharedCheck_6026_;
                        state = 14;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6019_);
                        crate::leanh::lean_dec(v___x_5948_);
                        v___x_6021_ = crate::leanh::lean_box(0);
                        v_isShared_6022_ = v_isSharedCheck_6026_;
                        state = 14;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5946_ = crate::leanh::lean_box(0);
                v___x_5947_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5947_, 0, v___x_5946_);
                return v___x_5947_;
            }
            2 => {
                if v_includeStar_5939_ == 0 {
                    crate::leanh::lean_dec_ref_known(v_a_5955_, 1);
                    crate::leanh::lean_dec_ref(v___f_5953_);
                    crate::leanh::lean_dec(v_goal_5934_);
                    return v___x_5954_;
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_5954_, 1);
                    v___x_5958_ = l_Lean_Meta_LibrarySearch_getStarLemmas(
                        v___y_5940_,
                        v___y_5941_,
                        v___y_5942_,
                        v___y_5943_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5958_) == 0 {
                        v_a_5959_ = crate::leanh::lean_ctor_get(v___x_5958_, 0);
                        v_isSharedCheck_5992_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5958_)) as u8;
                        if v_isSharedCheck_5992_ == 0 {
                            v___x_5961_ = v___x_5958_;
                            v_isShared_5962_ = v_isSharedCheck_5992_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5959_);
                            crate::leanh::lean_dec(v___x_5958_);
                            v___x_5961_ = crate::leanh::lean_box(0);
                            v_isShared_5962_ = v_isSharedCheck_5992_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_a_5955_, 1);
                        crate::leanh::lean_dec_ref(v___f_5953_);
                        crate::leanh::lean_dec(v_goal_5934_);
                        v_a_5993_ = crate::leanh::lean_ctor_get(v___x_5958_, 0);
                        v_isSharedCheck_6000_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5958_)) as u8;
                        if v_isSharedCheck_6000_ == 0 {
                            v___x_5995_ = v___x_5958_;
                            v_isShared_5996_ = v_isSharedCheck_6000_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5993_);
                            crate::leanh::lean_dec(v___x_5958_);
                            v___x_5995_ = crate::leanh::lean_box(0);
                            v_isShared_5996_ = v_isSharedCheck_6000_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            3 => {
                v___x_5963_ = lean_array_get_size(v_a_5959_);
                v___x_5964_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5965_ = lean_nat_dec_eq(v___x_5963_, v___x_5964_);
                if v___x_5965_ == 0 {
                    crate::leanh::lean_inc(v_val_5956_);
                    crate::leanh::lean_del_object(v___x_5961_);
                    crate::leanh::lean_dec_ref_known(v_a_5955_, 1);
                    v___x_5966_ = lean_st_ref_get(v___y_5941_);
                    v_mctx_5967_ = crate::leanh::lean_ctor_get(v___x_5966_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_5967_);
                    crate::leanh::lean_dec(v___x_5966_);
                    v_sz_5968_ = lean_array_size(v_a_5959_);
                    v___x_5969_ = 0usize;
                    v___x_5970_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1(v_goal_5934_, v_mctx_5967_, v_sz_5968_, v___x_5969_, v_a_5959_);
                    v___x_5971_ = l_Lean_Meta_LibrarySearch_tryOnEach(
                        v___f_5953_,
                        v___x_5970_,
                        v_collectAll_5938_,
                        v___y_5940_,
                        v___y_5941_,
                        v___y_5942_,
                        v___y_5943_,
                    );
                    crate::leanh::lean_dec_ref(v___x_5970_);
                    if crate::leanh::lean_obj_tag(v___x_5971_) == 0 {
                        v_a_5972_ = crate::leanh::lean_ctor_get(v___x_5971_, 0);
                        v_isSharedCheck_5988_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5971_)) as u8;
                        if v_isSharedCheck_5988_ == 0 {
                            v___x_5974_ = v___x_5971_;
                            v_isShared_5975_ = v_isSharedCheck_5988_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5972_);
                            crate::leanh::lean_dec(v___x_5971_);
                            v___x_5974_ = crate::leanh::lean_box(0);
                            v_isShared_5975_ = v_isSharedCheck_5988_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_5956_);
                        return v___x_5971_;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_5959_);
                    crate::leanh::lean_dec_ref(v___f_5953_);
                    crate::leanh::lean_dec(v_goal_5934_);
                    if v_isShared_5962_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5961_, 0, v_a_5955_);
                        v___x_5990_ = v___x_5961_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_5991_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5991_, 0, v_a_5955_);
                        v___x_5990_ = v_reuseFailAlloc_5991_;
                        state = 8;
                        continue;
                    }
                }
            }
            4 => {
                if crate::leanh::lean_obj_tag(v_a_5972_) == 0 {
                    crate::leanh::lean_del_object(v___x_5974_);
                    crate::leanh::lean_dec(v_val_5956_);
                    state = 1;
                    continue;
                } else {
                    v_val_5976_ = crate::leanh::lean_ctor_get(v_a_5972_, 0);
                    v_isSharedCheck_5987_ = (!crate::leanh::lean_is_exclusive(v_a_5972_)) as u8;
                    if v_isSharedCheck_5987_ == 0 {
                        v___x_5978_ = v_a_5972_;
                        v_isShared_5979_ = v_isSharedCheck_5987_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5976_);
                        crate::leanh::lean_dec(v_a_5972_);
                        v___x_5978_ = crate::leanh::lean_box(0);
                        v_isShared_5979_ = v_isSharedCheck_5987_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___x_5980_ = l_Array_append___redArg(v_val_5956_, v_val_5976_);
                crate::leanh::lean_dec(v_val_5976_);
                if v_isShared_5979_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5978_, 0, v___x_5980_);
                    v___x_5982_ = v___x_5978_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5986_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5986_, 0, v___x_5980_);
                    v___x_5982_ = v_reuseFailAlloc_5986_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_5975_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5974_, 0, v___x_5982_);
                    v___x_5984_ = v___x_5974_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5985_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5985_, 0, v___x_5982_);
                    v___x_5984_ = v_reuseFailAlloc_5985_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5984_;
            }
            8 => {
                return v___x_5990_;
            }
            9 => {
                if v_isShared_5996_ == 0 {
                    v___x_5998_ = v___x_5995_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5999_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5999_, 0, v_a_5993_);
                    v___x_5998_ = v_reuseFailAlloc_5999_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5998_;
            }
            11 => {
                if v_collectAll_5938_ == 0 {
                    v___x_6002_ = lean_array_get_size(v_val_5956_);
                    v___x_6003_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_6004_ = lean_nat_dec_eq(v___x_6002_, v___x_6003_);
                    if v___x_6004_ == 0 {
                        crate::leanh::lean_dec_ref_known(v_a_5955_, 1);
                        crate::leanh::lean_dec_ref(v___f_5953_);
                        crate::leanh::lean_dec(v_goal_5934_);
                        return v___x_5954_;
                    } else {
                        state = 2;
                        continue;
                    }
                } else {
                    state = 2;
                    continue;
                }
            }
            12 => {
                if v_isShared_6014_ == 0 {
                    v___x_6016_ = v___x_6013_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_6017_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6017_, 0, v_a_6011_);
                    v___x_6016_ = v_reuseFailAlloc_6017_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_6016_;
            }
            14 => {
                if v_isShared_6022_ == 0 {
                    v___x_6024_ = v___x_6021_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_6025_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6025_, 0, v_a_6019_);
                    v___x_6024_ = v_reuseFailAlloc_6025_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_6024_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1___boxed(
    mut v_leavePercentHeartbeats_6027_: *mut crate::leanh::LeanObject,
    mut v_goal_6028_: *mut crate::leanh::LeanObject,
    mut v___x_6029_: *mut crate::leanh::LeanObject,
    mut v_tactic_6030_: *mut crate::leanh::LeanObject,
    mut v_allowFailure_6031_: *mut crate::leanh::LeanObject,
    mut v_collectAll_6032_: *mut crate::leanh::LeanObject,
    mut v_includeStar_6033_: *mut crate::leanh::LeanObject,
    mut v___y_6034_: *mut crate::leanh::LeanObject,
    mut v___y_6035_: *mut crate::leanh::LeanObject,
    mut v___y_6036_: *mut crate::leanh::LeanObject,
    mut v___y_6037_: *mut crate::leanh::LeanObject,
    mut v___y_6038_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_collectAll_boxed_6039_: u8 = 0;
    let mut v_includeStar_boxed_6040_: u8 = 0;
    let mut v_res_6041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_collectAll_boxed_6039_ = (crate::leanh::lean_unbox(v_collectAll_6032_) as u8);
    v_includeStar_boxed_6040_ = (crate::leanh::lean_unbox(v_includeStar_6033_) as u8);
    v_res_6041_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1(v_leavePercentHeartbeats_6027_, v_goal_6028_, v___x_6029_, v_tactic_6030_, v_allowFailure_6031_, v_collectAll_boxed_6039_, v_includeStar_boxed_6040_, v___y_6034_, v___y_6035_, v___y_6036_, v___y_6037_);
    crate::leanh::lean_dec(v___y_6037_);
    crate::leanh::lean_dec_ref(v___y_6036_);
    crate::leanh::lean_dec(v___y_6035_);
    crate::leanh::lean_dec_ref(v___y_6034_);
    crate::leanh::lean_dec(v_leavePercentHeartbeats_6027_);
    return v_res_6041_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__2(
    mut v_goal_6042_: *mut crate::leanh::LeanObject,
    mut v_x_6043_: *mut crate::leanh::LeanObject,
    mut v___y_6044_: *mut crate::leanh::LeanObject,
    mut v___y_6045_: *mut crate::leanh::LeanObject,
    mut v___y_6046_: *mut crate::leanh::LeanObject,
    mut v___y_6047_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6053_: u8 = 0;
    let mut v___x_6054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6058_: u8 = 0;
    let mut v_a_6059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6062_: u8 = 0;
    let mut v___x_6064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6066_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6049_ = l_Lean_MVarId_getType(
                    v_goal_6042_,
                    v___y_6044_,
                    v___y_6045_,
                    v___y_6046_,
                    v___y_6047_,
                );
                if crate::leanh::lean_obj_tag(v___x_6049_) == 0 {
                    v_a_6050_ = crate::leanh::lean_ctor_get(v___x_6049_, 0);
                    v_isSharedCheck_6058_ = (!crate::leanh::lean_is_exclusive(v___x_6049_)) as u8;
                    if v_isSharedCheck_6058_ == 0 {
                        v___x_6052_ = v___x_6049_;
                        v_isShared_6053_ = v_isSharedCheck_6058_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6050_);
                        crate::leanh::lean_dec(v___x_6049_);
                        v___x_6052_ = crate::leanh::lean_box(0);
                        v_isShared_6053_ = v_isSharedCheck_6058_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6059_ = crate::leanh::lean_ctor_get(v___x_6049_, 0);
                    v_isSharedCheck_6066_ = (!crate::leanh::lean_is_exclusive(v___x_6049_)) as u8;
                    if v_isSharedCheck_6066_ == 0 {
                        v___x_6061_ = v___x_6049_;
                        v_isShared_6062_ = v_isSharedCheck_6066_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6059_);
                        crate::leanh::lean_dec(v___x_6049_);
                        v___x_6061_ = crate::leanh::lean_box(0);
                        v_isShared_6062_ = v_isSharedCheck_6066_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6054_ = l_Lean_MessageData_ofExpr(v_a_6050_);
                if v_isShared_6053_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6052_, 0, v___x_6054_);
                    v___x_6056_ = v___x_6052_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6057_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6057_, 0, v___x_6054_);
                    v___x_6056_ = v_reuseFailAlloc_6057_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6056_;
            }
            3 => {
                if v_isShared_6062_ == 0 {
                    v___x_6064_ = v___x_6061_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6065_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6065_, 0, v_a_6059_);
                    v___x_6064_ = v_reuseFailAlloc_6065_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6064_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__2___boxed(
    mut v_goal_6067_: *mut crate::leanh::LeanObject,
    mut v_x_6068_: *mut crate::leanh::LeanObject,
    mut v___y_6069_: *mut crate::leanh::LeanObject,
    mut v___y_6070_: *mut crate::leanh::LeanObject,
    mut v___y_6071_: *mut crate::leanh::LeanObject,
    mut v___y_6072_: *mut crate::leanh::LeanObject,
    mut v___y_6073_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6074_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__2(v_goal_6067_, v_x_6068_, v___y_6069_, v___y_6070_, v___y_6071_, v___y_6072_);
    crate::leanh::lean_dec(v___y_6072_);
    crate::leanh::lean_dec_ref(v___y_6071_);
    crate::leanh::lean_dec(v___y_6070_);
    crate::leanh::lean_dec_ref(v___y_6069_);
    crate::leanh::lean_dec_ref(v_x_6068_);
    return v_res_6074_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__4(
    mut v_leavePercentHeartbeats_6075_: *mut crate::leanh::LeanObject,
    mut v_goal_6076_: *mut crate::leanh::LeanObject,
    mut v___x_6077_: *mut crate::leanh::LeanObject,
    mut v_tactic_6078_: *mut crate::leanh::LeanObject,
    mut v_allowFailure_6079_: *mut crate::leanh::LeanObject,
    mut v_collectAll_6080_: u8,
    mut v_includeStar_6081_: u8,
    mut v___x_6082_: u8,
    mut v___y_6083_: *mut crate::leanh::LeanObject,
    mut v___y_6084_: *mut crate::leanh::LeanObject,
    mut v___y_6085_: *mut crate::leanh::LeanObject,
    mut v___y_6086_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6105_: u8 = 0;
    let mut v___x_6106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6108_: u8 = 0;
    let mut v___x_6109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_6110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6111_: usize = 0;
    let mut v___x_6112_: usize = 0;
    let mut v___x_6113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6118_: u8 = 0;
    let mut v_val_6119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6122_: u8 = 0;
    let mut v___x_6123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6130_: u8 = 0;
    let mut v_isSharedCheck_6131_: u8 = 0;
    let mut v___x_6133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6135_: u8 = 0;
    let mut v_a_6136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6139_: u8 = 0;
    let mut v___x_6141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6143_: u8 = 0;
    let mut v___y_6145_: u8 = 0;
    let mut v___x_6146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6148_: u8 = 0;
    let mut v___x_6149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6151_: u8 = 0;
    let mut v___x_6152_: usize = 0;
    let mut v___x_6153_: usize = 0;
    let mut v___x_6154_: u8 = 0;
    let mut v_a_6155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6158_: u8 = 0;
    let mut v___x_6160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6162_: u8 = 0;
    let mut v_a_6163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6166_: u8 = 0;
    let mut v___x_6168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6170_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6091_ = l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg(
                    v_leavePercentHeartbeats_6075_,
                    v___y_6085_,
                );
                if crate::leanh::lean_obj_tag(v___x_6091_) == 0 {
                    v_a_6092_ = crate::leanh::lean_ctor_get(v___x_6091_, 0);
                    crate::leanh::lean_inc(v_a_6092_);
                    crate::leanh::lean_dec_ref_known(v___x_6091_, 1);
                    v___x_6093_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1___closed__0;
                    crate::leanh::lean_inc(v_goal_6076_);
                    v___x_6094_ = l_Lean_Meta_LibrarySearch_librarySearchSymm(
                        v___x_6093_,
                        v_goal_6076_,
                        v___y_6083_,
                        v___y_6084_,
                        v___y_6085_,
                        v___y_6086_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_6094_) == 0 {
                        v_a_6095_ = crate::leanh::lean_ctor_get(v___x_6094_, 0);
                        crate::leanh::lean_inc(v_a_6095_);
                        crate::leanh::lean_dec_ref_known(v___x_6094_, 1);
                        v___f_6096_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__0___boxed as *mut core::ffi::c_void, 10, 4);
                        crate::leanh::lean_closure_set(v___f_6096_, 0, v_a_6092_);
                        crate::leanh::lean_closure_set(v___f_6096_, 1, v___x_6077_);
                        crate::leanh::lean_closure_set(v___f_6096_, 2, v_tactic_6078_);
                        crate::leanh::lean_closure_set(v___f_6096_, 3, v_allowFailure_6079_);
                        crate::leanh::lean_inc_ref(v___f_6096_);
                        v___x_6097_ = l_Lean_Meta_LibrarySearch_tryOnEach(
                            v___f_6096_,
                            v_a_6095_,
                            v_collectAll_6080_,
                            v___y_6083_,
                            v___y_6084_,
                            v___y_6085_,
                            v___y_6086_,
                        );
                        crate::leanh::lean_dec(v_a_6095_);
                        if crate::leanh::lean_obj_tag(v___x_6097_) == 0 {
                            v_a_6098_ = crate::leanh::lean_ctor_get(v___x_6097_, 0);
                            crate::leanh::lean_inc(v_a_6098_);
                            if crate::leanh::lean_obj_tag(v_a_6098_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_6097_, 1);
                                crate::leanh::lean_dec_ref(v___f_6096_);
                                crate::leanh::lean_dec(v_goal_6076_);
                                state = 1;
                                continue;
                            } else {
                                v_val_6099_ = crate::leanh::lean_ctor_get(v_a_6098_, 0);
                                v___x_6149_ = crate::leanh::lean_unsigned_to_nat(0);
                                v___x_6150_ = lean_array_get_size(v_val_6099_);
                                v___x_6151_ = lean_nat_dec_lt(v___x_6149_, v___x_6150_);
                                if v___x_6151_ == 0 {
                                    v___y_6145_ = v___x_6082_;
                                    state = 11;
                                    continue;
                                } else {
                                    if v___x_6151_ == 0 {
                                        v___y_6145_ = v___x_6082_;
                                        state = 11;
                                        continue;
                                    } else {
                                        v___x_6152_ = 0usize;
                                        v___x_6153_ = lean_usize_of_nat(v___x_6150_);
                                        v___x_6154_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__2(v_val_6099_, v___x_6152_, v___x_6153_);
                                        v___y_6145_ = v___x_6154_;
                                        state = 11;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___f_6096_);
                            crate::leanh::lean_dec(v_goal_6076_);
                            return v___x_6097_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_6092_);
                        crate::leanh::lean_dec_ref(v_allowFailure_6079_);
                        crate::leanh::lean_dec_ref(v_tactic_6078_);
                        crate::leanh::lean_dec_ref(v___x_6077_);
                        crate::leanh::lean_dec(v_goal_6076_);
                        v_a_6155_ = crate::leanh::lean_ctor_get(v___x_6094_, 0);
                        v_isSharedCheck_6162_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6094_)) as u8;
                        if v_isSharedCheck_6162_ == 0 {
                            v___x_6157_ = v___x_6094_;
                            v_isShared_6158_ = v_isSharedCheck_6162_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6155_);
                            crate::leanh::lean_dec(v___x_6094_);
                            v___x_6157_ = crate::leanh::lean_box(0);
                            v_isShared_6158_ = v_isSharedCheck_6162_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_allowFailure_6079_);
                    crate::leanh::lean_dec_ref(v_tactic_6078_);
                    crate::leanh::lean_dec_ref(v___x_6077_);
                    crate::leanh::lean_dec(v_goal_6076_);
                    v_a_6163_ = crate::leanh::lean_ctor_get(v___x_6091_, 0);
                    v_isSharedCheck_6170_ = (!crate::leanh::lean_is_exclusive(v___x_6091_)) as u8;
                    if v_isSharedCheck_6170_ == 0 {
                        v___x_6165_ = v___x_6091_;
                        v_isShared_6166_ = v_isSharedCheck_6170_;
                        state = 14;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6163_);
                        crate::leanh::lean_dec(v___x_6091_);
                        v___x_6165_ = crate::leanh::lean_box(0);
                        v_isShared_6166_ = v_isSharedCheck_6170_;
                        state = 14;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6089_ = crate::leanh::lean_box(0);
                v___x_6090_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6090_, 0, v___x_6089_);
                return v___x_6090_;
            }
            2 => {
                if v_includeStar_6081_ == 0 {
                    crate::leanh::lean_dec_ref_known(v_a_6098_, 1);
                    crate::leanh::lean_dec_ref(v___f_6096_);
                    crate::leanh::lean_dec(v_goal_6076_);
                    return v___x_6097_;
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_6097_, 1);
                    v___x_6101_ = l_Lean_Meta_LibrarySearch_getStarLemmas(
                        v___y_6083_,
                        v___y_6084_,
                        v___y_6085_,
                        v___y_6086_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_6101_) == 0 {
                        v_a_6102_ = crate::leanh::lean_ctor_get(v___x_6101_, 0);
                        v_isSharedCheck_6135_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6101_)) as u8;
                        if v_isSharedCheck_6135_ == 0 {
                            v___x_6104_ = v___x_6101_;
                            v_isShared_6105_ = v_isSharedCheck_6135_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6102_);
                            crate::leanh::lean_dec(v___x_6101_);
                            v___x_6104_ = crate::leanh::lean_box(0);
                            v_isShared_6105_ = v_isSharedCheck_6135_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_a_6098_, 1);
                        crate::leanh::lean_dec_ref(v___f_6096_);
                        crate::leanh::lean_dec(v_goal_6076_);
                        v_a_6136_ = crate::leanh::lean_ctor_get(v___x_6101_, 0);
                        v_isSharedCheck_6143_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6101_)) as u8;
                        if v_isSharedCheck_6143_ == 0 {
                            v___x_6138_ = v___x_6101_;
                            v_isShared_6139_ = v_isSharedCheck_6143_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6136_);
                            crate::leanh::lean_dec(v___x_6101_);
                            v___x_6138_ = crate::leanh::lean_box(0);
                            v_isShared_6139_ = v_isSharedCheck_6143_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            3 => {
                v___x_6106_ = lean_array_get_size(v_a_6102_);
                v___x_6107_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_6108_ = lean_nat_dec_eq(v___x_6106_, v___x_6107_);
                if v___x_6108_ == 0 {
                    crate::leanh::lean_inc(v_val_6099_);
                    crate::leanh::lean_del_object(v___x_6104_);
                    crate::leanh::lean_dec_ref_known(v_a_6098_, 1);
                    v___x_6109_ = lean_st_ref_get(v___y_6084_);
                    v_mctx_6110_ = crate::leanh::lean_ctor_get(v___x_6109_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_6110_);
                    crate::leanh::lean_dec(v___x_6109_);
                    v_sz_6111_ = lean_array_size(v_a_6102_);
                    v___x_6112_ = 0usize;
                    v___x_6113_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1(v_goal_6076_, v_mctx_6110_, v_sz_6111_, v___x_6112_, v_a_6102_);
                    v___x_6114_ = l_Lean_Meta_LibrarySearch_tryOnEach(
                        v___f_6096_,
                        v___x_6113_,
                        v_collectAll_6080_,
                        v___y_6083_,
                        v___y_6084_,
                        v___y_6085_,
                        v___y_6086_,
                    );
                    crate::leanh::lean_dec_ref(v___x_6113_);
                    if crate::leanh::lean_obj_tag(v___x_6114_) == 0 {
                        v_a_6115_ = crate::leanh::lean_ctor_get(v___x_6114_, 0);
                        v_isSharedCheck_6131_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6114_)) as u8;
                        if v_isSharedCheck_6131_ == 0 {
                            v___x_6117_ = v___x_6114_;
                            v_isShared_6118_ = v_isSharedCheck_6131_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6115_);
                            crate::leanh::lean_dec(v___x_6114_);
                            v___x_6117_ = crate::leanh::lean_box(0);
                            v_isShared_6118_ = v_isSharedCheck_6131_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_6099_);
                        return v___x_6114_;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_6102_);
                    crate::leanh::lean_dec_ref(v___f_6096_);
                    crate::leanh::lean_dec(v_goal_6076_);
                    if v_isShared_6105_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6104_, 0, v_a_6098_);
                        v___x_6133_ = v___x_6104_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_6134_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6134_, 0, v_a_6098_);
                        v___x_6133_ = v_reuseFailAlloc_6134_;
                        state = 8;
                        continue;
                    }
                }
            }
            4 => {
                if crate::leanh::lean_obj_tag(v_a_6115_) == 0 {
                    crate::leanh::lean_del_object(v___x_6117_);
                    crate::leanh::lean_dec(v_val_6099_);
                    state = 1;
                    continue;
                } else {
                    v_val_6119_ = crate::leanh::lean_ctor_get(v_a_6115_, 0);
                    v_isSharedCheck_6130_ = (!crate::leanh::lean_is_exclusive(v_a_6115_)) as u8;
                    if v_isSharedCheck_6130_ == 0 {
                        v___x_6121_ = v_a_6115_;
                        v_isShared_6122_ = v_isSharedCheck_6130_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_6119_);
                        crate::leanh::lean_dec(v_a_6115_);
                        v___x_6121_ = crate::leanh::lean_box(0);
                        v_isShared_6122_ = v_isSharedCheck_6130_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___x_6123_ = l_Array_append___redArg(v_val_6099_, v_val_6119_);
                crate::leanh::lean_dec(v_val_6119_);
                if v_isShared_6122_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6121_, 0, v___x_6123_);
                    v___x_6125_ = v___x_6121_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6129_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6129_, 0, v___x_6123_);
                    v___x_6125_ = v_reuseFailAlloc_6129_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_6118_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6117_, 0, v___x_6125_);
                    v___x_6127_ = v___x_6117_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6128_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6128_, 0, v___x_6125_);
                    v___x_6127_ = v_reuseFailAlloc_6128_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6127_;
            }
            8 => {
                return v___x_6133_;
            }
            9 => {
                if v_isShared_6139_ == 0 {
                    v___x_6141_ = v___x_6138_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6142_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6142_, 0, v_a_6136_);
                    v___x_6141_ = v_reuseFailAlloc_6142_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6141_;
            }
            11 => {
                if v___y_6145_ == 0 {
                    if v_collectAll_6080_ == 0 {
                        v___x_6146_ = lean_array_get_size(v_val_6099_);
                        v___x_6147_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_6148_ = lean_nat_dec_eq(v___x_6146_, v___x_6147_);
                        if v___x_6148_ == 0 {
                            crate::leanh::lean_dec_ref_known(v_a_6098_, 1);
                            crate::leanh::lean_dec_ref(v___f_6096_);
                            crate::leanh::lean_dec(v_goal_6076_);
                            return v___x_6097_;
                        } else {
                            state = 2;
                            continue;
                        }
                    } else {
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v_a_6098_, 1);
                    crate::leanh::lean_dec_ref(v___f_6096_);
                    crate::leanh::lean_dec(v_goal_6076_);
                    return v___x_6097_;
                }
            }
            12 => {
                if v_isShared_6158_ == 0 {
                    v___x_6160_ = v___x_6157_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_6161_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6161_, 0, v_a_6155_);
                    v___x_6160_ = v_reuseFailAlloc_6161_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_6160_;
            }
            14 => {
                if v_isShared_6166_ == 0 {
                    v___x_6168_ = v___x_6165_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_6169_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6169_, 0, v_a_6163_);
                    v___x_6168_ = v_reuseFailAlloc_6169_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_6168_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__4___boxed(
    mut v_leavePercentHeartbeats_6171_: *mut crate::leanh::LeanObject,
    mut v_goal_6172_: *mut crate::leanh::LeanObject,
    mut v___x_6173_: *mut crate::leanh::LeanObject,
    mut v_tactic_6174_: *mut crate::leanh::LeanObject,
    mut v_allowFailure_6175_: *mut crate::leanh::LeanObject,
    mut v_collectAll_6176_: *mut crate::leanh::LeanObject,
    mut v_includeStar_6177_: *mut crate::leanh::LeanObject,
    mut v___x_6178_: *mut crate::leanh::LeanObject,
    mut v___y_6179_: *mut crate::leanh::LeanObject,
    mut v___y_6180_: *mut crate::leanh::LeanObject,
    mut v___y_6181_: *mut crate::leanh::LeanObject,
    mut v___y_6182_: *mut crate::leanh::LeanObject,
    mut v___y_6183_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_collectAll_boxed_6184_: u8 = 0;
    let mut v_includeStar_boxed_6185_: u8 = 0;
    let mut v___x_15848__boxed_6186_: u8 = 0;
    let mut v_res_6187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_collectAll_boxed_6184_ = (crate::leanh::lean_unbox(v_collectAll_6176_) as u8);
    v_includeStar_boxed_6185_ = (crate::leanh::lean_unbox(v_includeStar_6177_) as u8);
    v___x_15848__boxed_6186_ = (crate::leanh::lean_unbox(v___x_6178_) as u8);
    v_res_6187_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__4(v_leavePercentHeartbeats_6171_, v_goal_6172_, v___x_6173_, v_tactic_6174_, v_allowFailure_6175_, v_collectAll_boxed_6184_, v_includeStar_boxed_6185_, v___x_15848__boxed_6186_, v___y_6179_, v___y_6180_, v___y_6181_, v___y_6182_);
    crate::leanh::lean_dec(v___y_6182_);
    crate::leanh::lean_dec_ref(v___y_6181_);
    crate::leanh::lean_dec(v___y_6180_);
    crate::leanh::lean_dec_ref(v___y_6179_);
    crate::leanh::lean_dec(v_leavePercentHeartbeats_6171_);
    return v_res_6187_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__5(
    mut v_leavePercentHeartbeats_6188_: *mut crate::leanh::LeanObject,
    mut v_goal_6189_: *mut crate::leanh::LeanObject,
    mut v___x_6190_: *mut crate::leanh::LeanObject,
    mut v_tactic_6191_: *mut crate::leanh::LeanObject,
    mut v_allowFailure_6192_: *mut crate::leanh::LeanObject,
    mut v_collectAll_6193_: u8,
    mut v_includeStar_6194_: u8,
    mut v___x_6195_: u8,
    mut v___y_6196_: *mut crate::leanh::LeanObject,
    mut v___y_6197_: *mut crate::leanh::LeanObject,
    mut v___y_6198_: *mut crate::leanh::LeanObject,
    mut v___y_6199_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6218_: u8 = 0;
    let mut v___x_6219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6221_: u8 = 0;
    let mut v___x_6222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_6223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6224_: usize = 0;
    let mut v___x_6225_: usize = 0;
    let mut v___x_6226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6231_: u8 = 0;
    let mut v_val_6232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6235_: u8 = 0;
    let mut v___x_6236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6243_: u8 = 0;
    let mut v_isSharedCheck_6244_: u8 = 0;
    let mut v___x_6246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6248_: u8 = 0;
    let mut v_a_6249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6252_: u8 = 0;
    let mut v___x_6254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6256_: u8 = 0;
    let mut v___x_6259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6261_: u8 = 0;
    let mut v___x_6262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6264_: u8 = 0;
    let mut v___x_6265_: usize = 0;
    let mut v___x_6266_: usize = 0;
    let mut v___x_6267_: u8 = 0;
    let mut v_a_6268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6271_: u8 = 0;
    let mut v___x_6273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6275_: u8 = 0;
    let mut v_a_6276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6279_: u8 = 0;
    let mut v___x_6281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6283_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6204_ = l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg(
                    v_leavePercentHeartbeats_6188_,
                    v___y_6198_,
                );
                if crate::leanh::lean_obj_tag(v___x_6204_) == 0 {
                    v_a_6205_ = crate::leanh::lean_ctor_get(v___x_6204_, 0);
                    crate::leanh::lean_inc(v_a_6205_);
                    crate::leanh::lean_dec_ref_known(v___x_6204_, 1);
                    v___x_6206_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1___closed__0;
                    crate::leanh::lean_inc(v_goal_6189_);
                    v___x_6207_ = l_Lean_Meta_LibrarySearch_librarySearchSymm(
                        v___x_6206_,
                        v_goal_6189_,
                        v___y_6196_,
                        v___y_6197_,
                        v___y_6198_,
                        v___y_6199_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_6207_) == 0 {
                        v_a_6208_ = crate::leanh::lean_ctor_get(v___x_6207_, 0);
                        crate::leanh::lean_inc(v_a_6208_);
                        crate::leanh::lean_dec_ref_known(v___x_6207_, 1);
                        v___f_6209_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__0___boxed as *mut core::ffi::c_void, 10, 4);
                        crate::leanh::lean_closure_set(v___f_6209_, 0, v_a_6205_);
                        crate::leanh::lean_closure_set(v___f_6209_, 1, v___x_6190_);
                        crate::leanh::lean_closure_set(v___f_6209_, 2, v_tactic_6191_);
                        crate::leanh::lean_closure_set(v___f_6209_, 3, v_allowFailure_6192_);
                        crate::leanh::lean_inc_ref(v___f_6209_);
                        v___x_6210_ = l_Lean_Meta_LibrarySearch_tryOnEach(
                            v___f_6209_,
                            v_a_6208_,
                            v_collectAll_6193_,
                            v___y_6196_,
                            v___y_6197_,
                            v___y_6198_,
                            v___y_6199_,
                        );
                        crate::leanh::lean_dec(v_a_6208_);
                        if crate::leanh::lean_obj_tag(v___x_6210_) == 0 {
                            v_a_6211_ = crate::leanh::lean_ctor_get(v___x_6210_, 0);
                            crate::leanh::lean_inc(v_a_6211_);
                            if crate::leanh::lean_obj_tag(v_a_6211_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_6210_, 1);
                                crate::leanh::lean_dec_ref(v___f_6209_);
                                crate::leanh::lean_dec(v_goal_6189_);
                                state = 1;
                                continue;
                            } else {
                                v_val_6212_ = crate::leanh::lean_ctor_get(v_a_6211_, 0);
                                v___x_6262_ = crate::leanh::lean_unsigned_to_nat(0);
                                v___x_6263_ = lean_array_get_size(v_val_6212_);
                                v___x_6264_ = lean_nat_dec_lt(v___x_6262_, v___x_6263_);
                                if v___x_6264_ == 0 {
                                    state = 12;
                                    continue;
                                } else {
                                    if v___x_6264_ == 0 {
                                        state = 12;
                                        continue;
                                    } else {
                                        v___x_6265_ = 0usize;
                                        v___x_6266_ = lean_usize_of_nat(v___x_6263_);
                                        v___x_6267_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__2(v_val_6212_, v___x_6265_, v___x_6266_);
                                        if v___x_6267_ == 0 {
                                            state = 12;
                                            continue;
                                        } else {
                                            if v___x_6195_ == 0 {
                                                state = 11;
                                                continue;
                                            } else {
                                                crate::leanh::lean_dec_ref_known(v_a_6211_, 1);
                                                crate::leanh::lean_dec_ref(v___f_6209_);
                                                crate::leanh::lean_dec(v_goal_6189_);
                                                return v___x_6210_;
                                            }
                                        }
                                    }
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___f_6209_);
                            crate::leanh::lean_dec(v_goal_6189_);
                            return v___x_6210_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_6205_);
                        crate::leanh::lean_dec_ref(v_allowFailure_6192_);
                        crate::leanh::lean_dec_ref(v_tactic_6191_);
                        crate::leanh::lean_dec_ref(v___x_6190_);
                        crate::leanh::lean_dec(v_goal_6189_);
                        v_a_6268_ = crate::leanh::lean_ctor_get(v___x_6207_, 0);
                        v_isSharedCheck_6275_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6207_)) as u8;
                        if v_isSharedCheck_6275_ == 0 {
                            v___x_6270_ = v___x_6207_;
                            v_isShared_6271_ = v_isSharedCheck_6275_;
                            state = 13;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6268_);
                            crate::leanh::lean_dec(v___x_6207_);
                            v___x_6270_ = crate::leanh::lean_box(0);
                            v_isShared_6271_ = v_isSharedCheck_6275_;
                            state = 13;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_allowFailure_6192_);
                    crate::leanh::lean_dec_ref(v_tactic_6191_);
                    crate::leanh::lean_dec_ref(v___x_6190_);
                    crate::leanh::lean_dec(v_goal_6189_);
                    v_a_6276_ = crate::leanh::lean_ctor_get(v___x_6204_, 0);
                    v_isSharedCheck_6283_ = (!crate::leanh::lean_is_exclusive(v___x_6204_)) as u8;
                    if v_isSharedCheck_6283_ == 0 {
                        v___x_6278_ = v___x_6204_;
                        v_isShared_6279_ = v_isSharedCheck_6283_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6276_);
                        crate::leanh::lean_dec(v___x_6204_);
                        v___x_6278_ = crate::leanh::lean_box(0);
                        v_isShared_6279_ = v_isSharedCheck_6283_;
                        state = 15;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6202_ = crate::leanh::lean_box(0);
                v___x_6203_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6203_, 0, v___x_6202_);
                return v___x_6203_;
            }
            2 => {
                v___x_6214_ = l_Lean_Meta_LibrarySearch_getStarLemmas(
                    v___y_6196_,
                    v___y_6197_,
                    v___y_6198_,
                    v___y_6199_,
                );
                if crate::leanh::lean_obj_tag(v___x_6214_) == 0 {
                    v_a_6215_ = crate::leanh::lean_ctor_get(v___x_6214_, 0);
                    v_isSharedCheck_6248_ = (!crate::leanh::lean_is_exclusive(v___x_6214_)) as u8;
                    if v_isSharedCheck_6248_ == 0 {
                        v___x_6217_ = v___x_6214_;
                        v_isShared_6218_ = v_isSharedCheck_6248_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6215_);
                        crate::leanh::lean_dec(v___x_6214_);
                        v___x_6217_ = crate::leanh::lean_box(0);
                        v_isShared_6218_ = v_isSharedCheck_6248_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v_a_6211_, 1);
                    crate::leanh::lean_dec_ref(v___f_6209_);
                    crate::leanh::lean_dec(v_goal_6189_);
                    v_a_6249_ = crate::leanh::lean_ctor_get(v___x_6214_, 0);
                    v_isSharedCheck_6256_ = (!crate::leanh::lean_is_exclusive(v___x_6214_)) as u8;
                    if v_isSharedCheck_6256_ == 0 {
                        v___x_6251_ = v___x_6214_;
                        v_isShared_6252_ = v_isSharedCheck_6256_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6249_);
                        crate::leanh::lean_dec(v___x_6214_);
                        v___x_6251_ = crate::leanh::lean_box(0);
                        v_isShared_6252_ = v_isSharedCheck_6256_;
                        state = 9;
                        continue;
                    }
                }
            }
            3 => {
                v___x_6219_ = lean_array_get_size(v_a_6215_);
                v___x_6220_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_6221_ = lean_nat_dec_eq(v___x_6219_, v___x_6220_);
                if v___x_6221_ == 0 {
                    crate::leanh::lean_inc(v_val_6212_);
                    crate::leanh::lean_del_object(v___x_6217_);
                    crate::leanh::lean_dec_ref_known(v_a_6211_, 1);
                    v___x_6222_ = lean_st_ref_get(v___y_6197_);
                    v_mctx_6223_ = crate::leanh::lean_ctor_get(v___x_6222_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_6223_);
                    crate::leanh::lean_dec(v___x_6222_);
                    v_sz_6224_ = lean_array_size(v_a_6215_);
                    v___x_6225_ = 0usize;
                    v___x_6226_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1(v_goal_6189_, v_mctx_6223_, v_sz_6224_, v___x_6225_, v_a_6215_);
                    v___x_6227_ = l_Lean_Meta_LibrarySearch_tryOnEach(
                        v___f_6209_,
                        v___x_6226_,
                        v_collectAll_6193_,
                        v___y_6196_,
                        v___y_6197_,
                        v___y_6198_,
                        v___y_6199_,
                    );
                    crate::leanh::lean_dec_ref(v___x_6226_);
                    if crate::leanh::lean_obj_tag(v___x_6227_) == 0 {
                        v_a_6228_ = crate::leanh::lean_ctor_get(v___x_6227_, 0);
                        v_isSharedCheck_6244_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6227_)) as u8;
                        if v_isSharedCheck_6244_ == 0 {
                            v___x_6230_ = v___x_6227_;
                            v_isShared_6231_ = v_isSharedCheck_6244_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6228_);
                            crate::leanh::lean_dec(v___x_6227_);
                            v___x_6230_ = crate::leanh::lean_box(0);
                            v_isShared_6231_ = v_isSharedCheck_6244_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_6212_);
                        return v___x_6227_;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_6215_);
                    crate::leanh::lean_dec_ref(v___f_6209_);
                    crate::leanh::lean_dec(v_goal_6189_);
                    if v_isShared_6218_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6217_, 0, v_a_6211_);
                        v___x_6246_ = v___x_6217_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_6247_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6247_, 0, v_a_6211_);
                        v___x_6246_ = v_reuseFailAlloc_6247_;
                        state = 8;
                        continue;
                    }
                }
            }
            4 => {
                if crate::leanh::lean_obj_tag(v_a_6228_) == 0 {
                    crate::leanh::lean_del_object(v___x_6230_);
                    crate::leanh::lean_dec(v_val_6212_);
                    state = 1;
                    continue;
                } else {
                    v_val_6232_ = crate::leanh::lean_ctor_get(v_a_6228_, 0);
                    v_isSharedCheck_6243_ = (!crate::leanh::lean_is_exclusive(v_a_6228_)) as u8;
                    if v_isSharedCheck_6243_ == 0 {
                        v___x_6234_ = v_a_6228_;
                        v_isShared_6235_ = v_isSharedCheck_6243_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_6232_);
                        crate::leanh::lean_dec(v_a_6228_);
                        v___x_6234_ = crate::leanh::lean_box(0);
                        v_isShared_6235_ = v_isSharedCheck_6243_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___x_6236_ = l_Array_append___redArg(v_val_6212_, v_val_6232_);
                crate::leanh::lean_dec(v_val_6232_);
                if v_isShared_6235_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6234_, 0, v___x_6236_);
                    v___x_6238_ = v___x_6234_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6242_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6242_, 0, v___x_6236_);
                    v___x_6238_ = v_reuseFailAlloc_6242_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_6231_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6230_, 0, v___x_6238_);
                    v___x_6240_ = v___x_6230_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6241_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6241_, 0, v___x_6238_);
                    v___x_6240_ = v_reuseFailAlloc_6241_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6240_;
            }
            8 => {
                return v___x_6246_;
            }
            9 => {
                if v_isShared_6252_ == 0 {
                    v___x_6254_ = v___x_6251_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6255_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6255_, 0, v_a_6249_);
                    v___x_6254_ = v_reuseFailAlloc_6255_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6254_;
            }
            11 => {
                if v_includeStar_6194_ == 0 {
                    if v___x_6195_ == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_6210_, 1);
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref_known(v_a_6211_, 1);
                        crate::leanh::lean_dec_ref(v___f_6209_);
                        crate::leanh::lean_dec(v_goal_6189_);
                        return v___x_6210_;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_6210_, 1);
                    state = 2;
                    continue;
                }
            }
            12 => {
                if v_collectAll_6193_ == 0 {
                    if v___x_6195_ == 0 {
                        state = 11;
                        continue;
                    } else {
                        v___x_6259_ = lean_array_get_size(v_val_6212_);
                        v___x_6260_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_6261_ = lean_nat_dec_eq(v___x_6259_, v___x_6260_);
                        if v___x_6261_ == 0 {
                            crate::leanh::lean_dec_ref_known(v_a_6211_, 1);
                            crate::leanh::lean_dec_ref(v___f_6209_);
                            crate::leanh::lean_dec(v_goal_6189_);
                            return v___x_6210_;
                        } else {
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    state = 11;
                    continue;
                }
            }
            13 => {
                if v_isShared_6271_ == 0 {
                    v___x_6273_ = v___x_6270_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_6274_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6274_, 0, v_a_6268_);
                    v___x_6273_ = v_reuseFailAlloc_6274_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_6273_;
            }
            15 => {
                if v_isShared_6279_ == 0 {
                    v___x_6281_ = v___x_6278_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_6282_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6282_, 0, v_a_6276_);
                    v___x_6281_ = v_reuseFailAlloc_6282_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_6281_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__5___boxed(
    mut v_leavePercentHeartbeats_6284_: *mut crate::leanh::LeanObject,
    mut v_goal_6285_: *mut crate::leanh::LeanObject,
    mut v___x_6286_: *mut crate::leanh::LeanObject,
    mut v_tactic_6287_: *mut crate::leanh::LeanObject,
    mut v_allowFailure_6288_: *mut crate::leanh::LeanObject,
    mut v_collectAll_6289_: *mut crate::leanh::LeanObject,
    mut v_includeStar_6290_: *mut crate::leanh::LeanObject,
    mut v___x_6291_: *mut crate::leanh::LeanObject,
    mut v___y_6292_: *mut crate::leanh::LeanObject,
    mut v___y_6293_: *mut crate::leanh::LeanObject,
    mut v___y_6294_: *mut crate::leanh::LeanObject,
    mut v___y_6295_: *mut crate::leanh::LeanObject,
    mut v___y_6296_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_collectAll_boxed_6297_: u8 = 0;
    let mut v_includeStar_boxed_6298_: u8 = 0;
    let mut v___x_16037__boxed_6299_: u8 = 0;
    let mut v_res_6300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_collectAll_boxed_6297_ = (crate::leanh::lean_unbox(v_collectAll_6289_) as u8);
    v_includeStar_boxed_6298_ = (crate::leanh::lean_unbox(v_includeStar_6290_) as u8);
    v___x_16037__boxed_6299_ = (crate::leanh::lean_unbox(v___x_6291_) as u8);
    v_res_6300_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__5(v_leavePercentHeartbeats_6284_, v_goal_6285_, v___x_6286_, v_tactic_6287_, v_allowFailure_6288_, v_collectAll_boxed_6297_, v_includeStar_boxed_6298_, v___x_16037__boxed_6299_, v___y_6292_, v___y_6293_, v___y_6294_, v___y_6295_);
    crate::leanh::lean_dec(v___y_6295_);
    crate::leanh::lean_dec_ref(v___y_6294_);
    crate::leanh::lean_dec(v___y_6293_);
    crate::leanh::lean_dec_ref(v___y_6292_);
    crate::leanh::lean_dec(v_leavePercentHeartbeats_6284_);
    return v_res_6300_;
}
pub unsafe fn l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4_spec__4(
    mut v_e_6301_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_e_6301_) == 0 {
        let mut v___x_6302_: u8 = 0;
        v___x_6302_ = 2;
        return v___x_6302_;
    } else {
        let mut v_a_6303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_6303_ = crate::leanh::lean_ctor_get(v_e_6301_, 0);
        if crate::leanh::lean_obj_tag(v_a_6303_) == 0 {
            let mut v___x_6304_: u8 = 0;
            v___x_6304_ = 1;
            return v___x_6304_;
        } else {
            let mut v___x_6305_: u8 = 0;
            v___x_6305_ = 0;
            return v___x_6305_;
        }
    }
}
pub unsafe fn l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4_spec__4___boxed(
    mut v_e_6306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6307_: u8 = 0;
    let mut v_r_6308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6307_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4_spec__4(v_e_6306_);
    crate::leanh::lean_dec_ref(v_e_6306_);
    v_r_6308_ = crate::leanh::lean_box((v_res_6307_) as usize);
    return v_r_6308_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4(
    mut v_cls_6309_: *mut crate::leanh::LeanObject,
    mut v_collapsed_6310_: u8,
    mut v_tag_6311_: *mut crate::leanh::LeanObject,
    mut v_opts_6312_: *mut crate::leanh::LeanObject,
    mut v_clsEnabled_6313_: u8,
    mut v_oldTraces_6314_: *mut crate::leanh::LeanObject,
    mut v_msg_6315_: *mut crate::leanh::LeanObject,
    mut v_resStartStop_6316_: *mut crate::leanh::LeanObject,
    mut v___y_6317_: *mut crate::leanh::LeanObject,
    mut v___y_6318_: *mut crate::leanh::LeanObject,
    mut v___y_6319_: *mut crate::leanh::LeanObject,
    mut v___y_6320_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_6322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6326_: u8 = 0;
    let mut v___y_6328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_6330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6336_: u8 = 0;
    let mut v___x_6338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6340_: u8 = 0;
    let mut v_fst_6341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6345_: u8 = 0;
    let mut v___x_6346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6347_: u8 = 0;
    let mut v___y_6349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_6351_: u8 = 0;
    let mut v___x_6352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_6358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6361_: f64 = 0.0;
    let mut v_data_6362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_6363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6364_: f64 = 0.0;
    let mut v___x_6365_: f64 = 0.0;
    let mut v_reuseFailAlloc_6366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_6369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6374_: u8 = 0;
    let mut v___x_6375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_6376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_6379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_6381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_6382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_6383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6387_: u8 = 0;
    let mut v_tid_6388_: u64 = 0;
    let mut v_traces_6389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6392_: u8 = 0;
    let mut v___x_6393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6402_: u8 = 0;
    let mut v_isSharedCheck_6403_: u8 = 0;
    let mut v___y_6405_: f64 = 0.0;
    let mut v___x_6406_: f64 = 0.0;
    let mut v___x_6407_: f64 = 0.0;
    let mut v___x_6408_: f64 = 0.0;
    let mut v___x_6409_: u8 = 0;
    let mut v___x_6410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6411_: u8 = 0;
    let mut v___x_6412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6414_: f64 = 0.0;
    let mut v___x_6415_: f64 = 0.0;
    let mut v___x_6416_: f64 = 0.0;
    let mut v___x_6417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6419_: f64 = 0.0;
    let mut v_isSharedCheck_6420_: u8 = 0;
    let mut v_isSharedCheck_6421_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_6322_ = crate::leanh::lean_ctor_get(v_resStartStop_6316_, 0);
                v_snd_6323_ = crate::leanh::lean_ctor_get(v_resStartStop_6316_, 1);
                v_isSharedCheck_6421_ =
                    (!crate::leanh::lean_is_exclusive(v_resStartStop_6316_)) as u8;
                if v_isSharedCheck_6421_ == 0 {
                    v___x_6325_ = v_resStartStop_6316_;
                    v_isShared_6326_ = v_isSharedCheck_6421_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_6323_);
                    crate::leanh::lean_inc(v_fst_6322_);
                    crate::leanh::lean_dec(v_resStartStop_6316_);
                    v___x_6325_ = crate::leanh::lean_box(0);
                    v_isShared_6326_ = v_isSharedCheck_6421_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_6341_ = crate::leanh::lean_ctor_get(v_snd_6323_, 0);
                v_snd_6342_ = crate::leanh::lean_ctor_get(v_snd_6323_, 1);
                v_isSharedCheck_6420_ = (!crate::leanh::lean_is_exclusive(v_snd_6323_)) as u8;
                if v_isSharedCheck_6420_ == 0 {
                    v___x_6344_ = v_snd_6323_;
                    v_isShared_6345_ = v_isSharedCheck_6420_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_6342_);
                    crate::leanh::lean_inc(v_fst_6341_);
                    crate::leanh::lean_dec(v_snd_6323_);
                    v___x_6344_ = crate::leanh::lean_box(0);
                    v_isShared_6345_ = v_isSharedCheck_6420_;
                    state = 5;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v___y_6328_);
                v___x_6331_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3(v_oldTraces_6314_, v_data_6330_, v___y_6328_, v___y_6329_, v___y_6317_, v___y_6318_, v___y_6319_, v___y_6320_);
                if crate::leanh::lean_obj_tag(v___x_6331_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_6331_, 1);
                    v___x_6332_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__4___redArg(v_fst_6322_);
                    return v___x_6332_;
                } else {
                    crate::leanh::lean_dec(v_fst_6322_);
                    v_a_6333_ = crate::leanh::lean_ctor_get(v___x_6331_, 0);
                    v_isSharedCheck_6340_ = (!crate::leanh::lean_is_exclusive(v___x_6331_)) as u8;
                    if v_isSharedCheck_6340_ == 0 {
                        v___x_6335_ = v___x_6331_;
                        v_isShared_6336_ = v_isSharedCheck_6340_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6333_);
                        crate::leanh::lean_dec(v___x_6331_);
                        v___x_6335_ = crate::leanh::lean_box(0);
                        v_isShared_6336_ = v_isSharedCheck_6340_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_6336_ == 0 {
                    v___x_6338_ = v___x_6335_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6339_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6339_, 0, v_a_6333_);
                    v___x_6338_ = v_reuseFailAlloc_6339_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6338_;
            }
            5 => {
                v___x_6346_ = l_Lean_trace_profiler;
                v___x_6347_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_opts_6312_, v___x_6346_);
                if v___x_6347_ == 0 {
                    v___y_6374_ = v___x_6347_;
                    state = 10;
                    continue;
                } else {
                    v___x_6410_ = l_Lean_trace_profiler_useHeartbeats;
                    v___x_6411_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_opts_6312_, v___x_6410_);
                    if v___x_6411_ == 0 {
                        v___x_6412_ = l_Lean_trace_profiler_threshold;
                        v___x_6413_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5(v_opts_6312_, v___x_6412_);
                        v___x_6414_ = lean_float_of_nat(v___x_6413_);
                        v___x_6415_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3);
                        v___x_6416_ = lean_float_div(v___x_6414_, v___x_6415_);
                        v___y_6405_ = v___x_6416_;
                        state = 15;
                        continue;
                    } else {
                        v___x_6417_ = l_Lean_trace_profiler_threshold;
                        v___x_6418_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5(v_opts_6312_, v___x_6417_);
                        v___x_6419_ = lean_float_of_nat(v___x_6418_);
                        v___y_6405_ = v___x_6419_;
                        state = 15;
                        continue;
                    }
                }
            }
            6 => {
                v_result_6351_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4_spec__4(v_fst_6322_);
                v___x_6352_ = l_Lean_TraceResult_toEmoji(v_result_6351_);
                v___x_6353_ = l_Lean_stringToMessageData(v___x_6352_);
                v___x_6354_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__3_once), _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__3);
                if v_isShared_6345_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6344_, 7);
                    crate::leanh::lean_ctor_set(v___x_6344_, 1, v___x_6354_);
                    crate::leanh::lean_ctor_set(v___x_6344_, 0, v___x_6353_);
                    v___x_6356_ = v___x_6344_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6367_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6367_, 0, v___x_6353_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6367_, 1, v___x_6354_);
                    v___x_6356_ = v_reuseFailAlloc_6367_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_6326_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6325_, 7);
                    crate::leanh::lean_ctor_set(v___x_6325_, 1, v_a_6350_);
                    crate::leanh::lean_ctor_set(v___x_6325_, 0, v___x_6356_);
                    v_m_6358_ = v___x_6325_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6366_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6366_, 0, v___x_6356_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6366_, 1, v_a_6350_);
                    v_m_6358_ = v_reuseFailAlloc_6366_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_6359_ = crate::leanh::lean_box((v_result_6351_) as usize);
                v___x_6360_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6360_, 0, v___x_6359_);
                v___x_6361_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0);
                crate::leanh::lean_inc_ref(v_tag_6311_);
                crate::leanh::lean_inc_ref(v___x_6360_);
                crate::leanh::lean_inc(v_cls_6309_);
                v_data_6362_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v_data_6362_, 0, v_cls_6309_);
                crate::leanh::lean_ctor_set(v_data_6362_, 1, v___x_6360_);
                crate::leanh::lean_ctor_set(v_data_6362_, 2, v_tag_6311_);
                crate::leanh::lean_ctor_set_float(
                    v_data_6362_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_6361_,
                );
                crate::leanh::lean_ctor_set_float(
                    v_data_6362_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_6361_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v_data_6362_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v_collapsed_6310_,
                );
                if v___x_6347_ == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_6360_, 1);
                    crate::leanh::lean_dec(v_snd_6342_);
                    crate::leanh::lean_dec(v_fst_6341_);
                    crate::leanh::lean_dec_ref(v_tag_6311_);
                    crate::leanh::lean_dec(v_cls_6309_);
                    v___y_6328_ = v___y_6349_;
                    v___y_6329_ = v_m_6358_;
                    v_data_6330_ = v_data_6362_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref_known(v_data_6362_, 3);
                    v_data_6363_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                    crate::leanh::lean_ctor_set(v_data_6363_, 0, v_cls_6309_);
                    crate::leanh::lean_ctor_set(v_data_6363_, 1, v___x_6360_);
                    crate::leanh::lean_ctor_set(v_data_6363_, 2, v_tag_6311_);
                    v___x_6364_ = crate::leanh::lean_unbox_float(v_fst_6341_);
                    crate::leanh::lean_dec(v_fst_6341_);
                    crate::leanh::lean_ctor_set_float(
                        v_data_6363_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v___x_6364_,
                    );
                    v___x_6365_ = crate::leanh::lean_unbox_float(v_snd_6342_);
                    crate::leanh::lean_dec(v_snd_6342_);
                    crate::leanh::lean_ctor_set_float(
                        v_data_6363_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                        v___x_6365_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_data_6363_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                        v_collapsed_6310_,
                    );
                    v___y_6328_ = v___y_6349_;
                    v___y_6329_ = v_m_6358_;
                    v_data_6330_ = v_data_6363_;
                    state = 2;
                    continue;
                }
            }
            9 => {
                v_ref_6369_ = crate::leanh::lean_ctor_get(v___y_6319_, 5);
                crate::leanh::lean_inc(v___y_6320_);
                crate::leanh::lean_inc_ref(v___y_6319_);
                crate::leanh::lean_inc(v___y_6318_);
                crate::leanh::lean_inc_ref(v___y_6317_);
                crate::leanh::lean_inc(v_fst_6322_);
                v___x_6370_ = crate::leanh::lean_apply_6(
                    v_msg_6315_,
                    v_fst_6322_,
                    v___y_6317_,
                    v___y_6318_,
                    v___y_6319_,
                    v___y_6320_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_6370_) == 0 {
                    v_a_6371_ = crate::leanh::lean_ctor_get(v___x_6370_, 0);
                    crate::leanh::lean_inc(v_a_6371_);
                    crate::leanh::lean_dec_ref_known(v___x_6370_, 1);
                    v___y_6349_ = v_ref_6369_;
                    v_a_6350_ = v_a_6371_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_6370_, 1);
                    v___x_6372_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2);
                    v___y_6349_ = v_ref_6369_;
                    v_a_6350_ = v___x_6372_;
                    state = 6;
                    continue;
                }
            }
            10 => {
                if v_clsEnabled_6313_ == 0 {
                    if v___y_6374_ == 0 {
                        crate::leanh::lean_del_object(v___x_6344_);
                        crate::leanh::lean_dec(v_snd_6342_);
                        crate::leanh::lean_dec(v_fst_6341_);
                        crate::leanh::lean_del_object(v___x_6325_);
                        crate::leanh::lean_dec_ref(v_msg_6315_);
                        crate::leanh::lean_dec_ref(v_tag_6311_);
                        crate::leanh::lean_dec(v_cls_6309_);
                        v___x_6375_ = lean_st_ref_take(v___y_6320_);
                        v_traceState_6376_ = crate::leanh::lean_ctor_get(v___x_6375_, 4);
                        v_env_6377_ = crate::leanh::lean_ctor_get(v___x_6375_, 0);
                        v_nextMacroScope_6378_ = crate::leanh::lean_ctor_get(v___x_6375_, 1);
                        v_ngen_6379_ = crate::leanh::lean_ctor_get(v___x_6375_, 2);
                        v_auxDeclNGen_6380_ = crate::leanh::lean_ctor_get(v___x_6375_, 3);
                        v_cache_6381_ = crate::leanh::lean_ctor_get(v___x_6375_, 5);
                        v_messages_6382_ = crate::leanh::lean_ctor_get(v___x_6375_, 6);
                        v_infoState_6383_ = crate::leanh::lean_ctor_get(v___x_6375_, 7);
                        v_snapshotTasks_6384_ = crate::leanh::lean_ctor_get(v___x_6375_, 8);
                        v_isSharedCheck_6403_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6375_)) as u8;
                        if v_isSharedCheck_6403_ == 0 {
                            v___x_6386_ = v___x_6375_;
                            v_isShared_6387_ = v_isSharedCheck_6403_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snapshotTasks_6384_);
                            crate::leanh::lean_inc(v_infoState_6383_);
                            crate::leanh::lean_inc(v_messages_6382_);
                            crate::leanh::lean_inc(v_cache_6381_);
                            crate::leanh::lean_inc(v_traceState_6376_);
                            crate::leanh::lean_inc(v_auxDeclNGen_6380_);
                            crate::leanh::lean_inc(v_ngen_6379_);
                            crate::leanh::lean_inc(v_nextMacroScope_6378_);
                            crate::leanh::lean_inc(v_env_6377_);
                            crate::leanh::lean_dec(v___x_6375_);
                            v___x_6386_ = crate::leanh::lean_box(0);
                            v_isShared_6387_ = v_isSharedCheck_6403_;
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
                v_tid_6388_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_6376_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_6389_ = crate::leanh::lean_ctor_get(v_traceState_6376_, 0);
                v_isSharedCheck_6402_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_6376_)) as u8;
                if v_isSharedCheck_6402_ == 0 {
                    v___x_6391_ = v_traceState_6376_;
                    v_isShared_6392_ = v_isSharedCheck_6402_;
                    state = 12;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_6389_);
                    crate::leanh::lean_dec(v_traceState_6376_);
                    v___x_6391_ = crate::leanh::lean_box(0);
                    v_isShared_6392_ = v_isSharedCheck_6402_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_6393_ =
                    l_Lean_PersistentArray_append___redArg(v_oldTraces_6314_, v_traces_6389_);
                crate::leanh::lean_dec_ref(v_traces_6389_);
                if v_isShared_6392_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6391_, 0, v___x_6393_);
                    v___x_6395_ = v___x_6391_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_6401_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6401_, 0, v___x_6393_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_6401_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_6388_,
                    );
                    v___x_6395_ = v_reuseFailAlloc_6401_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_6387_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6386_, 4, v___x_6395_);
                    v___x_6397_ = v___x_6386_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_6400_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6400_, 0, v_env_6377_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6400_, 1, v_nextMacroScope_6378_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6400_, 2, v_ngen_6379_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6400_, 3, v_auxDeclNGen_6380_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6400_, 4, v___x_6395_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6400_, 5, v_cache_6381_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6400_, 6, v_messages_6382_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6400_, 7, v_infoState_6383_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6400_, 8, v_snapshotTasks_6384_);
                    v___x_6397_ = v_reuseFailAlloc_6400_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_6398_ = lean_st_ref_set(v___y_6320_, v___x_6397_);
                v___x_6399_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__4___redArg(v_fst_6322_);
                return v___x_6399_;
            }
            15 => {
                v___x_6406_ = crate::leanh::lean_unbox_float(v_snd_6342_);
                v___x_6407_ = crate::leanh::lean_unbox_float(v_fst_6341_);
                v___x_6408_ = lean_float_sub(v___x_6406_, v___x_6407_);
                v___x_6409_ = lean_float_decLt(v___y_6405_, v___x_6408_);
                v___y_6374_ = v___x_6409_;
                state = 10;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4___boxed(
    mut v_cls_6422_: *mut crate::leanh::LeanObject,
    mut v_collapsed_6423_: *mut crate::leanh::LeanObject,
    mut v_tag_6424_: *mut crate::leanh::LeanObject,
    mut v_opts_6425_: *mut crate::leanh::LeanObject,
    mut v_clsEnabled_6426_: *mut crate::leanh::LeanObject,
    mut v_oldTraces_6427_: *mut crate::leanh::LeanObject,
    mut v_msg_6428_: *mut crate::leanh::LeanObject,
    mut v_resStartStop_6429_: *mut crate::leanh::LeanObject,
    mut v___y_6430_: *mut crate::leanh::LeanObject,
    mut v___y_6431_: *mut crate::leanh::LeanObject,
    mut v___y_6432_: *mut crate::leanh::LeanObject,
    mut v___y_6433_: *mut crate::leanh::LeanObject,
    mut v___y_6434_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_collapsed_boxed_6435_: u8 = 0;
    let mut v_clsEnabled_boxed_6436_: u8 = 0;
    let mut v_res_6437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_6435_ = (crate::leanh::lean_unbox(v_collapsed_6423_) as u8);
    v_clsEnabled_boxed_6436_ = (crate::leanh::lean_unbox(v_clsEnabled_6426_) as u8);
    v_res_6437_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4(v_cls_6422_, v_collapsed_boxed_6435_, v_tag_6424_, v_opts_6425_, v_clsEnabled_boxed_6436_, v_oldTraces_6427_, v_msg_6428_, v_resStartStop_6429_, v___y_6430_, v___y_6431_, v___y_6432_, v___y_6433_);
    crate::leanh::lean_dec(v___y_6433_);
    crate::leanh::lean_dec_ref(v___y_6432_);
    crate::leanh::lean_dec(v___y_6431_);
    crate::leanh::lean_dec_ref(v___y_6430_);
    crate::leanh::lean_dec_ref(v_opts_6425_);
    return v_res_6437_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27(
    mut v_goal_6441_: *mut crate::leanh::LeanObject,
    mut v_tactic_6442_: *mut crate::leanh::LeanObject,
    mut v_allowFailure_6443_: *mut crate::leanh::LeanObject,
    mut v_leavePercentHeartbeats_6444_: *mut crate::leanh::LeanObject,
    mut v_includeStar_6445_: u8,
    mut v_collectAll_6446_: u8,
    mut v_a_6447_: *mut crate::leanh::LeanObject,
    mut v_a_6448_: *mut crate::leanh::LeanObject,
    mut v_a_6449_: *mut crate::leanh::LeanObject,
    mut v_a_6450_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_6452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_6453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_6454_: u8 = 0;
    let mut v___x_6455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6466_: u8 = 0;
    let mut v___y_6468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6472_: f64 = 0.0;
    let mut v___x_6473_: f64 = 0.0;
    let mut v___x_6474_: f64 = 0.0;
    let mut v___x_6475_: f64 = 0.0;
    let mut v___x_6476_: f64 = 0.0;
    let mut v___x_6477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6487_: f64 = 0.0;
    let mut v___x_6488_: f64 = 0.0;
    let mut v___x_6489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6498_: u8 = 0;
    let mut v___x_6499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6500_: u8 = 0;
    let mut v___x_6501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6511_: u8 = 0;
    let mut v___x_6513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6515_: u8 = 0;
    let mut v_a_6516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6519_: u8 = 0;
    let mut v___x_6521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6523_: u8 = 0;
    let mut v___x_6524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6525_: u8 = 0;
    let mut v___x_6526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6536_: u8 = 0;
    let mut v___x_6538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6540_: u8 = 0;
    let mut v_a_6541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6544_: u8 = 0;
    let mut v___x_6546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6548_: u8 = 0;
    let mut v___x_6549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6550_: u8 = 0;
    let mut v___x_6551_: u8 = 0;
    let mut v___x_6552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_6452_ = crate::leanh::lean_ctor_get(v_a_6449_, 2);
                v_inheritedTraceOptions_6453_ = crate::leanh::lean_ctor_get(v_a_6449_, 13);
                v_hasTrace_6454_ = crate::leanh::lean_ctor_get_uint8(
                    v_options_6452_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v___x_6455_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__1_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_;
                if v_hasTrace_6454_ == 0 {
                    v___x_6456_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___closed__0;
                    v___x_6457_ = crate::leanh::lean_box((v_collectAll_6446_) as usize);
                    v___x_6458_ = crate::leanh::lean_box((v_includeStar_6445_) as usize);
                    v___f_6459_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1___boxed as *mut core::ffi::c_void, 12, 7);
                    crate::leanh::lean_closure_set(v___f_6459_, 0, v_leavePercentHeartbeats_6444_);
                    crate::leanh::lean_closure_set(v___f_6459_, 1, v_goal_6441_);
                    crate::leanh::lean_closure_set(v___f_6459_, 2, v___x_6456_);
                    crate::leanh::lean_closure_set(v___f_6459_, 3, v_tactic_6442_);
                    crate::leanh::lean_closure_set(v___f_6459_, 4, v_allowFailure_6443_);
                    crate::leanh::lean_closure_set(v___f_6459_, 5, v___x_6457_);
                    crate::leanh::lean_closure_set(v___f_6459_, 6, v___x_6458_);
                    v___x_6460_ = crate::leanh::lean_box(0);
                    v___x_6461_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(v___x_6455_, v_options_6452_, v___f_6459_, v___x_6460_, v_a_6447_, v_a_6448_, v_a_6449_, v_a_6450_);
                    return v___x_6461_;
                } else {
                    crate::leanh::lean_inc(v_goal_6441_);
                    v___f_6462_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__2___boxed as *mut core::ffi::c_void, 7, 1);
                    crate::leanh::lean_closure_set(v___f_6462_, 0, v_goal_6441_);
                    v___x_6463_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__2_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_;
                    v___x_6464_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__4;
                    v___x_6465_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2_once), _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2);
                    v___x_6466_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_6453_,
                        v_options_6452_,
                        v___x_6465_,
                    );
                    if v___x_6466_ == 0 {
                        v___x_6549_ = l_Lean_trace_profiler;
                        v___x_6550_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_options_6452_, v___x_6549_);
                        if v___x_6550_ == 0 {
                            crate::leanh::lean_dec_ref(v___f_6462_);
                            v___x_6551_ = 0;
                            v___x_6552_ = crate::leanh::lean_alloc_ctor(0, 0, (4) as u32);
                            crate::leanh::lean_ctor_set_uint8(v___x_6552_, 0 as u32, v___x_6551_);
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_6552_,
                                1 as u32,
                                v_hasTrace_6454_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_6552_,
                                2 as u32,
                                v_hasTrace_6454_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_6552_,
                                3 as u32,
                                v_hasTrace_6454_,
                            );
                            v___x_6553_ = crate::leanh::lean_box((v_collectAll_6446_) as usize);
                            v___x_6554_ = crate::leanh::lean_box((v_includeStar_6445_) as usize);
                            v___x_6555_ = crate::leanh::lean_box((v___x_6550_) as usize);
                            v___f_6556_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__4___boxed as *mut core::ffi::c_void, 13, 8);
                            crate::leanh::lean_closure_set(
                                v___f_6556_,
                                0,
                                v_leavePercentHeartbeats_6444_,
                            );
                            crate::leanh::lean_closure_set(v___f_6556_, 1, v_goal_6441_);
                            crate::leanh::lean_closure_set(v___f_6556_, 2, v___x_6552_);
                            crate::leanh::lean_closure_set(v___f_6556_, 3, v_tactic_6442_);
                            crate::leanh::lean_closure_set(v___f_6556_, 4, v_allowFailure_6443_);
                            crate::leanh::lean_closure_set(v___f_6556_, 5, v___x_6553_);
                            crate::leanh::lean_closure_set(v___f_6556_, 6, v___x_6554_);
                            crate::leanh::lean_closure_set(v___f_6556_, 7, v___x_6555_);
                            v___x_6557_ = crate::leanh::lean_box(0);
                            v___x_6558_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(v___x_6455_, v_options_6452_, v___f_6556_, v___x_6557_, v_a_6447_, v_a_6448_, v_a_6449_, v_a_6450_);
                            return v___x_6558_;
                        } else {
                            state = 3;
                            continue;
                        }
                    } else {
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6471_ = lean_io_mono_nanos_now();
                v___x_6472_ = lean_float_of_nat(v___y_6468_);
                v___x_6473_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3_once), _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3);
                v___x_6474_ = lean_float_div(v___x_6472_, v___x_6473_);
                v___x_6475_ = lean_float_of_nat(v___x_6471_);
                v___x_6476_ = lean_float_div(v___x_6475_, v___x_6473_);
                v___x_6477_ = crate::leanh::lean_box_float(v___x_6474_);
                v___x_6478_ = crate::leanh::lean_box_float(v___x_6476_);
                v___x_6479_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6479_, 0, v___x_6477_);
                crate::leanh::lean_ctor_set(v___x_6479_, 1, v___x_6478_);
                v___x_6480_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6480_, 0, v_a_6470_);
                crate::leanh::lean_ctor_set(v___x_6480_, 1, v___x_6479_);
                v___x_6481_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4(v___x_6463_, v_hasTrace_6454_, v___x_6464_, v_options_6452_, v___x_6466_, v___y_6469_, v___f_6462_, v___x_6480_, v_a_6447_, v_a_6448_, v_a_6449_, v_a_6450_);
                return v___x_6481_;
            }
            2 => {
                v___x_6486_ = lean_io_get_num_heartbeats();
                v___x_6487_ = lean_float_of_nat(v___y_6483_);
                v___x_6488_ = lean_float_of_nat(v___x_6486_);
                v___x_6489_ = crate::leanh::lean_box_float(v___x_6487_);
                v___x_6490_ = crate::leanh::lean_box_float(v___x_6488_);
                v___x_6491_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6491_, 0, v___x_6489_);
                crate::leanh::lean_ctor_set(v___x_6491_, 1, v___x_6490_);
                v___x_6492_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6492_, 0, v_a_6485_);
                crate::leanh::lean_ctor_set(v___x_6492_, 1, v___x_6491_);
                v___x_6493_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4(v___x_6463_, v_hasTrace_6454_, v___x_6464_, v_options_6452_, v___x_6466_, v___y_6484_, v___f_6462_, v___x_6492_, v_a_6447_, v_a_6448_, v_a_6449_, v_a_6450_);
                return v___x_6493_;
            }
            3 => {
                v___x_6495_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg(v_a_6450_);
                v_a_6496_ = crate::leanh::lean_ctor_get(v___x_6495_, 0);
                crate::leanh::lean_inc(v_a_6496_);
                crate::leanh::lean_dec_ref(v___x_6495_);
                v___x_6497_ = l_Lean_trace_profiler_useHeartbeats;
                v___x_6498_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_options_6452_, v___x_6497_);
                if v___x_6498_ == 0 {
                    v___x_6499_ = lean_io_mono_nanos_now();
                    v___x_6500_ = 0;
                    v___x_6501_ = crate::leanh::lean_alloc_ctor(0, 0, (4) as u32);
                    crate::leanh::lean_ctor_set_uint8(v___x_6501_, 0 as u32, v___x_6500_);
                    crate::leanh::lean_ctor_set_uint8(v___x_6501_, 1 as u32, v_hasTrace_6454_);
                    crate::leanh::lean_ctor_set_uint8(v___x_6501_, 2 as u32, v_hasTrace_6454_);
                    crate::leanh::lean_ctor_set_uint8(v___x_6501_, 3 as u32, v_hasTrace_6454_);
                    v___x_6502_ = crate::leanh::lean_box((v_collectAll_6446_) as usize);
                    v___x_6503_ = crate::leanh::lean_box((v_includeStar_6445_) as usize);
                    v___x_6504_ = crate::leanh::lean_box((v___x_6498_) as usize);
                    v___f_6505_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__4___boxed as *mut core::ffi::c_void, 13, 8);
                    crate::leanh::lean_closure_set(v___f_6505_, 0, v_leavePercentHeartbeats_6444_);
                    crate::leanh::lean_closure_set(v___f_6505_, 1, v_goal_6441_);
                    crate::leanh::lean_closure_set(v___f_6505_, 2, v___x_6501_);
                    crate::leanh::lean_closure_set(v___f_6505_, 3, v_tactic_6442_);
                    crate::leanh::lean_closure_set(v___f_6505_, 4, v_allowFailure_6443_);
                    crate::leanh::lean_closure_set(v___f_6505_, 5, v___x_6502_);
                    crate::leanh::lean_closure_set(v___f_6505_, 6, v___x_6503_);
                    crate::leanh::lean_closure_set(v___f_6505_, 7, v___x_6504_);
                    v___x_6506_ = crate::leanh::lean_box(0);
                    v___x_6507_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(v___x_6455_, v_options_6452_, v___f_6505_, v___x_6506_, v_a_6447_, v_a_6448_, v_a_6449_, v_a_6450_);
                    if crate::leanh::lean_obj_tag(v___x_6507_) == 0 {
                        v_a_6508_ = crate::leanh::lean_ctor_get(v___x_6507_, 0);
                        v_isSharedCheck_6515_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6507_)) as u8;
                        if v_isSharedCheck_6515_ == 0 {
                            v___x_6510_ = v___x_6507_;
                            v_isShared_6511_ = v_isSharedCheck_6515_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6508_);
                            crate::leanh::lean_dec(v___x_6507_);
                            v___x_6510_ = crate::leanh::lean_box(0);
                            v_isShared_6511_ = v_isSharedCheck_6515_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v_a_6516_ = crate::leanh::lean_ctor_get(v___x_6507_, 0);
                        v_isSharedCheck_6523_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6507_)) as u8;
                        if v_isSharedCheck_6523_ == 0 {
                            v___x_6518_ = v___x_6507_;
                            v_isShared_6519_ = v_isSharedCheck_6523_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6516_);
                            crate::leanh::lean_dec(v___x_6507_);
                            v___x_6518_ = crate::leanh::lean_box(0);
                            v_isShared_6519_ = v_isSharedCheck_6523_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    v___x_6524_ = lean_io_get_num_heartbeats();
                    v___x_6525_ = 0;
                    v___x_6526_ = crate::leanh::lean_alloc_ctor(0, 0, (4) as u32);
                    crate::leanh::lean_ctor_set_uint8(v___x_6526_, 0 as u32, v___x_6525_);
                    crate::leanh::lean_ctor_set_uint8(v___x_6526_, 1 as u32, v___x_6498_);
                    crate::leanh::lean_ctor_set_uint8(v___x_6526_, 2 as u32, v___x_6498_);
                    crate::leanh::lean_ctor_set_uint8(v___x_6526_, 3 as u32, v___x_6498_);
                    v___x_6527_ = crate::leanh::lean_box((v_collectAll_6446_) as usize);
                    v___x_6528_ = crate::leanh::lean_box((v_includeStar_6445_) as usize);
                    v___x_6529_ = crate::leanh::lean_box((v___x_6498_) as usize);
                    v___f_6530_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__5___boxed as *mut core::ffi::c_void, 13, 8);
                    crate::leanh::lean_closure_set(v___f_6530_, 0, v_leavePercentHeartbeats_6444_);
                    crate::leanh::lean_closure_set(v___f_6530_, 1, v_goal_6441_);
                    crate::leanh::lean_closure_set(v___f_6530_, 2, v___x_6526_);
                    crate::leanh::lean_closure_set(v___f_6530_, 3, v_tactic_6442_);
                    crate::leanh::lean_closure_set(v___f_6530_, 4, v_allowFailure_6443_);
                    crate::leanh::lean_closure_set(v___f_6530_, 5, v___x_6527_);
                    crate::leanh::lean_closure_set(v___f_6530_, 6, v___x_6528_);
                    crate::leanh::lean_closure_set(v___f_6530_, 7, v___x_6529_);
                    v___x_6531_ = crate::leanh::lean_box(0);
                    v___x_6532_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(v___x_6455_, v_options_6452_, v___f_6530_, v___x_6531_, v_a_6447_, v_a_6448_, v_a_6449_, v_a_6450_);
                    if crate::leanh::lean_obj_tag(v___x_6532_) == 0 {
                        v_a_6533_ = crate::leanh::lean_ctor_get(v___x_6532_, 0);
                        v_isSharedCheck_6540_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6532_)) as u8;
                        if v_isSharedCheck_6540_ == 0 {
                            v___x_6535_ = v___x_6532_;
                            v_isShared_6536_ = v_isSharedCheck_6540_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6533_);
                            crate::leanh::lean_dec(v___x_6532_);
                            v___x_6535_ = crate::leanh::lean_box(0);
                            v_isShared_6536_ = v_isSharedCheck_6540_;
                            state = 8;
                            continue;
                        }
                    } else {
                        v_a_6541_ = crate::leanh::lean_ctor_get(v___x_6532_, 0);
                        v_isSharedCheck_6548_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6532_)) as u8;
                        if v_isSharedCheck_6548_ == 0 {
                            v___x_6543_ = v___x_6532_;
                            v_isShared_6544_ = v_isSharedCheck_6548_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6541_);
                            crate::leanh::lean_dec(v___x_6532_);
                            v___x_6543_ = crate::leanh::lean_box(0);
                            v_isShared_6544_ = v_isSharedCheck_6548_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            4 => {
                if v_isShared_6511_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6510_, 1);
                    v___x_6513_ = v___x_6510_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6514_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6514_, 0, v_a_6508_);
                    v___x_6513_ = v_reuseFailAlloc_6514_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___y_6468_ = v___x_6499_;
                v___y_6469_ = v_a_6496_;
                v_a_6470_ = v___x_6513_;
                state = 1;
                continue;
            }
            6 => {
                if v_isShared_6519_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6518_, 0);
                    v___x_6521_ = v___x_6518_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6522_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6522_, 0, v_a_6516_);
                    v___x_6521_ = v_reuseFailAlloc_6522_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_6468_ = v___x_6499_;
                v___y_6469_ = v_a_6496_;
                v_a_6470_ = v___x_6521_;
                state = 1;
                continue;
            }
            8 => {
                if v_isShared_6536_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6535_, 1);
                    v___x_6538_ = v___x_6535_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6539_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6539_, 0, v_a_6533_);
                    v___x_6538_ = v_reuseFailAlloc_6539_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___y_6483_ = v___x_6524_;
                v___y_6484_ = v_a_6496_;
                v_a_6485_ = v___x_6538_;
                state = 2;
                continue;
            }
            10 => {
                if v_isShared_6544_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6543_, 0);
                    v___x_6546_ = v___x_6543_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_6547_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6547_, 0, v_a_6541_);
                    v___x_6546_ = v_reuseFailAlloc_6547_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___y_6483_ = v___x_6524_;
                v___y_6484_ = v_a_6496_;
                v_a_6485_ = v___x_6546_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___boxed(
    mut v_goal_6559_: *mut crate::leanh::LeanObject,
    mut v_tactic_6560_: *mut crate::leanh::LeanObject,
    mut v_allowFailure_6561_: *mut crate::leanh::LeanObject,
    mut v_leavePercentHeartbeats_6562_: *mut crate::leanh::LeanObject,
    mut v_includeStar_6563_: *mut crate::leanh::LeanObject,
    mut v_collectAll_6564_: *mut crate::leanh::LeanObject,
    mut v_a_6565_: *mut crate::leanh::LeanObject,
    mut v_a_6566_: *mut crate::leanh::LeanObject,
    mut v_a_6567_: *mut crate::leanh::LeanObject,
    mut v_a_6568_: *mut crate::leanh::LeanObject,
    mut v_a_6569_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_includeStar_boxed_6570_: u8 = 0;
    let mut v_collectAll_boxed_6571_: u8 = 0;
    let mut v_res_6572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_includeStar_boxed_6570_ = (crate::leanh::lean_unbox(v_includeStar_6563_) as u8);
    v_collectAll_boxed_6571_ = (crate::leanh::lean_unbox(v_collectAll_6564_) as u8);
    v_res_6572_ =
        l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27(
            v_goal_6559_,
            v_tactic_6560_,
            v_allowFailure_6561_,
            v_leavePercentHeartbeats_6562_,
            v_includeStar_boxed_6570_,
            v_collectAll_boxed_6571_,
            v_a_6565_,
            v_a_6566_,
            v_a_6567_,
            v_a_6568_,
        );
    crate::leanh::lean_dec(v_a_6568_);
    crate::leanh::lean_dec_ref(v_a_6567_);
    crate::leanh::lean_dec(v_a_6566_);
    crate::leanh::lean_dec_ref(v_a_6565_);
    return v_res_6572_;
}
pub unsafe fn l_Lean_Meta_LibrarySearch_librarySearch(
    mut v_goal_6573_: *mut crate::leanh::LeanObject,
    mut v_tactic_6574_: *mut crate::leanh::LeanObject,
    mut v_allowFailure_6575_: *mut crate::leanh::LeanObject,
    mut v_leavePercentHeartbeats_6576_: *mut crate::leanh::LeanObject,
    mut v_includeStar_6577_: u8,
    mut v_collectAll_6578_: u8,
    mut v_a_6579_: *mut crate::leanh::LeanObject,
    mut v_a_6580_: *mut crate::leanh::LeanObject,
    mut v_a_6581_: *mut crate::leanh::LeanObject,
    mut v_a_6582_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6584_ =
        l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27(
            v_goal_6573_,
            v_tactic_6574_,
            v_allowFailure_6575_,
            v_leavePercentHeartbeats_6576_,
            v_includeStar_6577_,
            v_collectAll_6578_,
            v_a_6579_,
            v_a_6580_,
            v_a_6581_,
            v_a_6582_,
        );
    return v___x_6584_;
}
pub unsafe fn l_Lean_Meta_LibrarySearch_librarySearch___boxed(
    mut v_goal_6585_: *mut crate::leanh::LeanObject,
    mut v_tactic_6586_: *mut crate::leanh::LeanObject,
    mut v_allowFailure_6587_: *mut crate::leanh::LeanObject,
    mut v_leavePercentHeartbeats_6588_: *mut crate::leanh::LeanObject,
    mut v_includeStar_6589_: *mut crate::leanh::LeanObject,
    mut v_collectAll_6590_: *mut crate::leanh::LeanObject,
    mut v_a_6591_: *mut crate::leanh::LeanObject,
    mut v_a_6592_: *mut crate::leanh::LeanObject,
    mut v_a_6593_: *mut crate::leanh::LeanObject,
    mut v_a_6594_: *mut crate::leanh::LeanObject,
    mut v_a_6595_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_includeStar_boxed_6596_: u8 = 0;
    let mut v_collectAll_boxed_6597_: u8 = 0;
    let mut v_res_6598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_includeStar_boxed_6596_ = (crate::leanh::lean_unbox(v_includeStar_6589_) as u8);
    v_collectAll_boxed_6597_ = (crate::leanh::lean_unbox(v_collectAll_6590_) as u8);
    v_res_6598_ = l_Lean_Meta_LibrarySearch_librarySearch(
        v_goal_6585_,
        v_tactic_6586_,
        v_allowFailure_6587_,
        v_leavePercentHeartbeats_6588_,
        v_includeStar_boxed_6596_,
        v_collectAll_boxed_6597_,
        v_a_6591_,
        v_a_6592_,
        v_a_6593_,
        v_a_6594_,
    );
    crate::leanh::lean_dec(v_a_6594_);
    crate::leanh::lean_dec_ref(v_a_6593_);
    crate::leanh::lean_dec(v_a_6592_);
    crate::leanh::lean_dec_ref(v_a_6591_);
    return v_res_6598_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_LibrarySearch(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_LazyDiscrTree(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_SolveByElim(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Main(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_Heartbeats(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Try(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Meta_LibrarySearch_instInhabitedDeclMod_default =
        _init_l_Lean_Meta_LibrarySearch_instInhabitedDeclMod_default();
    l_Lean_Meta_LibrarySearch_instInhabitedDeclMod =
        _init_l_Lean_Meta_LibrarySearch_instInhabitedDeclMod();
    res = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_641666102____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_defaultLibSearchState =
        crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(
        l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_defaultLibSearchState,
    );
    crate::leanh::lean_dec_ref(res);
    l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_instInhabitedLibSearchState = _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_instInhabitedLibSearchState();
    crate::leanh::lean_mark_persistent(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_instInhabitedLibSearchState);
    res = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_2561004661____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_ext =
        crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(
        l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_ext,
    );
    crate::leanh::lean_dec_ref(res);
    l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_constantsPerImportTask = _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_constantsPerImportTask();
    crate::leanh::lean_mark_persistent(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_constantsPerImportTask);
    res = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_956453063____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_starLemmasExt =
        crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(
        l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_starLemmasExt,
    );
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_989218885____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_abortSpeculationId =
        crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(
        l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_abortSpeculationId,
    );
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_LibrarySearch(
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
pub unsafe fn initialize_Lean_Meta_Tactic_LibrarySearch(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_LazyDiscrTree(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_SolveByElim(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Main(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Util_Heartbeats(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Grind_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Try(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_LibrarySearch(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_LibrarySearch(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_LibrarySearch(builtin);
}
