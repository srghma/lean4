// Lean compiler output
// Module: Lean.Elab.ConfigEval.Util
// Imports: Lean.Elab.Command
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_fswap, lean_array_get,
    lean_array_get_borrowed, lean_array_get_size, lean_array_push, lean_array_size,
    lean_array_to_list, lean_array_uget, lean_array_uget_borrowed, lean_array_uset, lean_expr_eqv,
    lean_float_decLt, lean_float_div, lean_float_sub, lean_infer_type, lean_io_get_num_heartbeats,
    lean_io_mono_nanos_now, lean_mk_array, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_shiftr,
    lean_nat_sub, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take, lean_string_dec_lt,
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_add,
    lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_land, lean_usize_of_nat, lean_usize_sub,
    lean_whnf,
};
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::List::BasicAux::l_List_head_x21___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Meta::Defs::l_Lean_Syntax_mkStrLit;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_node3, l_Lean_Syntax_node6,
    l_Lean_maxRecDepthErrorMessage, l_Lean_replaceRef,
};
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_withFreshMacroScope___redArg, l_Lean_Exception_isRuntime,
};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::PersistentArray::{
    l_Lean_PersistentArray_append___redArg, l_Lean_PersistentArray_push___redArg,
    l_Lean_PersistentArray_toArray___redArg,
};
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Elab::Command::Scope::l_Lean_Elab_Command_instInhabitedScope_default;
use crate::r#gen::Lean::Elab::Command::{
    initialize_Lean_Elab_Command, l_Lean_Elab_Command_elabCommand,
    l_Lean_Elab_Command_getRef___redArg, l_Lean_Elab_Command_liftTermElabM___redArg,
    runtime_initialize_Lean_Elab_Command,
};
use crate::r#gen::Lean::Elab::Term::TermElabM::l_Lean_Elab_Term_synthesizeInstMVarCore;
use crate::r#gen::Lean::Elab::Util::{l_Lean_Elab_getBetterRef, l_Lean_Elab_pp_macroStack};
use crate::r#gen::Lean::Exception::{l_Lean_Exception_isInterrupt, l_Lean_Exception_toMessageData};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appArg_x21, l_Lean_Expr_hasMVar, l_Lean_Expr_hash, l_Lean_Expr_isAppOfArity,
    l_Lean_Expr_mvarId_x21, l_Lean_instInhabitedExpr,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofFormat,
    l_Lean_MessageData_ofList, l_Lean_MessageData_ofSyntax, l_Lean_indentD,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::AppBuilder::l_Lean_Meta_mkAppM;
use crate::r#gen::Lean::Meta::Basic::{
    l_Lean_Meta_forallMetaTelescopeReducing, l_Lean_Meta_isExprDefEq,
};
use crate::r#gen::Lean::Meta::SynthInstance::l_Lean_Meta_SynthInstance_getInstances;
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Lean::Util::Trace::{
    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go, l_Lean_TraceResult_toEmoji,
    l_Lean_inheritedTraceOptions, l_Lean_registerTraceClass, l_Lean_trace_profiler,
    l_Lean_trace_profiler_threshold, l_Lean_trace_profiler_useHeartbeats,
};
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___closed__0_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [116, 101, 114, 109, 73, 102, 84, 104, 101, 110, 69, 108, 115, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject,14296711813398647265 as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___closed__2_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [105, 102, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___closed__3_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [116, 101, 114, 109, 95, 61, 61, 95, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___closed__3_value) as *mut leanh::LeanObject,1990087968466729753 as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___closed__5_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [61, 61, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___closed__6_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 104, 101, 110, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___closed__7_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [101, 108, 115, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___closed__7_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build___closed__0_value: leanh::LeanStringObject<1> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build___closed__1_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build___closed__0_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build___closed__2_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [116, 101, 114, 109, 95, 60, 95, 0]};
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build___closed__2_value) as *mut leanh::LeanObject,6883052497475924672 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build___closed__4_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [60, 0]};
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg___closed__0_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 117, 110, 116, 105, 109, 101, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg___closed__1_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg___closed__1_value) as *mut leanh::LeanObject;
static l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg___closed__0_value) as *mut leanh::LeanObject,7310567555909517314 as *mut leanh::LeanObject] };
pub static l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg___closed__1_value) as *mut leanh::LeanObject,273128857561458264 as *mut leanh::LeanObject] };
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___lam__0___closed__0_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___lam__0___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___lam__0___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___lam__0___closed__0_value) as *mut leanh::LeanObject,14231257465488249300 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___lam__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___lam__0___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__16___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__16___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__16___closed__0_value) as *mut leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__22___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__22___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__22___closed__1_value: leanh::LeanStringObject<16> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__22___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__22___closed__1_value) as *mut leanh::LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__22___closed__2_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__22___closed__1_value) as *mut leanh::LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__22___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__22___closed__2_value) as *mut leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__22___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__22___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18___redArg___closed__0_value: leanh::LeanStringObject<25> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18___redArg___closed__1_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18___redArg___closed__0_value) as *mut leanh::LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18___redArg___closed__1_value) as *mut leanh::LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg___closed__1_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg___closed__0_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [102, 97, 105, 108, 101, 100, 0]};
static mut l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__0_value: leanh::LeanStringObject<22> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [99, 121, 99, 108, 105, 99, 32, 100, 101, 112, 101, 110, 100, 101, 110, 99, 121, 32, 111, 110, 32, 0]};
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__2_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__3_value: leanh::LeanStringObject<31> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 31, m_capacity: 31, m_length: 30, m_data: [100, 101, 112, 101, 110, 100, 101, 110, 99, 121, 32, 104, 97, 115, 32, 109, 101, 116, 97, 118, 97, 114, 105, 97, 98, 108, 101, 115, 58, 32, 0]};
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__3_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__1_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [67, 111, 110, 102, 105, 103, 69, 118, 97, 108, 0]};
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__0_value) as *mut leanh::LeanObject,12843180897352504333 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__1_value) as *mut leanh::LeanObject,12243250833400551512 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__1___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__1___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__4_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [105, 110, 115, 116, 32, 102, 111, 114, 32, 96, 0]};
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__4_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__6_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [96, 32, 100, 101, 112, 115, 58, 32, 0]};
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__6_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__8_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 115, 116, 58, 32, 0]};
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__8_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__10_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [44, 32, 0]};
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__10_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__12_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [116, 114, 121, 73, 110, 115, 116, 32, 0]};
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__12_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__13_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__13: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__0_value: leanh::LeanStringObject<17> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [101, 120, 116, 114, 97, 32, 100, 101, 112, 115, 32, 102, 111, 114, 32, 96, 0]};
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__2_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [96, 58, 32, 0]};
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__4_value: leanh::LeanStringObject<16> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [110, 117, 109, 32, 105, 110, 115, 116, 115, 32, 102, 111, 114, 32, 96, 0]};
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__4_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__6_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [44, 32, 116, 121, 112, 101, 58, 32, 0]};
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__6_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__8_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [112, 108, 97, 110, 58, 32, 0]};
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__8_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__10_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [44, 32, 112, 114, 111, 99, 101, 115, 115, 105, 110, 103, 58, 32, 0]};
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__10_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___closed__0_value: leanh::LeanStringObject<18> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [100, 101, 114, 105, 118, 97, 116, 105, 111, 110, 32, 112, 108, 97, 110, 32, 96, 0]};
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___closed__2_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [96, 32, 102, 111, 114, 32, 96, 0]};
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___closed__0_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___closed__2_value: leanh::LeanStringObject<54> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [60, 101, 120, 99, 101, 112, 116, 105, 111, 110, 32, 116, 104, 114, 111, 119, 110, 32, 119, 104, 105, 108, 101, 32, 112, 114, 111, 100, 117, 99, 105, 110, 103, 32, 116, 114, 97, 99, 101, 32, 110, 111, 100, 101, 32, 109, 101, 115, 115, 97, 103, 101, 62, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___closed__4: f64 = 0.0;
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___closed__2: f64 = 0.0;
static mut l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___lam__0___closed__0_value: leanh::LeanStringObject<32> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 32, m_capacity: 32, m_length: 31, m_data: [102, 97, 105, 108, 117, 114, 101, 32, 100, 101, 114, 105, 118, 105, 110, 103, 32, 105, 110, 115, 116, 97, 110, 99, 101, 32, 102, 111, 114, 32, 96, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___lam__0___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___lam__0___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___lam__0___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__0_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [97, 100, 100, 101, 100, 32, 105, 110, 115, 116, 97, 110, 99, 101, 32, 111, 102, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__2_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [32, 102, 111, 114, 32, 32, 96, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__4_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__4_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__0_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__0_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__0_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__1_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__0_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11079354408986465895 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__1_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__1_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__2_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__2_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__2_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__3_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__1_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__2_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value) as *mut leanh::LeanObject,10352885018404983386 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__3_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__3_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__4_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__3_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__0_value) as *mut leanh::LeanObject,5444244426488757208 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__4_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__4_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__5_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__4_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__1_value) as *mut leanh::LeanObject,8105975667137788465 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__5_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__5_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__6_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [85, 116, 105, 108, 0]};
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__6_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__6_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__7_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__5_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__6_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value) as *mut leanh::LeanObject,16959765724646536291 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__7_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__7_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__8_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__7_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,4606381545185302062 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__8_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__8_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__9_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__8_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__2_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value) as *mut leanh::LeanObject,9308540624602620759 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__9_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__9_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__10_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__9_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__0_value) as *mut leanh::LeanObject,8958706626930197529 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__10_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__10_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__11_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__10_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__1_value) as *mut leanh::LeanObject,2553152521223443804 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__11_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__11_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__12_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__12_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__12_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__13_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__11_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__12_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value) as *mut leanh::LeanObject,2242150389412106985 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__13_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__13_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__14_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__14_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__14_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__15_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__13_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__14_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value) as *mut leanh::LeanObject,18290379954784180484 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__15_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__15_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__16_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__15_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__2_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15171864691763810277 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__16_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__16_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__17_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__16_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__0_value) as *mut leanh::LeanObject,5559384498376346067 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__17_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__17_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__18_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__17_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__1_value) as *mut leanh::LeanObject,1874224393281518878 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__18_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__18_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__19_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__18_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__6_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value) as *mut leanh::LeanObject,8941480450374017944 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__19_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__19_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__20_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__19_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 1975219684 as usize) << 1) | 1) as *mut leanh::LeanObject,5161896621287922084 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__20_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__20_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__21_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__21_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__21_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__22_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__20_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__21_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value) as *mut leanh::LeanObject,2640161792953404427 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__22_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__22_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__23_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__23_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__23_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__24_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__22_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__23_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value) as *mut leanh::LeanObject,16910171267688660811 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__24_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__24_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__25_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__24_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,183777009657404510 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__25_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__25_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg(
    mut v_discr_3037_: *mut leanh::LeanObject,
    mut v_as_3038_: *mut leanh::LeanObject,
    mut v_i_3039_: usize,
    mut v_stop_3040_: usize,
    mut v_b_3041_: *mut leanh::LeanObject,
    mut v___y_3042_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3044_: u8 = 0;
    let mut v___x_3045_: usize = 0;
    let mut v___x_3046_: usize = 0;
    let mut v___x_3047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3052_: u8 = 0;
    let mut v_ref_3053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3072_: u8 = 0;
    let mut v___x_3073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3044_ = lean_usize_dec_eq(v_i_3039_, v_stop_3040_);
                if v___x_3044_ == 0 {
                    v___x_3045_ = 1usize;
                    v___x_3046_ = lean_usize_sub(v_i_3039_, v___x_3045_);
                    v___x_3047_ = lean_array_uget(v_as_3038_, v___x_3046_);
                    v_fst_3048_ = leanh::lean_ctor_get(v___x_3047_, 0);
                    v_snd_3049_ = leanh::lean_ctor_get(v___x_3047_, 1);
                    v_isSharedCheck_3072_ = (!leanh::lean_is_exclusive(v___x_3047_)) as u8;
                    if v_isSharedCheck_3072_ == 0 {
                        v___x_3051_ = v___x_3047_;
                        v_isShared_3052_ = v_isSharedCheck_3072_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_3049_);
                        leanh::lean_inc(v_fst_3048_);
                        leanh::lean_dec(v___x_3047_);
                        v___x_3051_ = leanh::lean_box(0);
                        v_isShared_3052_ = v_isSharedCheck_3072_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_discr_3037_);
                    v___x_3073_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3073_, 0, v_b_3041_);
                    return v___x_3073_;
                }
            }
            1 => {
                v_ref_3053_ = leanh::lean_ctor_get(v___y_3042_, 5);
                v___x_3054_ = l_Lean_SourceInfo_fromRef(v_ref_3053_, v___x_3044_);
                v___x_3055_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___closed__1;
                v___x_3056_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___closed__2;
                leanh::lean_inc(v___x_3054_);
                if v_isShared_3052_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3051_, 2);
                    leanh::lean_ctor_set(v___x_3051_, 1, v___x_3056_);
                    leanh::lean_ctor_set(v___x_3051_, 0, v___x_3054_);
                    v___x_3058_ = v___x_3051_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3071_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3071_, 0, v___x_3054_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3071_, 1, v___x_3056_);
                    v___x_3058_ = v_reuseFailAlloc_3071_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3059_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___closed__4;
                v___x_3060_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___closed__5;
                leanh::lean_inc_n(v___x_3054_, 4);
                v___x_3061_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3061_, 0, v___x_3054_);
                leanh::lean_ctor_set(v___x_3061_, 1, v___x_3060_);
                v___x_3062_ = leanh::lean_box(2);
                v___x_3063_ = l_Lean_Syntax_mkStrLit(v_fst_3048_, v___x_3062_);
                leanh::lean_inc(v_discr_3037_);
                v___x_3064_ = l_Lean_Syntax_node3(
                    v___x_3054_,
                    v___x_3059_,
                    v_discr_3037_,
                    v___x_3061_,
                    v___x_3063_,
                );
                v___x_3065_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___closed__6;
                v___x_3066_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3066_, 0, v___x_3054_);
                leanh::lean_ctor_set(v___x_3066_, 1, v___x_3065_);
                v___x_3067_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___closed__7;
                v___x_3068_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3068_, 0, v___x_3054_);
                leanh::lean_ctor_set(v___x_3068_, 1, v___x_3067_);
                v___x_3069_ = l_Lean_Syntax_node6(
                    v___x_3054_,
                    v___x_3055_,
                    v___x_3058_,
                    v___x_3064_,
                    v___x_3066_,
                    v_snd_3049_,
                    v___x_3068_,
                    v_b_3041_,
                );
                v_i_3039_ = v___x_3046_;
                v_b_3041_ = v___x_3069_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___boxed(
    mut v_discr_3074_: *mut leanh::LeanObject,
    mut v_as_3075_: *mut leanh::LeanObject,
    mut v_i_3076_: *mut leanh::LeanObject,
    mut v_stop_3077_: *mut leanh::LeanObject,
    mut v_b_3078_: *mut leanh::LeanObject,
    mut v___y_3079_: *mut leanh::LeanObject,
    mut v___y_3080_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_3081_: usize = 0;
    let mut v_stop_boxed_3082_: usize = 0;
    let mut v_res_3083_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3081_ = leanh::lean_unbox_usize(v_i_3076_);
    leanh::lean_dec(v_i_3076_);
    v_stop_boxed_3082_ = leanh::lean_unbox_usize(v_stop_3077_);
    leanh::lean_dec(v_stop_3077_);
    v_res_3083_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg(v_discr_3074_, v_as_3075_, v_i_boxed_3081_, v_stop_boxed_3082_, v_b_3078_, v___y_3079_);
    leanh::lean_dec_ref(v___y_3079_);
    leanh::lean_dec_ref(v_as_3075_);
    return v_res_3083_;
}
pub unsafe fn l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build(
    mut v_discr_3092_: *mut leanh::LeanObject,
    mut v_onFail_3093_: *mut leanh::LeanObject,
    mut v_start_3094_: *mut leanh::LeanObject,
    mut v_stop_3095_: *mut leanh::LeanObject,
    mut v_cases_3096_: *mut leanh::LeanObject,
    mut v_a_3097_: *mut leanh::LeanObject,
    mut v_a_3098_: *mut leanh::LeanObject,
    mut v_a_3099_: *mut leanh::LeanObject,
    mut v_a_3100_: *mut leanh::LeanObject,
    mut v_a_3101_: *mut leanh::LeanObject,
    mut v_a_3102_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: u8 = 0;
    let mut v___x_3107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_3109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3115_: u8 = 0;
    let mut v___x_3116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3122_: u8 = 0;
    let mut v_ref_3123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3144_: u8 = 0;
    let mut v_isSharedCheck_3145_: u8 = 0;
    let mut v_unused_3146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_3148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_3149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_3150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: u8 = 0;
    let mut v___x_3153_: u8 = 0;
    let mut v___x_3154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3155_: usize = 0;
    let mut v___x_3156_: usize = 0;
    let mut v___x_3157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: u8 = 0;
    let mut v___x_3159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3160_: usize = 0;
    let mut v___x_3161_: usize = 0;
    let mut v___x_3162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3104_ = lean_nat_sub(v_stop_3095_, v_start_3094_);
                v___x_3105_ = leanh::lean_unsigned_to_nat(5);
                v___x_3106_ = lean_nat_dec_le(v___x_3104_, v___x_3105_);
                leanh::lean_dec(v___x_3104_);
                if v___x_3106_ == 0 {
                    v___x_3107_ = lean_nat_add(v_start_3094_, v_stop_3095_);
                    v___x_3108_ = leanh::lean_unsigned_to_nat(1);
                    v_mid_3109_ = lean_nat_shiftr(v___x_3107_, v___x_3108_);
                    leanh::lean_dec(v___x_3107_);
                    v___x_3110_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build___closed__1;
                    v___x_3111_ = lean_array_get(v___x_3110_, v_cases_3096_, v_mid_3109_);
                    v_fst_3112_ = leanh::lean_ctor_get(v___x_3111_, 0);
                    v_isSharedCheck_3145_ = (!leanh::lean_is_exclusive(v___x_3111_)) as u8;
                    if v_isSharedCheck_3145_ == 0 {
                        v_unused_3146_ = leanh::lean_ctor_get(v___x_3111_, 1);
                        leanh::lean_dec(v_unused_3146_);
                        v___x_3114_ = v___x_3111_;
                        v_isShared_3115_ = v_isSharedCheck_3145_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_fst_3112_);
                        leanh::lean_dec(v___x_3111_);
                        v___x_3114_ = leanh::lean_box(0);
                        v_isShared_3115_ = v_isSharedCheck_3145_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_3147_ =
                        l_Array_toSubarray___redArg(v_cases_3096_, v_start_3094_, v_stop_3095_);
                    v_array_3148_ = leanh::lean_ctor_get(v___x_3147_, 0);
                    leanh::lean_inc_ref(v_array_3148_);
                    v_start_3149_ = leanh::lean_ctor_get(v___x_3147_, 1);
                    leanh::lean_inc(v_start_3149_);
                    v_stop_3150_ = leanh::lean_ctor_get(v___x_3147_, 2);
                    leanh::lean_inc(v_stop_3150_);
                    leanh::lean_dec_ref(v___x_3147_);
                    v___x_3151_ = lean_array_get_size(v_array_3148_);
                    v___x_3152_ = lean_nat_dec_le(v_stop_3150_, v___x_3151_);
                    if v___x_3152_ == 0 {
                        leanh::lean_dec(v_stop_3150_);
                        v___x_3153_ = lean_nat_dec_lt(v_start_3149_, v___x_3151_);
                        if v___x_3153_ == 0 {
                            leanh::lean_dec(v_start_3149_);
                            leanh::lean_dec_ref(v_array_3148_);
                            leanh::lean_dec(v_discr_3092_);
                            v___x_3154_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_3154_, 0, v_onFail_3093_);
                            return v___x_3154_;
                        } else {
                            v___x_3155_ = lean_usize_of_nat(v___x_3151_);
                            v___x_3156_ = lean_usize_of_nat(v_start_3149_);
                            leanh::lean_dec(v_start_3149_);
                            v___x_3157_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg(v_discr_3092_, v_array_3148_, v___x_3155_, v___x_3156_, v_onFail_3093_, v_a_3101_);
                            leanh::lean_dec_ref(v_array_3148_);
                            return v___x_3157_;
                        }
                    } else {
                        v___x_3158_ = lean_nat_dec_lt(v_start_3149_, v_stop_3150_);
                        if v___x_3158_ == 0 {
                            leanh::lean_dec(v_stop_3150_);
                            leanh::lean_dec(v_start_3149_);
                            leanh::lean_dec_ref(v_array_3148_);
                            leanh::lean_dec(v_discr_3092_);
                            v___x_3159_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_3159_, 0, v_onFail_3093_);
                            return v___x_3159_;
                        } else {
                            v___x_3160_ = lean_usize_of_nat(v_stop_3150_);
                            leanh::lean_dec(v_stop_3150_);
                            v___x_3161_ = lean_usize_of_nat(v_start_3149_);
                            leanh::lean_dec(v_start_3149_);
                            v___x_3162_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg(v_discr_3092_, v_array_3148_, v___x_3160_, v___x_3161_, v_onFail_3093_, v_a_3101_);
                            leanh::lean_dec_ref(v_array_3148_);
                            return v___x_3162_;
                        }
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref(v_cases_3096_);
                leanh::lean_inc(v_mid_3109_);
                leanh::lean_inc(v_onFail_3093_);
                leanh::lean_inc(v_discr_3092_);
                v___x_3116_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build(v_discr_3092_, v_onFail_3093_, v_start_3094_, v_mid_3109_, v_cases_3096_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_, v_a_3101_, v_a_3102_);
                if leanh::lean_obj_tag(v___x_3116_) == 0 {
                    v_a_3117_ = leanh::lean_ctor_get(v___x_3116_, 0);
                    leanh::lean_inc(v_a_3117_);
                    leanh::lean_dec_ref_known(v___x_3116_, 1);
                    leanh::lean_inc(v_discr_3092_);
                    v___x_3118_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build(v_discr_3092_, v_onFail_3093_, v_mid_3109_, v_stop_3095_, v_cases_3096_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_, v_a_3101_, v_a_3102_);
                    if leanh::lean_obj_tag(v___x_3118_) == 0 {
                        v_a_3119_ = leanh::lean_ctor_get(v___x_3118_, 0);
                        v_isSharedCheck_3144_ =
                            (!leanh::lean_is_exclusive(v___x_3118_)) as u8;
                        if v_isSharedCheck_3144_ == 0 {
                            v___x_3121_ = v___x_3118_;
                            v_isShared_3122_ = v_isSharedCheck_3144_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3119_);
                            leanh::lean_dec(v___x_3118_);
                            v___x_3121_ = leanh::lean_box(0);
                            v_isShared_3122_ = v_isSharedCheck_3144_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_3117_);
                        leanh::lean_del_object(v___x_3114_);
                        leanh::lean_dec(v_fst_3112_);
                        leanh::lean_dec(v_discr_3092_);
                        return v___x_3118_;
                    }
                } else {
                    leanh::lean_del_object(v___x_3114_);
                    leanh::lean_dec(v_fst_3112_);
                    leanh::lean_dec(v_mid_3109_);
                    leanh::lean_dec_ref(v_cases_3096_);
                    leanh::lean_dec(v_stop_3095_);
                    leanh::lean_dec(v_onFail_3093_);
                    leanh::lean_dec(v_discr_3092_);
                    return v___x_3116_;
                }
            }
            2 => {
                v_ref_3123_ = leanh::lean_ctor_get(v_a_3101_, 5);
                v___x_3124_ = l_Lean_SourceInfo_fromRef(v_ref_3123_, v___x_3106_);
                v___x_3125_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___closed__1;
                v___x_3126_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___closed__2;
                leanh::lean_inc(v___x_3124_);
                if v_isShared_3115_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3114_, 2);
                    leanh::lean_ctor_set(v___x_3114_, 1, v___x_3126_);
                    leanh::lean_ctor_set(v___x_3114_, 0, v___x_3124_);
                    v___x_3128_ = v___x_3114_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3143_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3143_, 0, v___x_3124_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3143_, 1, v___x_3126_);
                    v___x_3128_ = v_reuseFailAlloc_3143_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3129_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build___closed__3;
                v___x_3130_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build___closed__4;
                leanh::lean_inc_n(v___x_3124_, 4);
                v___x_3131_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3131_, 0, v___x_3124_);
                leanh::lean_ctor_set(v___x_3131_, 1, v___x_3130_);
                v___x_3132_ = leanh::lean_box(2);
                v___x_3133_ = l_Lean_Syntax_mkStrLit(v_fst_3112_, v___x_3132_);
                v___x_3134_ = l_Lean_Syntax_node3(
                    v___x_3124_,
                    v___x_3129_,
                    v_discr_3092_,
                    v___x_3131_,
                    v___x_3133_,
                );
                v___x_3135_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___closed__6;
                v___x_3136_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3136_, 0, v___x_3124_);
                leanh::lean_ctor_set(v___x_3136_, 1, v___x_3135_);
                v___x_3137_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___closed__7;
                v___x_3138_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3138_, 0, v___x_3124_);
                leanh::lean_ctor_set(v___x_3138_, 1, v___x_3137_);
                v___x_3139_ = l_Lean_Syntax_node6(
                    v___x_3124_,
                    v___x_3125_,
                    v___x_3128_,
                    v___x_3134_,
                    v___x_3136_,
                    v_a_3117_,
                    v___x_3138_,
                    v_a_3119_,
                );
                if v_isShared_3122_ == 0 {
                    leanh::lean_ctor_set(v___x_3121_, 0, v___x_3139_);
                    v___x_3141_ = v___x_3121_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3142_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3142_, 0, v___x_3139_);
                    v___x_3141_ = v_reuseFailAlloc_3142_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3141_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build___boxed(
    mut v_discr_3163_: *mut leanh::LeanObject,
    mut v_onFail_3164_: *mut leanh::LeanObject,
    mut v_start_3165_: *mut leanh::LeanObject,
    mut v_stop_3166_: *mut leanh::LeanObject,
    mut v_cases_3167_: *mut leanh::LeanObject,
    mut v_a_3168_: *mut leanh::LeanObject,
    mut v_a_3169_: *mut leanh::LeanObject,
    mut v_a_3170_: *mut leanh::LeanObject,
    mut v_a_3171_: *mut leanh::LeanObject,
    mut v_a_3172_: *mut leanh::LeanObject,
    mut v_a_3173_: *mut leanh::LeanObject,
    mut v_a_3174_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3175_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3175_ =
        l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build(
            v_discr_3163_,
            v_onFail_3164_,
            v_start_3165_,
            v_stop_3166_,
            v_cases_3167_,
            v_a_3168_,
            v_a_3169_,
            v_a_3170_,
            v_a_3171_,
            v_a_3172_,
            v_a_3173_,
        );
    leanh::lean_dec(v_a_3173_);
    leanh::lean_dec_ref(v_a_3172_);
    leanh::lean_dec(v_a_3171_);
    leanh::lean_dec_ref(v_a_3170_);
    leanh::lean_dec(v_a_3169_);
    leanh::lean_dec_ref(v_a_3168_);
    return v_res_3175_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0(
    mut v_discr_3176_: *mut leanh::LeanObject,
    mut v_as_3177_: *mut leanh::LeanObject,
    mut v_i_3178_: usize,
    mut v_stop_3179_: usize,
    mut v_b_3180_: *mut leanh::LeanObject,
    mut v___y_3181_: *mut leanh::LeanObject,
    mut v___y_3182_: *mut leanh::LeanObject,
    mut v___y_3183_: *mut leanh::LeanObject,
    mut v___y_3184_: *mut leanh::LeanObject,
    mut v___y_3185_: *mut leanh::LeanObject,
    mut v___y_3186_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3188_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3188_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg(v_discr_3176_, v_as_3177_, v_i_3178_, v_stop_3179_, v_b_3180_, v___y_3185_);
    return v___x_3188_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___boxed(
    mut v_discr_3189_: *mut leanh::LeanObject,
    mut v_as_3190_: *mut leanh::LeanObject,
    mut v_i_3191_: *mut leanh::LeanObject,
    mut v_stop_3192_: *mut leanh::LeanObject,
    mut v_b_3193_: *mut leanh::LeanObject,
    mut v___y_3194_: *mut leanh::LeanObject,
    mut v___y_3195_: *mut leanh::LeanObject,
    mut v___y_3196_: *mut leanh::LeanObject,
    mut v___y_3197_: *mut leanh::LeanObject,
    mut v___y_3198_: *mut leanh::LeanObject,
    mut v___y_3199_: *mut leanh::LeanObject,
    mut v___y_3200_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_3201_: usize = 0;
    let mut v_stop_boxed_3202_: usize = 0;
    let mut v_res_3203_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3201_ = leanh::lean_unbox_usize(v_i_3191_);
    leanh::lean_dec(v_i_3191_);
    v_stop_boxed_3202_ = leanh::lean_unbox_usize(v_stop_3192_);
    leanh::lean_dec(v_stop_3192_);
    v_res_3203_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0(v_discr_3189_, v_as_3190_, v_i_boxed_3201_, v_stop_boxed_3202_, v_b_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_);
    leanh::lean_dec(v___y_3199_);
    leanh::lean_dec_ref(v___y_3198_);
    leanh::lean_dec(v___y_3197_);
    leanh::lean_dec_ref(v___y_3196_);
    leanh::lean_dec(v___y_3195_);
    leanh::lean_dec_ref(v___y_3194_);
    leanh::lean_dec_ref(v_as_3190_);
    return v_res_3203_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_ConfigEval_makeStringMatcher_spec__0___redArg___lam__0(
    mut v_c_3204_: *mut leanh::LeanObject,
    mut v_c_x27_3205_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_fst_3206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3208_: u8 = 0;
    v_fst_3206_ = leanh::lean_ctor_get(v_c_3204_, 0);
    v_fst_3207_ = leanh::lean_ctor_get(v_c_x27_3205_, 0);
    v___x_3208_ = lean_string_dec_lt(v_fst_3206_, v_fst_3207_);
    return v___x_3208_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_ConfigEval_makeStringMatcher_spec__0___redArg___lam__0___boxed(
    mut v_c_3209_: *mut leanh::LeanObject,
    mut v_c_x27_3210_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3211_: u8 = 0;
    let mut v_r_3212_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3211_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_ConfigEval_makeStringMatcher_spec__0___redArg___lam__0(v_c_3209_, v_c_x27_3210_);
    leanh::lean_dec_ref(v_c_x27_3210_);
    leanh::lean_dec_ref(v_c_3209_);
    v_r_3212_ = leanh::lean_box((v_res_3211_) as usize);
    return v_r_3212_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_ConfigEval_makeStringMatcher_spec__0_spec__0___redArg(
    mut v_hi_3213_: *mut leanh::LeanObject,
    mut v_pivot_3214_: *mut leanh::LeanObject,
    mut v_as_3215_: *mut leanh::LeanObject,
    mut v_i_3216_: *mut leanh::LeanObject,
    mut v_k_3217_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3218_: u8 = 0;
    let mut v___x_3219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: u8 = 0;
    let mut v___x_3225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3218_ = lean_nat_dec_lt(v_k_3217_, v_hi_3213_);
                if v___x_3218_ == 0 {
                    leanh::lean_dec(v_k_3217_);
                    v___x_3219_ = lean_array_fswap(v_as_3215_, v_i_3216_, v_hi_3213_);
                    v___x_3220_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3220_, 0, v_i_3216_);
                    leanh::lean_ctor_set(v___x_3220_, 1, v___x_3219_);
                    return v___x_3220_;
                } else {
                    v___x_3221_ = lean_array_fget_borrowed(v_as_3215_, v_k_3217_);
                    v_fst_3222_ = leanh::lean_ctor_get(v___x_3221_, 0);
                    v_fst_3223_ = leanh::lean_ctor_get(v_pivot_3214_, 0);
                    v___x_3224_ = lean_string_dec_lt(v_fst_3222_, v_fst_3223_);
                    if v___x_3224_ == 0 {
                        v___x_3225_ = leanh::lean_unsigned_to_nat(1);
                        v___x_3226_ = lean_nat_add(v_k_3217_, v___x_3225_);
                        leanh::lean_dec(v_k_3217_);
                        v_k_3217_ = v___x_3226_;
                        state = 0;
                        continue;
                    } else {
                        v___x_3228_ = lean_array_fswap(v_as_3215_, v_i_3216_, v_k_3217_);
                        v___x_3229_ = leanh::lean_unsigned_to_nat(1);
                        v___x_3230_ = lean_nat_add(v_i_3216_, v___x_3229_);
                        leanh::lean_dec(v_i_3216_);
                        v___x_3231_ = lean_nat_add(v_k_3217_, v___x_3229_);
                        leanh::lean_dec(v_k_3217_);
                        v_as_3215_ = v___x_3228_;
                        v_i_3216_ = v___x_3230_;
                        v_k_3217_ = v___x_3231_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_ConfigEval_makeStringMatcher_spec__0_spec__0___redArg___boxed(
    mut v_hi_3233_: *mut leanh::LeanObject,
    mut v_pivot_3234_: *mut leanh::LeanObject,
    mut v_as_3235_: *mut leanh::LeanObject,
    mut v_i_3236_: *mut leanh::LeanObject,
    mut v_k_3237_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3238_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3238_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_ConfigEval_makeStringMatcher_spec__0_spec__0___redArg(v_hi_3233_, v_pivot_3234_, v_as_3235_, v_i_3236_, v_k_3237_);
    leanh::lean_dec_ref(v_pivot_3234_);
    leanh::lean_dec(v_hi_3233_);
    return v_res_3238_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_ConfigEval_makeStringMatcher_spec__0___redArg(
    mut v_n_3239_: *mut leanh::LeanObject,
    mut v_as_3240_: *mut leanh::LeanObject,
    mut v_lo_3241_: *mut leanh::LeanObject,
    mut v_hi_3242_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pivot_3245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3249_: u8 = 0;
    let mut v___x_3250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3254_: u8 = 0;
    let mut v___x_3255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_3257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: u8 = 0;
    let mut v___x_3263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3268_: u8 = 0;
    let mut v___x_3269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: u8 = 0;
    let mut v___x_3273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3254_ = lean_nat_dec_lt(v_lo_3241_, v_hi_3242_);
                if v___x_3254_ == 0 {
                    leanh::lean_dec(v_lo_3241_);
                    return v_as_3240_;
                } else {
                    v___x_3255_ = lean_nat_add(v_lo_3241_, v_hi_3242_);
                    v___x_3256_ = leanh::lean_unsigned_to_nat(1);
                    v_mid_3257_ = lean_nat_shiftr(v___x_3255_, v___x_3256_);
                    leanh::lean_dec(v___x_3255_);
                    v___x_3270_ = lean_array_fget_borrowed(v_as_3240_, v_mid_3257_);
                    v___x_3271_ = lean_array_fget_borrowed(v_as_3240_, v_lo_3241_);
                    v___x_3272_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_ConfigEval_makeStringMatcher_spec__0___redArg___lam__0(v___x_3270_, v___x_3271_);
                    if v___x_3272_ == 0 {
                        v___y_3265_ = v_as_3240_;
                        state = 3;
                        continue;
                    } else {
                        v___x_3273_ = lean_array_fswap(v_as_3240_, v_lo_3241_, v_mid_3257_);
                        v___y_3265_ = v___x_3273_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_pivot_3245_ = lean_array_fget(v___y_3244_, v_hi_3242_);
                leanh::lean_inc_n(v_lo_3241_, 2);
                v___x_3246_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_ConfigEval_makeStringMatcher_spec__0_spec__0___redArg(v_hi_3242_, v_pivot_3245_, v___y_3244_, v_lo_3241_, v_lo_3241_);
                leanh::lean_dec(v_pivot_3245_);
                v_fst_3247_ = leanh::lean_ctor_get(v___x_3246_, 0);
                leanh::lean_inc(v_fst_3247_);
                v_snd_3248_ = leanh::lean_ctor_get(v___x_3246_, 1);
                leanh::lean_inc(v_snd_3248_);
                leanh::lean_dec_ref(v___x_3246_);
                v___x_3249_ = lean_nat_dec_le(v_hi_3242_, v_fst_3247_);
                if v___x_3249_ == 0 {
                    v___x_3250_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_ConfigEval_makeStringMatcher_spec__0___redArg(v_n_3239_, v_snd_3248_, v_lo_3241_, v_fst_3247_);
                    v___x_3251_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3252_ = lean_nat_add(v_fst_3247_, v___x_3251_);
                    leanh::lean_dec(v_fst_3247_);
                    v_as_3240_ = v___x_3250_;
                    v_lo_3241_ = v___x_3252_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_fst_3247_);
                    leanh::lean_dec(v_lo_3241_);
                    return v_snd_3248_;
                }
            }
            2 => {
                v___x_3260_ = lean_array_fget_borrowed(v___y_3259_, v_mid_3257_);
                v___x_3261_ = lean_array_fget_borrowed(v___y_3259_, v_hi_3242_);
                v___x_3262_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_ConfigEval_makeStringMatcher_spec__0___redArg___lam__0(v___x_3260_, v___x_3261_);
                if v___x_3262_ == 0 {
                    leanh::lean_dec(v_mid_3257_);
                    v___y_3244_ = v___y_3259_;
                    state = 1;
                    continue;
                } else {
                    v___x_3263_ = lean_array_fswap(v___y_3259_, v_mid_3257_, v_hi_3242_);
                    leanh::lean_dec(v_mid_3257_);
                    v___y_3244_ = v___x_3263_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_3266_ = lean_array_fget_borrowed(v___y_3265_, v_hi_3242_);
                v___x_3267_ = lean_array_fget_borrowed(v___y_3265_, v_lo_3241_);
                v___x_3268_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_ConfigEval_makeStringMatcher_spec__0___redArg___lam__0(v___x_3266_, v___x_3267_);
                if v___x_3268_ == 0 {
                    v___y_3259_ = v___y_3265_;
                    state = 2;
                    continue;
                } else {
                    v___x_3269_ = lean_array_fswap(v___y_3265_, v_lo_3241_, v_hi_3242_);
                    v___y_3259_ = v___x_3269_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_ConfigEval_makeStringMatcher_spec__0___redArg___boxed(
    mut v_n_3274_: *mut leanh::LeanObject,
    mut v_as_3275_: *mut leanh::LeanObject,
    mut v_lo_3276_: *mut leanh::LeanObject,
    mut v_hi_3277_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3278_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3278_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_ConfigEval_makeStringMatcher_spec__0___redArg(v_n_3274_, v_as_3275_, v_lo_3276_, v_hi_3277_);
    leanh::lean_dec(v_hi_3277_);
    leanh::lean_dec(v_n_3274_);
    return v_res_3278_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_makeStringMatcher(
    mut v_discr_3279_: *mut leanh::LeanObject,
    mut v_cases_3280_: *mut leanh::LeanObject,
    mut v_onFail_3281_: *mut leanh::LeanObject,
    mut v_a_3282_: *mut leanh::LeanObject,
    mut v_a_3283_: *mut leanh::LeanObject,
    mut v_a_3284_: *mut leanh::LeanObject,
    mut v_a_3285_: *mut leanh::LeanObject,
    mut v_a_3286_: *mut leanh::LeanObject,
    mut v_a_3287_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3299_: u8 = 0;
    let mut v___x_3300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: u8 = 0;
    let mut v___x_3305_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3289_ = leanh::lean_unsigned_to_nat(0);
                v___x_3294_ = lean_array_get_size(v_cases_3280_);
                v___x_3299_ = lean_nat_dec_eq(v___x_3294_, v___x_3289_);
                if v___x_3299_ == 0 {
                    v___x_3300_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3301_ = lean_nat_sub(v___x_3294_, v___x_3300_);
                    v___x_3305_ = lean_nat_dec_le(v___x_3289_, v___x_3301_);
                    if v___x_3305_ == 0 {
                        leanh::lean_inc(v___x_3301_);
                        v___y_3303_ = v___x_3301_;
                        state = 3;
                        continue;
                    } else {
                        v___y_3303_ = v___x_3289_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___y_3291_ = v_cases_3280_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3292_ = lean_array_get_size(v___y_3291_);
                v___x_3293_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build(v_discr_3279_, v_onFail_3281_, v___x_3289_, v___x_3292_, v___y_3291_, v_a_3282_, v_a_3283_, v_a_3284_, v_a_3285_, v_a_3286_, v_a_3287_);
                return v___x_3293_;
            }
            2 => {
                v___x_3298_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_ConfigEval_makeStringMatcher_spec__0___redArg(v___x_3294_, v_cases_3280_, v___y_3296_, v___y_3297_);
                leanh::lean_dec(v___y_3297_);
                v___y_3291_ = v___x_3298_;
                state = 1;
                continue;
            }
            3 => {
                v___x_3304_ = lean_nat_dec_le(v___y_3303_, v___x_3301_);
                if v___x_3304_ == 0 {
                    leanh::lean_dec(v___x_3301_);
                    leanh::lean_inc(v___y_3303_);
                    v___y_3296_ = v___y_3303_;
                    v___y_3297_ = v___y_3303_;
                    state = 2;
                    continue;
                } else {
                    v___y_3296_ = v___y_3303_;
                    v___y_3297_ = v___x_3301_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_makeStringMatcher___boxed(
    mut v_discr_3306_: *mut leanh::LeanObject,
    mut v_cases_3307_: *mut leanh::LeanObject,
    mut v_onFail_3308_: *mut leanh::LeanObject,
    mut v_a_3309_: *mut leanh::LeanObject,
    mut v_a_3310_: *mut leanh::LeanObject,
    mut v_a_3311_: *mut leanh::LeanObject,
    mut v_a_3312_: *mut leanh::LeanObject,
    mut v_a_3313_: *mut leanh::LeanObject,
    mut v_a_3314_: *mut leanh::LeanObject,
    mut v_a_3315_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3316_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3316_ = l_Lean_Elab_ConfigEval_makeStringMatcher(
        v_discr_3306_,
        v_cases_3307_,
        v_onFail_3308_,
        v_a_3309_,
        v_a_3310_,
        v_a_3311_,
        v_a_3312_,
        v_a_3313_,
        v_a_3314_,
    );
    leanh::lean_dec(v_a_3314_);
    leanh::lean_dec_ref(v_a_3313_);
    leanh::lean_dec(v_a_3312_);
    leanh::lean_dec_ref(v_a_3311_);
    leanh::lean_dec(v_a_3310_);
    leanh::lean_dec_ref(v_a_3309_);
    return v_res_3316_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_ConfigEval_makeStringMatcher_spec__0(
    mut v_n_3317_: *mut leanh::LeanObject,
    mut v_as_3318_: *mut leanh::LeanObject,
    mut v_lo_3319_: *mut leanh::LeanObject,
    mut v_hi_3320_: *mut leanh::LeanObject,
    mut v_w_3321_: *mut leanh::LeanObject,
    mut v_hlo_3322_: *mut leanh::LeanObject,
    mut v_hhi_3323_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3324_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3324_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_ConfigEval_makeStringMatcher_spec__0___redArg(v_n_3317_, v_as_3318_, v_lo_3319_, v_hi_3320_);
    return v___x_3324_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_ConfigEval_makeStringMatcher_spec__0___boxed(
    mut v_n_3325_: *mut leanh::LeanObject,
    mut v_as_3326_: *mut leanh::LeanObject,
    mut v_lo_3327_: *mut leanh::LeanObject,
    mut v_hi_3328_: *mut leanh::LeanObject,
    mut v_w_3329_: *mut leanh::LeanObject,
    mut v_hlo_3330_: *mut leanh::LeanObject,
    mut v_hhi_3331_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3332_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3332_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_ConfigEval_makeStringMatcher_spec__0(v_n_3325_, v_as_3326_, v_lo_3327_, v_hi_3328_, v_w_3329_, v_hlo_3330_, v_hhi_3331_);
    leanh::lean_dec(v_hi_3328_);
    leanh::lean_dec(v_n_3325_);
    return v_res_3332_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_ConfigEval_makeStringMatcher_spec__0_spec__0(
    mut v_n_3333_: *mut leanh::LeanObject,
    mut v_lo_3334_: *mut leanh::LeanObject,
    mut v_hi_3335_: *mut leanh::LeanObject,
    mut v_hhi_3336_: *mut leanh::LeanObject,
    mut v_pivot_3337_: *mut leanh::LeanObject,
    mut v_as_3338_: *mut leanh::LeanObject,
    mut v_i_3339_: *mut leanh::LeanObject,
    mut v_k_3340_: *mut leanh::LeanObject,
    mut v_ilo_3341_: *mut leanh::LeanObject,
    mut v_ik_3342_: *mut leanh::LeanObject,
    mut v_w_3343_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3344_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3344_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_ConfigEval_makeStringMatcher_spec__0_spec__0___redArg(v_hi_3335_, v_pivot_3337_, v_as_3338_, v_i_3339_, v_k_3340_);
    return v___x_3344_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_ConfigEval_makeStringMatcher_spec__0_spec__0___boxed(
    mut v_n_3345_: *mut leanh::LeanObject,
    mut v_lo_3346_: *mut leanh::LeanObject,
    mut v_hi_3347_: *mut leanh::LeanObject,
    mut v_hhi_3348_: *mut leanh::LeanObject,
    mut v_pivot_3349_: *mut leanh::LeanObject,
    mut v_as_3350_: *mut leanh::LeanObject,
    mut v_i_3351_: *mut leanh::LeanObject,
    mut v_k_3352_: *mut leanh::LeanObject,
    mut v_ilo_3353_: *mut leanh::LeanObject,
    mut v_ik_3354_: *mut leanh::LeanObject,
    mut v_w_3355_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3356_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3356_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_ConfigEval_makeStringMatcher_spec__0_spec__0(v_n_3345_, v_lo_3346_, v_hi_3347_, v_hhi_3348_, v_pivot_3349_, v_as_3350_, v_i_3351_, v_k_3352_, v_ilo_3353_, v_ik_3354_, v_w_3355_);
    leanh::lean_dec_ref(v_pivot_3349_);
    leanh::lean_dec(v_hi_3347_);
    leanh::lean_dec(v_lo_3346_);
    leanh::lean_dec(v_n_3345_);
    return v_res_3356_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3363_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3362_ = l_Lean_maxRecDepthErrorMessage;
    v___x_3363_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3363_, 0, v___x_3362_);
    return v___x_3363_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_3364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3365_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3364_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg___closed__3_once), _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg___closed__3);
    v___x_3365_ = l_Lean_MessageData_ofFormat(v___x_3364_);
    return v___x_3365_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_3366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3366_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg___closed__4_once), _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg___closed__4);
    v___x_3367_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg___closed__2;
    v___x_3368_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3368_, 0, v___x_3367_);
    leanh::lean_ctor_set(v___x_3368_, 1, v___x_3366_);
    return v___x_3368_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg(
    mut v_ref_3369_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3371_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg___closed__5_once), _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg___closed__5);
    v___x_3372_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3372_, 0, v_ref_3369_);
    leanh::lean_ctor_set(v___x_3372_, 1, v___x_3371_);
    v___x_3373_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3373_, 0, v___x_3372_);
    return v___x_3373_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg___boxed(
    mut v_ref_3374_: *mut leanh::LeanObject,
    mut v___y_3375_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3376_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3376_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg(v_ref_3374_);
    return v_res_3376_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6(
    mut v_00_u03b1_3377_: *mut leanh::LeanObject,
    mut v_ref_3378_: *mut leanh::LeanObject,
    mut v___y_3379_: *mut leanh::LeanObject,
    mut v___y_3380_: *mut leanh::LeanObject,
    mut v___y_3381_: *mut leanh::LeanObject,
    mut v___y_3382_: *mut leanh::LeanObject,
    mut v___y_3383_: *mut leanh::LeanObject,
    mut v___y_3384_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3386_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3386_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg(v_ref_3378_);
    return v___x_3386_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___boxed(
    mut v_00_u03b1_3387_: *mut leanh::LeanObject,
    mut v_ref_3388_: *mut leanh::LeanObject,
    mut v___y_3389_: *mut leanh::LeanObject,
    mut v___y_3390_: *mut leanh::LeanObject,
    mut v___y_3391_: *mut leanh::LeanObject,
    mut v___y_3392_: *mut leanh::LeanObject,
    mut v___y_3393_: *mut leanh::LeanObject,
    mut v___y_3394_: *mut leanh::LeanObject,
    mut v___y_3395_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3396_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3396_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6(v_00_u03b1_3387_, v_ref_3388_, v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_);
    leanh::lean_dec(v___y_3394_);
    leanh::lean_dec_ref(v___y_3393_);
    leanh::lean_dec(v___y_3392_);
    leanh::lean_dec_ref(v___y_3391_);
    leanh::lean_dec(v___y_3390_);
    leanh::lean_dec_ref(v___y_3389_);
    return v_res_3396_;
}
pub unsafe fn l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___lam__0(
    mut v_cls_3400_: *mut leanh::LeanObject,
    mut v___y_3401_: *mut leanh::LeanObject,
    mut v___y_3402_: *mut leanh::LeanObject,
    mut v___y_3403_: *mut leanh::LeanObject,
    mut v___y_3404_: *mut leanh::LeanObject,
    mut v___y_3405_: *mut leanh::LeanObject,
    mut v___y_3406_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_options_3408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3409_: u8 = 0;
    v_options_3408_ = leanh::lean_ctor_get(v___y_3405_, 2);
    v_hasTrace_3409_ = leanh::lean_ctor_get_uint8(
        v_options_3408_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
    );
    if v_hasTrace_3409_ == 0 {
        let mut v___x_3410_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3411_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_cls_3400_);
        v___x_3410_ = leanh::lean_box((v_hasTrace_3409_) as usize);
        v___x_3411_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_3411_, 0, v___x_3410_);
        return v___x_3411_;
    } else {
        let mut v_inheritedTraceOptions_3412_: *mut leanh::LeanObject =
            core::ptr::null_mut();
        let mut v___x_3413_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3414_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3415_: u8 = 0;
        let mut v___x_3416_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3417_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_inheritedTraceOptions_3412_ = leanh::lean_ctor_get(v___y_3405_, 13);
        v___x_3413_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___lam__0___closed__1;
        v___x_3414_ = l_Lean_Name_append(v___x_3413_, v_cls_3400_);
        v___x_3415_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
            v_inheritedTraceOptions_3412_,
            v_options_3408_,
            v___x_3414_,
        );
        leanh::lean_dec(v___x_3414_);
        v___x_3416_ = leanh::lean_box((v___x_3415_) as usize);
        v___x_3417_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_3417_, 0, v___x_3416_);
        return v___x_3417_;
    }
}
pub unsafe fn l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___lam__0___boxed(
    mut v_cls_3418_: *mut leanh::LeanObject,
    mut v___y_3419_: *mut leanh::LeanObject,
    mut v___y_3420_: *mut leanh::LeanObject,
    mut v___y_3421_: *mut leanh::LeanObject,
    mut v___y_3422_: *mut leanh::LeanObject,
    mut v___y_3423_: *mut leanh::LeanObject,
    mut v___y_3424_: *mut leanh::LeanObject,
    mut v___y_3425_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3426_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3426_ =
        l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___lam__0(
            v_cls_3418_,
            v___y_3419_,
            v___y_3420_,
            v___y_3421_,
            v___y_3422_,
            v___y_3423_,
            v___y_3424_,
        );
    leanh::lean_dec(v___y_3424_);
    leanh::lean_dec_ref(v___y_3423_);
    leanh::lean_dec(v___y_3422_);
    leanh::lean_dec_ref(v___y_3421_);
    leanh::lean_dec(v___y_3420_);
    leanh::lean_dec_ref(v___y_3419_);
    return v_res_3426_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__16(
    mut v_as_3430_: *mut leanh::LeanObject,
    mut v_sz_3431_: usize,
    mut v_i_3432_: usize,
    mut v_b_3433_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3434_: u8 = 0;
    let mut v___x_3435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: u8 = 0;
    let mut v___x_3438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: usize = 0;
    let mut v___x_3440_: usize = 0;
    let mut v___x_3442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3434_ = lean_usize_dec_lt(v_i_3432_, v_sz_3431_);
                if v___x_3434_ == 0 {
                    leanh::lean_inc_ref(v_b_3433_);
                    return v_b_3433_;
                } else {
                    v___x_3435_ = leanh::lean_box(0);
                    v_a_3436_ = lean_array_uget_borrowed(v_as_3430_, v_i_3432_);
                    v___x_3437_ = l_Lean_Expr_hasMVar(v_a_3436_);
                    if v___x_3437_ == 0 {
                        v___x_3438_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__16___closed__0;
                        v___x_3439_ = 1usize;
                        v___x_3440_ = lean_usize_add(v_i_3432_, v___x_3439_);
                        v_i_3432_ = v___x_3440_;
                        v_b_3433_ = v___x_3438_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3436_);
                        v___x_3442_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3442_, 0, v_a_3436_);
                        v___x_3443_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3443_, 0, v___x_3442_);
                        v___x_3444_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3444_, 0, v___x_3443_);
                        leanh::lean_ctor_set(v___x_3444_, 1, v___x_3435_);
                        return v___x_3444_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__16___boxed(
    mut v_as_3445_: *mut leanh::LeanObject,
    mut v_sz_3446_: *mut leanh::LeanObject,
    mut v_i_3447_: *mut leanh::LeanObject,
    mut v_b_3448_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3449_: usize = 0;
    let mut v_i_boxed_3450_: usize = 0;
    let mut v_res_3451_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3449_ = leanh::lean_unbox_usize(v_sz_3446_);
    leanh::lean_dec(v_sz_3446_);
    v_i_boxed_3450_ = leanh::lean_unbox_usize(v_i_3447_);
    leanh::lean_dec(v_i_3447_);
    v_res_3451_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__16(v_as_3445_, v_sz_boxed_3449_, v_i_boxed_3450_, v_b_3448_);
    leanh::lean_dec_ref(v_b_3448_);
    leanh::lean_dec_ref(v_as_3445_);
    return v_res_3451_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__0_spec__0(
    mut v_a_3452_: *mut leanh::LeanObject,
    mut v_as_3453_: *mut leanh::LeanObject,
    mut v_i_3454_: usize,
    mut v_stop_3455_: usize,
) -> u8 {
    let mut v___x_3456_: u8 = 0;
    let mut v___x_3457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: u8 = 0;
    let mut v___x_3459_: usize = 0;
    let mut v___x_3460_: usize = 0;
    let mut v___x_3462_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3456_ = lean_usize_dec_eq(v_i_3454_, v_stop_3455_);
                if v___x_3456_ == 0 {
                    v___x_3457_ = lean_array_uget_borrowed(v_as_3453_, v_i_3454_);
                    v___x_3458_ = lean_expr_eqv(v_a_3452_, v___x_3457_);
                    if v___x_3458_ == 0 {
                        v___x_3459_ = 1usize;
                        v___x_3460_ = lean_usize_add(v_i_3454_, v___x_3459_);
                        v_i_3454_ = v___x_3460_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3458_;
                    }
                } else {
                    v___x_3462_ = 0;
                    return v___x_3462_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__0_spec__0___boxed(
    mut v_a_3463_: *mut leanh::LeanObject,
    mut v_as_3464_: *mut leanh::LeanObject,
    mut v_i_3465_: *mut leanh::LeanObject,
    mut v_stop_3466_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_3467_: usize = 0;
    let mut v_stop_boxed_3468_: usize = 0;
    let mut v_res_3469_: u8 = 0;
    let mut v_r_3470_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3467_ = leanh::lean_unbox_usize(v_i_3465_);
    leanh::lean_dec(v_i_3465_);
    v_stop_boxed_3468_ = leanh::lean_unbox_usize(v_stop_3466_);
    leanh::lean_dec(v_stop_3466_);
    v_res_3469_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__0_spec__0(v_a_3463_, v_as_3464_, v_i_boxed_3467_, v_stop_boxed_3468_);
    leanh::lean_dec_ref(v_as_3464_);
    leanh::lean_dec_ref(v_a_3463_);
    v_r_3470_ = leanh::lean_box((v_res_3469_) as usize);
    return v_r_3470_;
}
pub unsafe fn l_Array_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__0(
    mut v_as_3471_: *mut leanh::LeanObject,
    mut v_a_3472_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: u8 = 0;
    v___x_3473_ = leanh::lean_unsigned_to_nat(0);
    v___x_3474_ = lean_array_get_size(v_as_3471_);
    v___x_3475_ = lean_nat_dec_lt(v___x_3473_, v___x_3474_);
    if v___x_3475_ == 0 {
        return v___x_3475_;
    } else {
        if v___x_3475_ == 0 {
            return v___x_3475_;
        } else {
            let mut v___x_3476_: usize = 0;
            let mut v___x_3477_: usize = 0;
            let mut v___x_3478_: u8 = 0;
            v___x_3476_ = 0usize;
            v___x_3477_ = lean_usize_of_nat(v___x_3474_);
            v___x_3478_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__0_spec__0(v_a_3472_, v_as_3471_, v___x_3476_, v___x_3477_);
            return v___x_3478_;
        }
    }
}
pub unsafe fn l_Array_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__0___boxed(
    mut v_as_3479_: *mut leanh::LeanObject,
    mut v_a_3480_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3481_: u8 = 0;
    let mut v_r_3482_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3481_ = l_Array_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__0(v_as_3479_, v_a_3480_);
    leanh::lean_dec_ref(v_a_3480_);
    leanh::lean_dec_ref(v_as_3479_);
    v_r_3482_ = leanh::lean_box((v_res_3481_) as usize);
    return v_r_3482_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__15(
    mut v_plan_3483_: *mut leanh::LeanObject,
    mut v_as_3484_: *mut leanh::LeanObject,
    mut v_i_3485_: usize,
    mut v_stop_3486_: usize,
    mut v_b_3487_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3490_: usize = 0;
    let mut v___x_3491_: usize = 0;
    let mut v___x_3493_: u8 = 0;
    let mut v___x_3494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3495_: u8 = 0;
    let mut v___x_3496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3493_ = lean_usize_dec_eq(v_i_3485_, v_stop_3486_);
                if v___x_3493_ == 0 {
                    v___x_3494_ = lean_array_uget_borrowed(v_as_3484_, v_i_3485_);
                    v___x_3495_ = l_Array_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__0(v_plan_3483_, v___x_3494_);
                    if v___x_3495_ == 0 {
                        leanh::lean_inc(v___x_3494_);
                        v___x_3496_ = lean_array_push(v_b_3487_, v___x_3494_);
                        v___y_3489_ = v___x_3496_;
                        state = 1;
                        continue;
                    } else {
                        v___y_3489_ = v_b_3487_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_3487_;
                }
            }
            1 => {
                v___x_3490_ = 1usize;
                v___x_3491_ = lean_usize_add(v_i_3485_, v___x_3490_);
                v_i_3485_ = v___x_3491_;
                v_b_3487_ = v___y_3489_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__15___boxed(
    mut v_plan_3497_: *mut leanh::LeanObject,
    mut v_as_3498_: *mut leanh::LeanObject,
    mut v_i_3499_: *mut leanh::LeanObject,
    mut v_stop_3500_: *mut leanh::LeanObject,
    mut v_b_3501_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_3502_: usize = 0;
    let mut v_stop_boxed_3503_: usize = 0;
    let mut v_res_3504_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3502_ = leanh::lean_unbox_usize(v_i_3499_);
    leanh::lean_dec(v_i_3499_);
    v_stop_boxed_3503_ = leanh::lean_unbox_usize(v_stop_3500_);
    leanh::lean_dec(v_stop_3500_);
    v_res_3504_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__15(v_plan_3497_, v_as_3498_, v_i_boxed_3502_, v_stop_boxed_3503_, v_b_3501_);
    leanh::lean_dec_ref(v_as_3498_);
    leanh::lean_dec_ref(v_plan_3497_);
    return v_res_3504_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__10___redArg(
    mut v_a_3505_: *mut leanh::LeanObject,
    mut v_x_3506_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3507_: u8 = 0;
    let mut v_key_3508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3510_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3506_) == 0 {
                    v___x_3507_ = 0;
                    return v___x_3507_;
                } else {
                    v_key_3508_ = leanh::lean_ctor_get(v_x_3506_, 0);
                    v_tail_3509_ = leanh::lean_ctor_get(v_x_3506_, 2);
                    v___x_3510_ = lean_expr_eqv(v_key_3508_, v_a_3505_);
                    if v___x_3510_ == 0 {
                        v_x_3506_ = v_tail_3509_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3510_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__10___redArg___boxed(
    mut v_a_3512_: *mut leanh::LeanObject,
    mut v_x_3513_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3514_: u8 = 0;
    let mut v_r_3515_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3514_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__10___redArg(v_a_3512_, v_x_3513_);
    leanh::lean_dec(v_x_3513_);
    leanh::lean_dec_ref(v_a_3512_);
    v_r_3515_ = leanh::lean_box((v_res_3514_) as usize);
    return v_r_3515_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__12___redArg(
    mut v_m_3516_: *mut leanh::LeanObject,
    mut v_a_3517_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_buckets_3518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: u64 = 0;
    let mut v___x_3521_: u64 = 0;
    let mut v___x_3522_: u64 = 0;
    let mut v_fold_3523_: u64 = 0;
    let mut v___x_3524_: u64 = 0;
    let mut v___x_3525_: u64 = 0;
    let mut v___x_3526_: u64 = 0;
    let mut v___x_3527_: usize = 0;
    let mut v___x_3528_: usize = 0;
    let mut v___x_3529_: usize = 0;
    let mut v___x_3530_: usize = 0;
    let mut v___x_3531_: usize = 0;
    let mut v___x_3532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: u8 = 0;
    v_buckets_3518_ = leanh::lean_ctor_get(v_m_3516_, 1);
    v___x_3519_ = lean_array_get_size(v_buckets_3518_);
    v___x_3520_ = l_Lean_Expr_hash(v_a_3517_);
    v___x_3521_ = 32u64;
    v___x_3522_ = lean_uint64_shift_right(v___x_3520_, v___x_3521_);
    v_fold_3523_ = lean_uint64_xor(v___x_3520_, v___x_3522_);
    v___x_3524_ = 16u64;
    v___x_3525_ = lean_uint64_shift_right(v_fold_3523_, v___x_3524_);
    v___x_3526_ = lean_uint64_xor(v_fold_3523_, v___x_3525_);
    v___x_3527_ = lean_uint64_to_usize(v___x_3526_);
    v___x_3528_ = lean_usize_of_nat(v___x_3519_);
    v___x_3529_ = 1usize;
    v___x_3530_ = lean_usize_sub(v___x_3528_, v___x_3529_);
    v___x_3531_ = lean_usize_land(v___x_3527_, v___x_3530_);
    v___x_3532_ = lean_array_uget_borrowed(v_buckets_3518_, v___x_3531_);
    v___x_3533_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__10___redArg(v_a_3517_, v___x_3532_);
    return v___x_3533_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__12___redArg___boxed(
    mut v_m_3534_: *mut leanh::LeanObject,
    mut v_a_3535_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3536_: u8 = 0;
    let mut v_r_3537_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3536_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__12___redArg(v_m_3534_, v_a_3535_);
    leanh::lean_dec_ref(v_a_3535_);
    leanh::lean_dec_ref(v_m_3534_);
    v_r_3537_ = leanh::lean_box((v_res_3536_) as usize);
    return v_r_3537_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__13(
    mut v_processing_3538_: *mut leanh::LeanObject,
    mut v_as_3539_: *mut leanh::LeanObject,
    mut v_sz_3540_: usize,
    mut v_i_3541_: usize,
    mut v_b_3542_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3543_: u8 = 0;
    let mut v___x_3544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3546_: u8 = 0;
    let mut v___x_3547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: usize = 0;
    let mut v___x_3549_: usize = 0;
    let mut v___x_3551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3543_ = lean_usize_dec_lt(v_i_3541_, v_sz_3540_);
                if v___x_3543_ == 0 {
                    leanh::lean_inc_ref(v_b_3542_);
                    return v_b_3542_;
                } else {
                    v___x_3544_ = leanh::lean_box(0);
                    v_a_3545_ = lean_array_uget_borrowed(v_as_3539_, v_i_3541_);
                    v___x_3546_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__12___redArg(v_processing_3538_, v_a_3545_);
                    if v___x_3546_ == 0 {
                        v___x_3547_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__16___closed__0;
                        v___x_3548_ = 1usize;
                        v___x_3549_ = lean_usize_add(v_i_3541_, v___x_3548_);
                        v_i_3541_ = v___x_3549_;
                        v_b_3542_ = v___x_3547_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3545_);
                        v___x_3551_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3551_, 0, v_a_3545_);
                        v___x_3552_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3552_, 0, v___x_3551_);
                        v___x_3553_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3553_, 0, v___x_3552_);
                        leanh::lean_ctor_set(v___x_3553_, 1, v___x_3544_);
                        return v___x_3553_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__13___boxed(
    mut v_processing_3554_: *mut leanh::LeanObject,
    mut v_as_3555_: *mut leanh::LeanObject,
    mut v_sz_3556_: *mut leanh::LeanObject,
    mut v_i_3557_: *mut leanh::LeanObject,
    mut v_b_3558_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3559_: usize = 0;
    let mut v_i_boxed_3560_: usize = 0;
    let mut v_res_3561_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3559_ = leanh::lean_unbox_usize(v_sz_3556_);
    leanh::lean_dec(v_sz_3556_);
    v_i_boxed_3560_ = leanh::lean_unbox_usize(v_i_3557_);
    leanh::lean_dec(v_i_3557_);
    v_res_3561_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__13(v_processing_3554_, v_as_3555_, v_sz_boxed_3559_, v_i_boxed_3560_, v_b_3558_);
    leanh::lean_dec_ref(v_b_3558_);
    leanh::lean_dec_ref(v_as_3555_);
    leanh::lean_dec_ref(v_processing_3554_);
    return v_res_3561_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__11_spec__14_spec__26___redArg(
    mut v_x_3562_: *mut leanh::LeanObject,
    mut v_x_3563_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_3564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3569_: u8 = 0;
    let mut v___x_3570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: u64 = 0;
    let mut v___x_3572_: u64 = 0;
    let mut v___x_3573_: u64 = 0;
    let mut v_fold_3574_: u64 = 0;
    let mut v___x_3575_: u64 = 0;
    let mut v___x_3576_: u64 = 0;
    let mut v___x_3577_: u64 = 0;
    let mut v___x_3578_: usize = 0;
    let mut v___x_3579_: usize = 0;
    let mut v___x_3580_: usize = 0;
    let mut v___x_3581_: usize = 0;
    let mut v___x_3582_: usize = 0;
    let mut v___x_3583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3589_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3563_) == 0 {
                    return v_x_3562_;
                } else {
                    v_key_3564_ = leanh::lean_ctor_get(v_x_3563_, 0);
                    v_value_3565_ = leanh::lean_ctor_get(v_x_3563_, 1);
                    v_tail_3566_ = leanh::lean_ctor_get(v_x_3563_, 2);
                    v_isSharedCheck_3589_ = (!leanh::lean_is_exclusive(v_x_3563_)) as u8;
                    if v_isSharedCheck_3589_ == 0 {
                        v___x_3568_ = v_x_3563_;
                        v_isShared_3569_ = v_isSharedCheck_3589_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_3566_);
                        leanh::lean_inc(v_value_3565_);
                        leanh::lean_inc(v_key_3564_);
                        leanh::lean_dec(v_x_3563_);
                        v___x_3568_ = leanh::lean_box(0);
                        v_isShared_3569_ = v_isSharedCheck_3589_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3570_ = lean_array_get_size(v_x_3562_);
                v___x_3571_ = l_Lean_Expr_hash(v_key_3564_);
                v___x_3572_ = 32u64;
                v___x_3573_ = lean_uint64_shift_right(v___x_3571_, v___x_3572_);
                v_fold_3574_ = lean_uint64_xor(v___x_3571_, v___x_3573_);
                v___x_3575_ = 16u64;
                v___x_3576_ = lean_uint64_shift_right(v_fold_3574_, v___x_3575_);
                v___x_3577_ = lean_uint64_xor(v_fold_3574_, v___x_3576_);
                v___x_3578_ = lean_uint64_to_usize(v___x_3577_);
                v___x_3579_ = lean_usize_of_nat(v___x_3570_);
                v___x_3580_ = 1usize;
                v___x_3581_ = lean_usize_sub(v___x_3579_, v___x_3580_);
                v___x_3582_ = lean_usize_land(v___x_3578_, v___x_3581_);
                v___x_3583_ = lean_array_uget_borrowed(v_x_3562_, v___x_3582_);
                leanh::lean_inc(v___x_3583_);
                if v_isShared_3569_ == 0 {
                    leanh::lean_ctor_set(v___x_3568_, 2, v___x_3583_);
                    v___x_3585_ = v___x_3568_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3588_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3588_, 0, v_key_3564_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3588_, 1, v_value_3565_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3588_, 2, v___x_3583_);
                    v___x_3585_ = v_reuseFailAlloc_3588_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3586_ = lean_array_uset(v_x_3562_, v___x_3582_, v___x_3585_);
                v_x_3562_ = v___x_3586_;
                v_x_3563_ = v_tail_3566_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__11_spec__14___redArg(
    mut v_i_3590_: *mut leanh::LeanObject,
    mut v_source_3591_: *mut leanh::LeanObject,
    mut v_target_3592_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: u8 = 0;
    let mut v_es_3595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_3597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_3598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3593_ = lean_array_get_size(v_source_3591_);
                v___x_3594_ = lean_nat_dec_lt(v_i_3590_, v___x_3593_);
                if v___x_3594_ == 0 {
                    leanh::lean_dec_ref(v_source_3591_);
                    leanh::lean_dec(v_i_3590_);
                    return v_target_3592_;
                } else {
                    v_es_3595_ = lean_array_fget(v_source_3591_, v_i_3590_);
                    v___x_3596_ = leanh::lean_box(0);
                    v_source_3597_ = lean_array_fset(v_source_3591_, v_i_3590_, v___x_3596_);
                    v_target_3598_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__11_spec__14_spec__26___redArg(v_target_3592_, v_es_3595_);
                    v___x_3599_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3600_ = lean_nat_add(v_i_3590_, v___x_3599_);
                    leanh::lean_dec(v_i_3590_);
                    v_i_3590_ = v___x_3600_;
                    v_source_3591_ = v_source_3597_;
                    v_target_3592_ = v_target_3598_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__11___redArg(
    mut v_data_3602_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_3605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3603_ = lean_array_get_size(v_data_3602_);
    v___x_3604_ = leanh::lean_unsigned_to_nat(2);
    v_nbuckets_3605_ = lean_nat_mul(v___x_3603_, v___x_3604_);
    v___x_3606_ = leanh::lean_unsigned_to_nat(0);
    v___x_3607_ = leanh::lean_box(0);
    v___x_3608_ = lean_mk_array(v_nbuckets_3605_, v___x_3607_);
    v___x_3609_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__11_spec__14___redArg(v___x_3606_, v_data_3602_, v___x_3608_);
    return v___x_3609_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8___redArg(
    mut v_m_3610_: *mut leanh::LeanObject,
    mut v_a_3611_: *mut leanh::LeanObject,
    mut v_b_3612_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_3613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: u64 = 0;
    let mut v___x_3617_: u64 = 0;
    let mut v___x_3618_: u64 = 0;
    let mut v_fold_3619_: u64 = 0;
    let mut v___x_3620_: u64 = 0;
    let mut v___x_3621_: u64 = 0;
    let mut v___x_3622_: u64 = 0;
    let mut v___x_3623_: usize = 0;
    let mut v___x_3624_: usize = 0;
    let mut v___x_3625_: usize = 0;
    let mut v___x_3626_: usize = 0;
    let mut v___x_3627_: usize = 0;
    let mut v_bkt_3628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: u8 = 0;
    let mut v___x_3631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3632_: u8 = 0;
    let mut v___x_3633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3642_: u8 = 0;
    let mut v_val_3643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3650_: u8 = 0;
    let mut v_unused_3651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3613_ = leanh::lean_ctor_get(v_m_3610_, 0);
                v_buckets_3614_ = leanh::lean_ctor_get(v_m_3610_, 1);
                v___x_3615_ = lean_array_get_size(v_buckets_3614_);
                v___x_3616_ = l_Lean_Expr_hash(v_a_3611_);
                v___x_3617_ = 32u64;
                v___x_3618_ = lean_uint64_shift_right(v___x_3616_, v___x_3617_);
                v_fold_3619_ = lean_uint64_xor(v___x_3616_, v___x_3618_);
                v___x_3620_ = 16u64;
                v___x_3621_ = lean_uint64_shift_right(v_fold_3619_, v___x_3620_);
                v___x_3622_ = lean_uint64_xor(v_fold_3619_, v___x_3621_);
                v___x_3623_ = lean_uint64_to_usize(v___x_3622_);
                v___x_3624_ = lean_usize_of_nat(v___x_3615_);
                v___x_3625_ = 1usize;
                v___x_3626_ = lean_usize_sub(v___x_3624_, v___x_3625_);
                v___x_3627_ = lean_usize_land(v___x_3623_, v___x_3626_);
                v_bkt_3628_ = lean_array_uget_borrowed(v_buckets_3614_, v___x_3627_);
                v___x_3629_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__10___redArg(v_a_3611_, v_bkt_3628_);
                if v___x_3629_ == 0 {
                    leanh::lean_inc_ref(v_buckets_3614_);
                    leanh::lean_inc(v_size_3613_);
                    v_isSharedCheck_3650_ = (!leanh::lean_is_exclusive(v_m_3610_)) as u8;
                    if v_isSharedCheck_3650_ == 0 {
                        v_unused_3651_ = leanh::lean_ctor_get(v_m_3610_, 1);
                        leanh::lean_dec(v_unused_3651_);
                        v_unused_3652_ = leanh::lean_ctor_get(v_m_3610_, 0);
                        leanh::lean_dec(v_unused_3652_);
                        v___x_3631_ = v_m_3610_;
                        v_isShared_3632_ = v_isSharedCheck_3650_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_m_3610_);
                        v___x_3631_ = leanh::lean_box(0);
                        v_isShared_3632_ = v_isSharedCheck_3650_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_b_3612_);
                    leanh::lean_dec_ref(v_a_3611_);
                    return v_m_3610_;
                }
            }
            1 => {
                v___x_3633_ = leanh::lean_unsigned_to_nat(1);
                v_size_x27_3634_ = lean_nat_add(v_size_3613_, v___x_3633_);
                leanh::lean_dec(v_size_3613_);
                leanh::lean_inc(v_bkt_3628_);
                v___x_3635_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3635_, 0, v_a_3611_);
                leanh::lean_ctor_set(v___x_3635_, 1, v_b_3612_);
                leanh::lean_ctor_set(v___x_3635_, 2, v_bkt_3628_);
                v_buckets_x27_3636_ = lean_array_uset(v_buckets_3614_, v___x_3627_, v___x_3635_);
                v___x_3637_ = leanh::lean_unsigned_to_nat(4);
                v___x_3638_ = lean_nat_mul(v_size_x27_3634_, v___x_3637_);
                v___x_3639_ = leanh::lean_unsigned_to_nat(3);
                v___x_3640_ = lean_nat_div(v___x_3638_, v___x_3639_);
                leanh::lean_dec(v___x_3638_);
                v___x_3641_ = lean_array_get_size(v_buckets_x27_3636_);
                v___x_3642_ = lean_nat_dec_le(v___x_3640_, v___x_3641_);
                leanh::lean_dec(v___x_3640_);
                if v___x_3642_ == 0 {
                    v_val_3643_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__11___redArg(v_buckets_x27_3636_);
                    if v_isShared_3632_ == 0 {
                        leanh::lean_ctor_set(v___x_3631_, 1, v_val_3643_);
                        leanh::lean_ctor_set(v___x_3631_, 0, v_size_x27_3634_);
                        v___x_3645_ = v___x_3631_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3646_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3646_, 0, v_size_x27_3634_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3646_, 1, v_val_3643_);
                        v___x_3645_ = v_reuseFailAlloc_3646_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_3632_ == 0 {
                        leanh::lean_ctor_set(v___x_3631_, 1, v_buckets_x27_3636_);
                        leanh::lean_ctor_set(v___x_3631_, 0, v_size_x27_3634_);
                        v___x_3648_ = v___x_3631_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3649_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3649_, 0, v_size_x27_3634_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3649_, 1, v_buckets_x27_3636_);
                        v___x_3648_ = v_reuseFailAlloc_3649_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3645_;
            }
            3 => {
                return v___x_3648_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__9___redArg(
    mut v_e_3653_: *mut leanh::LeanObject,
    mut v___y_3654_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3656_: u8 = 0;
    let mut v___x_3657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_3666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3670_: u8 = 0;
    let mut v___x_3672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3676_: u8 = 0;
    let mut v_unused_3677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3656_ = l_Lean_Expr_hasMVar(v_e_3653_);
                if v___x_3656_ == 0 {
                    v___x_3657_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3657_, 0, v_e_3653_);
                    return v___x_3657_;
                } else {
                    v___x_3658_ = lean_st_ref_get(v___y_3654_);
                    v_mctx_3659_ = leanh::lean_ctor_get(v___x_3658_, 0);
                    leanh::lean_inc_ref(v_mctx_3659_);
                    leanh::lean_dec(v___x_3658_);
                    v___x_3660_ = l_Lean_instantiateMVarsCore(v_mctx_3659_, v_e_3653_);
                    v_fst_3661_ = leanh::lean_ctor_get(v___x_3660_, 0);
                    leanh::lean_inc(v_fst_3661_);
                    v_snd_3662_ = leanh::lean_ctor_get(v___x_3660_, 1);
                    leanh::lean_inc(v_snd_3662_);
                    leanh::lean_dec_ref(v___x_3660_);
                    v___x_3663_ = lean_st_ref_take(v___y_3654_);
                    v_cache_3664_ = leanh::lean_ctor_get(v___x_3663_, 1);
                    v_zetaDeltaFVarIds_3665_ = leanh::lean_ctor_get(v___x_3663_, 2);
                    v_postponed_3666_ = leanh::lean_ctor_get(v___x_3663_, 3);
                    v_diag_3667_ = leanh::lean_ctor_get(v___x_3663_, 4);
                    v_isSharedCheck_3676_ = (!leanh::lean_is_exclusive(v___x_3663_)) as u8;
                    if v_isSharedCheck_3676_ == 0 {
                        v_unused_3677_ = leanh::lean_ctor_get(v___x_3663_, 0);
                        leanh::lean_dec(v_unused_3677_);
                        v___x_3669_ = v___x_3663_;
                        v_isShared_3670_ = v_isSharedCheck_3676_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_diag_3667_);
                        leanh::lean_inc(v_postponed_3666_);
                        leanh::lean_inc(v_zetaDeltaFVarIds_3665_);
                        leanh::lean_inc(v_cache_3664_);
                        leanh::lean_dec(v___x_3663_);
                        v___x_3669_ = leanh::lean_box(0);
                        v_isShared_3670_ = v_isSharedCheck_3676_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3670_ == 0 {
                    leanh::lean_ctor_set(v___x_3669_, 0, v_snd_3662_);
                    v___x_3672_ = v___x_3669_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3675_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3675_, 0, v_snd_3662_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3675_, 1, v_cache_3664_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3675_,
                        2,
                        v_zetaDeltaFVarIds_3665_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3675_, 3, v_postponed_3666_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3675_, 4, v_diag_3667_);
                    v___x_3672_ = v_reuseFailAlloc_3675_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3673_ = lean_st_ref_set(v___y_3654_, v___x_3672_);
                v___x_3674_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3674_, 0, v_fst_3661_);
                return v___x_3674_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__9___redArg___boxed(
    mut v_e_3678_: *mut leanh::LeanObject,
    mut v___y_3679_: *mut leanh::LeanObject,
    mut v___y_3680_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3681_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3681_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__9___redArg(v_e_3678_, v___y_3679_);
    leanh::lean_dec(v___y_3679_);
    return v_res_3681_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__10(
    mut v_sz_3682_: usize,
    mut v_i_3683_: usize,
    mut v_bs_3684_: *mut leanh::LeanObject,
    mut v___y_3685_: *mut leanh::LeanObject,
    mut v___y_3686_: *mut leanh::LeanObject,
    mut v___y_3687_: *mut leanh::LeanObject,
    mut v___y_3688_: *mut leanh::LeanObject,
    mut v___y_3689_: *mut leanh::LeanObject,
    mut v___y_3690_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3692_: u8 = 0;
    let mut v___x_3693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3699_: usize = 0;
    let mut v___x_3700_: usize = 0;
    let mut v___x_3701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3706_: u8 = 0;
    let mut v___x_3708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3710_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3692_ = lean_usize_dec_lt(v_i_3683_, v_sz_3682_);
                if v___x_3692_ == 0 {
                    v___x_3693_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3693_, 0, v_bs_3684_);
                    return v___x_3693_;
                } else {
                    v_v_3694_ = lean_array_uget_borrowed(v_bs_3684_, v_i_3683_);
                    leanh::lean_inc(v_v_3694_);
                    v___x_3695_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__9___redArg(v_v_3694_, v___y_3688_);
                    if leanh::lean_obj_tag(v___x_3695_) == 0 {
                        v_a_3696_ = leanh::lean_ctor_get(v___x_3695_, 0);
                        leanh::lean_inc(v_a_3696_);
                        leanh::lean_dec_ref_known(v___x_3695_, 1);
                        v___x_3697_ = leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_3698_ = lean_array_uset(v_bs_3684_, v_i_3683_, v___x_3697_);
                        v___x_3699_ = 1usize;
                        v___x_3700_ = lean_usize_add(v_i_3683_, v___x_3699_);
                        v___x_3701_ = lean_array_uset(v_bs_x27_3698_, v_i_3683_, v_a_3696_);
                        v_i_3683_ = v___x_3700_;
                        v_bs_3684_ = v___x_3701_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_bs_3684_);
                        v_a_3703_ = leanh::lean_ctor_get(v___x_3695_, 0);
                        v_isSharedCheck_3710_ =
                            (!leanh::lean_is_exclusive(v___x_3695_)) as u8;
                        if v_isSharedCheck_3710_ == 0 {
                            v___x_3705_ = v___x_3695_;
                            v_isShared_3706_ = v_isSharedCheck_3710_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3703_);
                            leanh::lean_dec(v___x_3695_);
                            v___x_3705_ = leanh::lean_box(0);
                            v_isShared_3706_ = v_isSharedCheck_3710_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3706_ == 0 {
                    v___x_3708_ = v___x_3705_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3709_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3709_, 0, v_a_3703_);
                    v___x_3708_ = v_reuseFailAlloc_3709_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3708_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__10___boxed(
    mut v_sz_3711_: *mut leanh::LeanObject,
    mut v_i_3712_: *mut leanh::LeanObject,
    mut v_bs_3713_: *mut leanh::LeanObject,
    mut v___y_3714_: *mut leanh::LeanObject,
    mut v___y_3715_: *mut leanh::LeanObject,
    mut v___y_3716_: *mut leanh::LeanObject,
    mut v___y_3717_: *mut leanh::LeanObject,
    mut v___y_3718_: *mut leanh::LeanObject,
    mut v___y_3719_: *mut leanh::LeanObject,
    mut v___y_3720_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3721_: usize = 0;
    let mut v_i_boxed_3722_: usize = 0;
    let mut v_res_3723_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3721_ = leanh::lean_unbox_usize(v_sz_3711_);
    leanh::lean_dec(v_sz_3711_);
    v_i_boxed_3722_ = leanh::lean_unbox_usize(v_i_3712_);
    leanh::lean_dec(v_i_3712_);
    v_res_3723_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__10(v_sz_boxed_3721_, v_i_boxed_3722_, v_bs_3713_, v___y_3714_, v___y_3715_, v___y_3716_, v___y_3717_, v___y_3718_, v___y_3719_);
    leanh::lean_dec(v___y_3719_);
    leanh::lean_dec_ref(v___y_3718_);
    leanh::lean_dec(v___y_3717_);
    leanh::lean_dec_ref(v___y_3716_);
    leanh::lean_dec(v___y_3715_);
    leanh::lean_dec_ref(v___y_3714_);
    return v_res_3723_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__21(
    mut v_opts_3724_: *mut leanh::LeanObject,
    mut v_opt_3725_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_name_3726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_3727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_3728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3729_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_3726_ = leanh::lean_ctor_get(v_opt_3725_, 0);
    v_defValue_3727_ = leanh::lean_ctor_get(v_opt_3725_, 1);
    v_map_3728_ = leanh::lean_ctor_get(v_opts_3724_, 0);
    v___x_3729_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3728_,
            v_name_3726_,
        );
    if leanh::lean_obj_tag(v___x_3729_) == 0 {
        let mut v___x_3730_: u8 = 0;
        v___x_3730_ = (leanh::lean_unbox(v_defValue_3727_) as u8);
        return v___x_3730_;
    } else {
        let mut v_val_3731_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_3731_ = leanh::lean_ctor_get(v___x_3729_, 0);
        leanh::lean_inc(v_val_3731_);
        leanh::lean_dec_ref_known(v___x_3729_, 1);
        if leanh::lean_obj_tag(v_val_3731_) == 1 {
            let mut v_v_3732_: u8 = 0;
            v_v_3732_ = leanh::lean_ctor_get_uint8(v_val_3731_, 0 as u32);
            leanh::lean_dec_ref_known(v_val_3731_, 0);
            return v_v_3732_;
        } else {
            let mut v___x_3733_: u8 = 0;
            leanh::lean_dec(v_val_3731_);
            v___x_3733_ = (leanh::lean_unbox(v_defValue_3727_) as u8);
            return v___x_3733_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__21___boxed(
    mut v_opts_3734_: *mut leanh::LeanObject,
    mut v_opt_3735_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3736_: u8 = 0;
    let mut v_r_3737_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3736_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__21(v_opts_3734_, v_opt_3735_);
    leanh::lean_dec_ref(v_opt_3735_);
    leanh::lean_dec_ref(v_opts_3734_);
    v_r_3737_ = leanh::lean_box((v_res_3736_) as usize);
    return v_r_3737_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__22___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3739_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3738_ = leanh::lean_box(1);
    v___x_3739_ = l_Lean_MessageData_ofFormat(v___x_3738_);
    return v___x_3739_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__22___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3744_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3743_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__22___closed__2;
    v___x_3744_ = l_Lean_MessageData_ofFormat(v___x_3743_);
    return v___x_3744_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__22(
    mut v_x_3745_: *mut leanh::LeanObject,
    mut v_x_3746_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_3747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3751_: u8 = 0;
    let mut v_before_3752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3755_: u8 = 0;
    let mut v___x_3756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3768_: u8 = 0;
    let mut v_unused_3769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3770_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3746_) == 0 {
                    return v_x_3745_;
                } else {
                    v_head_3747_ = leanh::lean_ctor_get(v_x_3746_, 0);
                    v_tail_3748_ = leanh::lean_ctor_get(v_x_3746_, 1);
                    v_isSharedCheck_3770_ = (!leanh::lean_is_exclusive(v_x_3746_)) as u8;
                    if v_isSharedCheck_3770_ == 0 {
                        v___x_3750_ = v_x_3746_;
                        v_isShared_3751_ = v_isSharedCheck_3770_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_3748_);
                        leanh::lean_inc(v_head_3747_);
                        leanh::lean_dec(v_x_3746_);
                        v___x_3750_ = leanh::lean_box(0);
                        v_isShared_3751_ = v_isSharedCheck_3770_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_3752_ = leanh::lean_ctor_get(v_head_3747_, 0);
                v_isSharedCheck_3768_ = (!leanh::lean_is_exclusive(v_head_3747_)) as u8;
                if v_isSharedCheck_3768_ == 0 {
                    v_unused_3769_ = leanh::lean_ctor_get(v_head_3747_, 1);
                    leanh::lean_dec(v_unused_3769_);
                    v___x_3754_ = v_head_3747_;
                    v_isShared_3755_ = v_isSharedCheck_3768_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_before_3752_);
                    leanh::lean_dec(v_head_3747_);
                    v___x_3754_ = leanh::lean_box(0);
                    v_isShared_3755_ = v_isSharedCheck_3768_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3756_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__22___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__22___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__22___closed__0);
                if v_isShared_3755_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3754_, 7);
                    leanh::lean_ctor_set(v___x_3754_, 1, v___x_3756_);
                    leanh::lean_ctor_set(v___x_3754_, 0, v_x_3745_);
                    v___x_3758_ = v___x_3754_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3767_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3767_, 0, v_x_3745_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3767_, 1, v___x_3756_);
                    v___x_3758_ = v_reuseFailAlloc_3767_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3759_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__22___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__22___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__22___closed__3);
                if v_isShared_3751_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3750_, 7);
                    leanh::lean_ctor_set(v___x_3750_, 1, v___x_3759_);
                    leanh::lean_ctor_set(v___x_3750_, 0, v___x_3758_);
                    v___x_3761_ = v___x_3750_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3766_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3766_, 0, v___x_3758_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3766_, 1, v___x_3759_);
                    v___x_3761_ = v_reuseFailAlloc_3766_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3762_ = l_Lean_MessageData_ofSyntax(v_before_3752_);
                v___x_3763_ = l_Lean_indentD(v___x_3762_);
                v___x_3764_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3764_, 0, v___x_3761_);
                leanh::lean_ctor_set(v___x_3764_, 1, v___x_3763_);
                v_x_3745_ = v___x_3764_;
                v_x_3746_ = v_tail_3748_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_3774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3775_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3774_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18___redArg___closed__1;
    v___x_3775_ = l_Lean_MessageData_ofFormat(v___x_3774_);
    return v___x_3775_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18___redArg(
    mut v_msgData_3776_: *mut leanh::LeanObject,
    mut v_macroStack_3777_: *mut leanh::LeanObject,
    mut v___y_3778_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_options_3780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3782_: u8 = 0;
    let mut v___x_3783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_after_3786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3789_: u8 = 0;
    let mut v___x_3790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgData_3797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3801_: u8 = 0;
    let mut v_unused_3802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_3780_ = leanh::lean_ctor_get(v___y_3778_, 2);
                v___x_3781_ = l_Lean_Elab_pp_macroStack;
                v___x_3782_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__21(v_options_3780_, v___x_3781_);
                if v___x_3782_ == 0 {
                    leanh::lean_dec(v_macroStack_3777_);
                    v___x_3783_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3783_, 0, v_msgData_3776_);
                    return v___x_3783_;
                } else {
                    if leanh::lean_obj_tag(v_macroStack_3777_) == 0 {
                        v___x_3784_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3784_, 0, v_msgData_3776_);
                        return v___x_3784_;
                    } else {
                        v_head_3785_ = leanh::lean_ctor_get(v_macroStack_3777_, 0);
                        leanh::lean_inc(v_head_3785_);
                        v_after_3786_ = leanh::lean_ctor_get(v_head_3785_, 1);
                        v_isSharedCheck_3801_ =
                            (!leanh::lean_is_exclusive(v_head_3785_)) as u8;
                        if v_isSharedCheck_3801_ == 0 {
                            v_unused_3802_ = leanh::lean_ctor_get(v_head_3785_, 0);
                            leanh::lean_dec(v_unused_3802_);
                            v___x_3788_ = v_head_3785_;
                            v_isShared_3789_ = v_isSharedCheck_3801_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_after_3786_);
                            leanh::lean_dec(v_head_3785_);
                            v___x_3788_ = leanh::lean_box(0);
                            v_isShared_3789_ = v_isSharedCheck_3801_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3790_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__22___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__22___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__22___closed__0);
                if v_isShared_3789_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3788_, 7);
                    leanh::lean_ctor_set(v___x_3788_, 1, v___x_3790_);
                    leanh::lean_ctor_set(v___x_3788_, 0, v_msgData_3776_);
                    v___x_3792_ = v___x_3788_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3800_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3800_, 0, v_msgData_3776_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3800_, 1, v___x_3790_);
                    v___x_3792_ = v_reuseFailAlloc_3800_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3793_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18___redArg___closed__2);
                v___x_3794_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3794_, 0, v___x_3792_);
                leanh::lean_ctor_set(v___x_3794_, 1, v___x_3793_);
                v___x_3795_ = l_Lean_MessageData_ofSyntax(v_after_3786_);
                v___x_3796_ = l_Lean_indentD(v___x_3795_);
                v_msgData_3797_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v_msgData_3797_, 0, v___x_3794_);
                leanh::lean_ctor_set(v_msgData_3797_, 1, v___x_3796_);
                v___x_3798_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__22(v_msgData_3797_, v_macroStack_3777_);
                v___x_3799_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3799_, 0, v___x_3798_);
                return v___x_3799_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18___redArg___boxed(
    mut v_msgData_3803_: *mut leanh::LeanObject,
    mut v_macroStack_3804_: *mut leanh::LeanObject,
    mut v___y_3805_: *mut leanh::LeanObject,
    mut v___y_3806_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3807_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3807_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18___redArg(v_msgData_3803_, v_macroStack_3804_, v___y_3805_);
    leanh::lean_dec_ref(v___y_3805_);
    return v_res_3807_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3_spec__4(
    mut v_msgData_3808_: *mut leanh::LeanObject,
    mut v___y_3809_: *mut leanh::LeanObject,
    mut v___y_3810_: *mut leanh::LeanObject,
    mut v___y_3811_: *mut leanh::LeanObject,
    mut v___y_3812_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3822_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3814_ = lean_st_ref_get(v___y_3812_);
    v_env_3815_ = leanh::lean_ctor_get(v___x_3814_, 0);
    leanh::lean_inc_ref(v_env_3815_);
    leanh::lean_dec(v___x_3814_);
    v___x_3816_ = lean_st_ref_get(v___y_3810_);
    v_mctx_3817_ = leanh::lean_ctor_get(v___x_3816_, 0);
    leanh::lean_inc_ref(v_mctx_3817_);
    leanh::lean_dec(v___x_3816_);
    v_lctx_3818_ = leanh::lean_ctor_get(v___y_3809_, 2);
    v_options_3819_ = leanh::lean_ctor_get(v___y_3811_, 2);
    leanh::lean_inc_ref(v_options_3819_);
    leanh::lean_inc_ref(v_lctx_3818_);
    v___x_3820_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_3820_, 0, v_env_3815_);
    leanh::lean_ctor_set(v___x_3820_, 1, v_mctx_3817_);
    leanh::lean_ctor_set(v___x_3820_, 2, v_lctx_3818_);
    leanh::lean_ctor_set(v___x_3820_, 3, v_options_3819_);
    v___x_3821_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3821_, 0, v___x_3820_);
    leanh::lean_ctor_set(v___x_3821_, 1, v_msgData_3808_);
    v___x_3822_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3822_, 0, v___x_3821_);
    return v___x_3822_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3_spec__4___boxed(
    mut v_msgData_3823_: *mut leanh::LeanObject,
    mut v___y_3824_: *mut leanh::LeanObject,
    mut v___y_3825_: *mut leanh::LeanObject,
    mut v___y_3826_: *mut leanh::LeanObject,
    mut v___y_3827_: *mut leanh::LeanObject,
    mut v___y_3828_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3829_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3829_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3_spec__4(v_msgData_3823_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_);
    leanh::lean_dec(v___y_3827_);
    leanh::lean_dec_ref(v___y_3826_);
    leanh::lean_dec(v___y_3825_);
    leanh::lean_dec_ref(v___y_3824_);
    return v_res_3829_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14___redArg(
    mut v_msg_3830_: *mut leanh::LeanObject,
    mut v___y_3831_: *mut leanh::LeanObject,
    mut v___y_3832_: *mut leanh::LeanObject,
    mut v___y_3833_: *mut leanh::LeanObject,
    mut v___y_3834_: *mut leanh::LeanObject,
    mut v___y_3835_: *mut leanh::LeanObject,
    mut v___y_3836_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_3838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_3841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3847_: u8 = 0;
    let mut v___x_3848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3852_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3838_ = leanh::lean_ctor_get(v___y_3835_, 5);
                v___x_3839_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3_spec__4(v_msg_3830_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_);
                v_a_3840_ = leanh::lean_ctor_get(v___x_3839_, 0);
                leanh::lean_inc(v_a_3840_);
                leanh::lean_dec_ref(v___x_3839_);
                v_macroStack_3841_ = leanh::lean_ctor_get(v___y_3831_, 1);
                v___x_3842_ = l_Lean_Elab_getBetterRef(v_ref_3838_, v_macroStack_3841_);
                leanh::lean_inc(v_macroStack_3841_);
                v___x_3843_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18___redArg(v_a_3840_, v_macroStack_3841_, v___y_3835_);
                v_a_3844_ = leanh::lean_ctor_get(v___x_3843_, 0);
                v_isSharedCheck_3852_ = (!leanh::lean_is_exclusive(v___x_3843_)) as u8;
                if v_isSharedCheck_3852_ == 0 {
                    v___x_3846_ = v___x_3843_;
                    v_isShared_3847_ = v_isSharedCheck_3852_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_3844_);
                    leanh::lean_dec(v___x_3843_);
                    v___x_3846_ = leanh::lean_box(0);
                    v_isShared_3847_ = v_isSharedCheck_3852_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3848_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3848_, 0, v___x_3842_);
                leanh::lean_ctor_set(v___x_3848_, 1, v_a_3844_);
                if v_isShared_3847_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3846_, 1);
                    leanh::lean_ctor_set(v___x_3846_, 0, v___x_3848_);
                    v___x_3850_ = v___x_3846_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3851_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3851_, 0, v___x_3848_);
                    v___x_3850_ = v_reuseFailAlloc_3851_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3850_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14___redArg___boxed(
    mut v_msg_3853_: *mut leanh::LeanObject,
    mut v___y_3854_: *mut leanh::LeanObject,
    mut v___y_3855_: *mut leanh::LeanObject,
    mut v___y_3856_: *mut leanh::LeanObject,
    mut v___y_3857_: *mut leanh::LeanObject,
    mut v___y_3858_: *mut leanh::LeanObject,
    mut v___y_3859_: *mut leanh::LeanObject,
    mut v___y_3860_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3861_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3861_ = l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14___redArg(v_msg_3853_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_);
    leanh::lean_dec(v___y_3859_);
    leanh::lean_dec_ref(v___y_3858_);
    leanh::lean_dec(v___y_3857_);
    leanh::lean_dec_ref(v___y_3856_);
    leanh::lean_dec(v___y_3855_);
    leanh::lean_dec_ref(v___y_3854_);
    return v_res_3861_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__4(
    mut v_x_3862_: *mut leanh::LeanObject,
    mut v_x_3863_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_3863_) == 0 {
        leanh::lean_inc(v_x_3862_);
        return v_x_3862_;
    } else {
        let mut v_key_3864_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_3865_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3866_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3867_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_key_3864_ = leanh::lean_ctor_get(v_x_3863_, 0);
        v_tail_3865_ = leanh::lean_ctor_get(v_x_3863_, 2);
        v___x_3866_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__4(v_x_3862_, v_tail_3865_);
        leanh::lean_inc(v_key_3864_);
        v___x_3867_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_3867_, 0, v_key_3864_);
        leanh::lean_ctor_set(v___x_3867_, 1, v___x_3866_);
        return v___x_3867_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__4___boxed(
    mut v_x_3868_: *mut leanh::LeanObject,
    mut v_x_3869_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3870_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3870_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__4(v_x_3868_, v_x_3869_);
    leanh::lean_dec(v_x_3869_);
    leanh::lean_dec(v_x_3868_);
    return v_res_3870_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__5(
    mut v_as_3871_: *mut leanh::LeanObject,
    mut v_i_3872_: usize,
    mut v_stop_3873_: usize,
    mut v_b_3874_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3875_: u8 = 0;
    let mut v___x_3876_: usize = 0;
    let mut v___x_3877_: usize = 0;
    let mut v___x_3878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3875_ = lean_usize_dec_eq(v_i_3872_, v_stop_3873_);
                if v___x_3875_ == 0 {
                    v___x_3876_ = 1usize;
                    v___x_3877_ = lean_usize_sub(v_i_3872_, v___x_3876_);
                    v___x_3878_ = lean_array_uget_borrowed(v_as_3871_, v___x_3877_);
                    v___x_3879_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__4(v_b_3874_, v___x_3878_);
                    leanh::lean_dec(v_b_3874_);
                    v_i_3872_ = v___x_3877_;
                    v_b_3874_ = v___x_3879_;
                    state = 0;
                    continue;
                } else {
                    return v_b_3874_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__5___boxed(
    mut v_as_3881_: *mut leanh::LeanObject,
    mut v_i_3882_: *mut leanh::LeanObject,
    mut v_stop_3883_: *mut leanh::LeanObject,
    mut v_b_3884_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_3885_: usize = 0;
    let mut v_stop_boxed_3886_: usize = 0;
    let mut v_res_3887_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3885_ = leanh::lean_unbox_usize(v_i_3882_);
    leanh::lean_dec(v_i_3882_);
    v_stop_boxed_3886_ = leanh::lean_unbox_usize(v_stop_3883_);
    leanh::lean_dec(v_stop_3883_);
    v_res_3887_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__5(v_as_3881_, v_i_boxed_3885_, v_stop_boxed_3886_, v_b_3884_);
    leanh::lean_dec_ref(v_as_3881_);
    return v_res_3887_;
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__2(
    mut v_a_3888_: *mut leanh::LeanObject,
    mut v_a_3889_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3895_: u8 = 0;
    let mut v___x_3896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3901_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_3888_) == 0 {
                    v___x_3890_ = l_List_reverse___redArg(v_a_3889_);
                    return v___x_3890_;
                } else {
                    v_head_3891_ = leanh::lean_ctor_get(v_a_3888_, 0);
                    v_tail_3892_ = leanh::lean_ctor_get(v_a_3888_, 1);
                    v_isSharedCheck_3901_ = (!leanh::lean_is_exclusive(v_a_3888_)) as u8;
                    if v_isSharedCheck_3901_ == 0 {
                        v___x_3894_ = v_a_3888_;
                        v_isShared_3895_ = v_isSharedCheck_3901_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_3892_);
                        leanh::lean_inc(v_head_3891_);
                        leanh::lean_dec(v_a_3888_);
                        v___x_3894_ = leanh::lean_box(0);
                        v_isShared_3895_ = v_isSharedCheck_3901_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3896_ = l_Lean_MessageData_ofExpr(v_head_3891_);
                if v_isShared_3895_ == 0 {
                    leanh::lean_ctor_set(v___x_3894_, 1, v_a_3889_);
                    leanh::lean_ctor_set(v___x_3894_, 0, v___x_3896_);
                    v___x_3898_ = v___x_3894_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3900_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3900_, 0, v___x_3896_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3900_, 1, v_a_3889_);
                    v___x_3898_ = v_reuseFailAlloc_3900_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_3888_ = v_tail_3892_;
                v_a_3889_ = v___x_3898_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg___closed__0()
-> f64 {
    let mut v___x_3902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3903_: f64 = 0.0;
    v___x_3902_ = leanh::lean_unsigned_to_nat(0);
    v___x_3903_ = lean_float_of_nat(v___x_3902_);
    return v___x_3903_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg(
    mut v_cls_3906_: *mut leanh::LeanObject,
    mut v_msg_3907_: *mut leanh::LeanObject,
    mut v___y_3908_: *mut leanh::LeanObject,
    mut v___y_3909_: *mut leanh::LeanObject,
    mut v___y_3910_: *mut leanh::LeanObject,
    mut v___y_3911_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_3913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3918_: u8 = 0;
    let mut v___x_3919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3931_: u8 = 0;
    let mut v_tid_3932_: u64 = 0;
    let mut v_traces_3933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3936_: u8 = 0;
    let mut v___x_3937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3938_: f64 = 0.0;
    let mut v___x_3939_: u8 = 0;
    let mut v___x_3940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3957_: u8 = 0;
    let mut v_isSharedCheck_3958_: u8 = 0;
    let mut v_isSharedCheck_3959_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3913_ = leanh::lean_ctor_get(v___y_3910_, 5);
                v___x_3914_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3_spec__4(v_msg_3907_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_);
                v_a_3915_ = leanh::lean_ctor_get(v___x_3914_, 0);
                v_isSharedCheck_3959_ = (!leanh::lean_is_exclusive(v___x_3914_)) as u8;
                if v_isSharedCheck_3959_ == 0 {
                    v___x_3917_ = v___x_3914_;
                    v_isShared_3918_ = v_isSharedCheck_3959_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_3915_);
                    leanh::lean_dec(v___x_3914_);
                    v___x_3917_ = leanh::lean_box(0);
                    v_isShared_3918_ = v_isSharedCheck_3959_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3919_ = lean_st_ref_take(v___y_3911_);
                v_traceState_3920_ = leanh::lean_ctor_get(v___x_3919_, 4);
                v_env_3921_ = leanh::lean_ctor_get(v___x_3919_, 0);
                v_nextMacroScope_3922_ = leanh::lean_ctor_get(v___x_3919_, 1);
                v_ngen_3923_ = leanh::lean_ctor_get(v___x_3919_, 2);
                v_auxDeclNGen_3924_ = leanh::lean_ctor_get(v___x_3919_, 3);
                v_cache_3925_ = leanh::lean_ctor_get(v___x_3919_, 5);
                v_messages_3926_ = leanh::lean_ctor_get(v___x_3919_, 6);
                v_infoState_3927_ = leanh::lean_ctor_get(v___x_3919_, 7);
                v_snapshotTasks_3928_ = leanh::lean_ctor_get(v___x_3919_, 8);
                v_isSharedCheck_3958_ = (!leanh::lean_is_exclusive(v___x_3919_)) as u8;
                if v_isSharedCheck_3958_ == 0 {
                    v___x_3930_ = v___x_3919_;
                    v_isShared_3931_ = v_isSharedCheck_3958_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_3928_);
                    leanh::lean_inc(v_infoState_3927_);
                    leanh::lean_inc(v_messages_3926_);
                    leanh::lean_inc(v_cache_3925_);
                    leanh::lean_inc(v_traceState_3920_);
                    leanh::lean_inc(v_auxDeclNGen_3924_);
                    leanh::lean_inc(v_ngen_3923_);
                    leanh::lean_inc(v_nextMacroScope_3922_);
                    leanh::lean_inc(v_env_3921_);
                    leanh::lean_dec(v___x_3919_);
                    v___x_3930_ = leanh::lean_box(0);
                    v_isShared_3931_ = v_isSharedCheck_3958_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_3932_ = leanh::lean_ctor_get_uint64(
                    v_traceState_3920_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_traces_3933_ = leanh::lean_ctor_get(v_traceState_3920_, 0);
                v_isSharedCheck_3957_ =
                    (!leanh::lean_is_exclusive(v_traceState_3920_)) as u8;
                if v_isSharedCheck_3957_ == 0 {
                    v___x_3935_ = v_traceState_3920_;
                    v_isShared_3936_ = v_isSharedCheck_3957_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_traces_3933_);
                    leanh::lean_dec(v_traceState_3920_);
                    v___x_3935_ = leanh::lean_box(0);
                    v_isShared_3936_ = v_isSharedCheck_3957_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3937_ = leanh::lean_box(0);
                v___x_3938_ = leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg___closed__0_once), _init_l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg___closed__0);
                v___x_3939_ = 0;
                v___x_3940_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build___closed__0;
                v___x_3941_ = leanh::lean_alloc_ctor(0, 3, (17) as u32);
                leanh::lean_ctor_set(v___x_3941_, 0, v_cls_3906_);
                leanh::lean_ctor_set(v___x_3941_, 1, v___x_3937_);
                leanh::lean_ctor_set(v___x_3941_, 2, v___x_3940_);
                leanh::lean_ctor_set_float(
                    v___x_3941_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_3938_,
                );
                leanh::lean_ctor_set_float(
                    v___x_3941_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_3938_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_3941_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_3939_,
                );
                v___x_3942_ = l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg___closed__1;
                v___x_3943_ = leanh::lean_alloc_ctor(9, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3943_, 0, v___x_3941_);
                leanh::lean_ctor_set(v___x_3943_, 1, v_a_3915_);
                leanh::lean_ctor_set(v___x_3943_, 2, v___x_3942_);
                leanh::lean_inc(v_ref_3913_);
                v___x_3944_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3944_, 0, v_ref_3913_);
                leanh::lean_ctor_set(v___x_3944_, 1, v___x_3943_);
                v___x_3945_ = l_Lean_PersistentArray_push___redArg(v_traces_3933_, v___x_3944_);
                if v_isShared_3936_ == 0 {
                    leanh::lean_ctor_set(v___x_3935_, 0, v___x_3945_);
                    v___x_3947_ = v___x_3935_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3956_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3956_, 0, v___x_3945_);
                    leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_3956_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_tid_3932_,
                    );
                    v___x_3947_ = v_reuseFailAlloc_3956_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3931_ == 0 {
                    leanh::lean_ctor_set(v___x_3930_, 4, v___x_3947_);
                    v___x_3949_ = v___x_3930_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3955_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3955_, 0, v_env_3921_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3955_, 1, v_nextMacroScope_3922_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3955_, 2, v_ngen_3923_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3955_, 3, v_auxDeclNGen_3924_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3955_, 4, v___x_3947_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3955_, 5, v_cache_3925_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3955_, 6, v_messages_3926_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3955_, 7, v_infoState_3927_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3955_, 8, v_snapshotTasks_3928_);
                    v___x_3949_ = v_reuseFailAlloc_3955_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3950_ = lean_st_ref_set(v___y_3911_, v___x_3949_);
                v___x_3951_ = leanh::lean_box(0);
                if v_isShared_3918_ == 0 {
                    leanh::lean_ctor_set(v___x_3917_, 0, v___x_3951_);
                    v___x_3953_ = v___x_3917_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3954_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3954_, 0, v___x_3951_);
                    v___x_3953_ = v_reuseFailAlloc_3954_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3953_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg___boxed(
    mut v_cls_3960_: *mut leanh::LeanObject,
    mut v_msg_3961_: *mut leanh::LeanObject,
    mut v___y_3962_: *mut leanh::LeanObject,
    mut v___y_3963_: *mut leanh::LeanObject,
    mut v___y_3964_: *mut leanh::LeanObject,
    mut v___y_3965_: *mut leanh::LeanObject,
    mut v___y_3966_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3967_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3967_ = l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg(v_cls_3960_, v_msg_3961_, v___y_3962_, v___y_3963_, v___y_3964_, v___y_3965_);
    leanh::lean_dec(v___y_3965_);
    leanh::lean_dec_ref(v___y_3964_);
    leanh::lean_dec(v___y_3963_);
    leanh::lean_dec_ref(v___y_3962_);
    return v_res_3967_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__18___redArg(
    mut v_msg_3968_: *mut leanh::LeanObject,
    mut v___y_3969_: *mut leanh::LeanObject,
    mut v___y_3970_: *mut leanh::LeanObject,
    mut v___y_3971_: *mut leanh::LeanObject,
    mut v___y_3972_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_3974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3979_: u8 = 0;
    let mut v___x_3980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3984_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3974_ = leanh::lean_ctor_get(v___y_3971_, 5);
                v___x_3975_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3_spec__4(v_msg_3968_, v___y_3969_, v___y_3970_, v___y_3971_, v___y_3972_);
                v_a_3976_ = leanh::lean_ctor_get(v___x_3975_, 0);
                v_isSharedCheck_3984_ = (!leanh::lean_is_exclusive(v___x_3975_)) as u8;
                if v_isSharedCheck_3984_ == 0 {
                    v___x_3978_ = v___x_3975_;
                    v_isShared_3979_ = v_isSharedCheck_3984_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_3976_);
                    leanh::lean_dec(v___x_3975_);
                    v___x_3978_ = leanh::lean_box(0);
                    v_isShared_3979_ = v_isSharedCheck_3984_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_3974_);
                v___x_3980_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3980_, 0, v_ref_3974_);
                leanh::lean_ctor_set(v___x_3980_, 1, v_a_3976_);
                if v_isShared_3979_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3978_, 1);
                    leanh::lean_ctor_set(v___x_3978_, 0, v___x_3980_);
                    v___x_3982_ = v___x_3978_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3983_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3983_, 0, v___x_3980_);
                    v___x_3982_ = v_reuseFailAlloc_3983_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3982_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__18___redArg___boxed(
    mut v_msg_3985_: *mut leanh::LeanObject,
    mut v___y_3986_: *mut leanh::LeanObject,
    mut v___y_3987_: *mut leanh::LeanObject,
    mut v___y_3988_: *mut leanh::LeanObject,
    mut v___y_3989_: *mut leanh::LeanObject,
    mut v___y_3990_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3991_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3991_ = l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__18___redArg(v_msg_3985_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_);
    leanh::lean_dec(v___y_3989_);
    leanh::lean_dec_ref(v___y_3988_);
    leanh::lean_dec(v___y_3987_);
    leanh::lean_dec_ref(v___y_3986_);
    return v_res_3991_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__20_spec__25(
    mut v_a_3992_: *mut leanh::LeanObject,
    mut v_as_3993_: *mut leanh::LeanObject,
    mut v_i_3994_: usize,
    mut v_stop_3995_: usize,
) -> u8 {
    let mut v___x_3996_: u8 = 0;
    let mut v___x_3997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: u8 = 0;
    let mut v___x_3999_: usize = 0;
    let mut v___x_4000_: usize = 0;
    let mut v___x_4002_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3996_ = lean_usize_dec_eq(v_i_3994_, v_stop_3995_);
                if v___x_3996_ == 0 {
                    v___x_3997_ = lean_array_uget_borrowed(v_as_3993_, v_i_3994_);
                    v___x_3998_ = lean_nat_dec_eq(v_a_3992_, v___x_3997_);
                    if v___x_3998_ == 0 {
                        v___x_3999_ = 1usize;
                        v___x_4000_ = lean_usize_add(v_i_3994_, v___x_3999_);
                        v_i_3994_ = v___x_4000_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3998_;
                    }
                } else {
                    v___x_4002_ = 0;
                    return v___x_4002_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__20_spec__25___boxed(
    mut v_a_4003_: *mut leanh::LeanObject,
    mut v_as_4004_: *mut leanh::LeanObject,
    mut v_i_4005_: *mut leanh::LeanObject,
    mut v_stop_4006_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_4007_: usize = 0;
    let mut v_stop_boxed_4008_: usize = 0;
    let mut v_res_4009_: u8 = 0;
    let mut v_r_4010_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4007_ = leanh::lean_unbox_usize(v_i_4005_);
    leanh::lean_dec(v_i_4005_);
    v_stop_boxed_4008_ = leanh::lean_unbox_usize(v_stop_4006_);
    leanh::lean_dec(v_stop_4006_);
    v_res_4009_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__20_spec__25(v_a_4003_, v_as_4004_, v_i_boxed_4007_, v_stop_boxed_4008_);
    leanh::lean_dec_ref(v_as_4004_);
    leanh::lean_dec(v_a_4003_);
    v_r_4010_ = leanh::lean_box((v_res_4009_) as usize);
    return v_r_4010_;
}
pub unsafe fn l_Array_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__20(
    mut v_as_4011_: *mut leanh::LeanObject,
    mut v_a_4012_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: u8 = 0;
    v___x_4013_ = leanh::lean_unsigned_to_nat(0);
    v___x_4014_ = lean_array_get_size(v_as_4011_);
    v___x_4015_ = lean_nat_dec_lt(v___x_4013_, v___x_4014_);
    if v___x_4015_ == 0 {
        return v___x_4015_;
    } else {
        if v___x_4015_ == 0 {
            return v___x_4015_;
        } else {
            let mut v___x_4016_: usize = 0;
            let mut v___x_4017_: usize = 0;
            let mut v___x_4018_: u8 = 0;
            v___x_4016_ = 0usize;
            v___x_4017_ = lean_usize_of_nat(v___x_4014_);
            v___x_4018_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__20_spec__25(v_a_4012_, v_as_4011_, v___x_4016_, v___x_4017_);
            return v___x_4018_;
        }
    }
}
pub unsafe fn l_Array_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__20___boxed(
    mut v_as_4019_: *mut leanh::LeanObject,
    mut v_a_4020_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4021_: u8 = 0;
    let mut v_r_4022_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4021_ = l_Array_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__20(v_as_4019_, v_a_4020_);
    leanh::lean_dec(v_a_4020_);
    leanh::lean_dec_ref(v_as_4019_);
    v_r_4022_ = leanh::lean_box((v_res_4021_) as usize);
    return v_r_4022_;
}
pub unsafe fn _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4025_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4024_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg___closed__0;
    v___x_4025_ = l_Lean_stringToMessageData(v___x_4024_);
    return v___x_4025_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg(
    mut v___x_4026_: *mut leanh::LeanObject,
    mut v_fst_4027_: *mut leanh::LeanObject,
    mut v_range_4028_: *mut leanh::LeanObject,
    mut v_b_4029_: *mut leanh::LeanObject,
    mut v_i_4030_: *mut leanh::LeanObject,
    mut v___y_4031_: *mut leanh::LeanObject,
    mut v___y_4032_: *mut leanh::LeanObject,
    mut v___y_4033_: *mut leanh::LeanObject,
    mut v___y_4034_: *mut leanh::LeanObject,
    mut v___y_4035_: *mut leanh::LeanObject,
    mut v___y_4036_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_stop_4038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_step_4039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4040_: u8 = 0;
    let mut v___x_4041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4046_: u8 = 0;
    let mut v___x_4047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4050_: u8 = 0;
    let mut v___x_4051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stop_4038_ = leanh::lean_ctor_get(v_range_4028_, 1);
                v_step_4039_ = leanh::lean_ctor_get(v_range_4028_, 2);
                v___x_4040_ = lean_nat_dec_lt(v_i_4030_, v_stop_4038_);
                if v___x_4040_ == 0 {
                    leanh::lean_dec(v_i_4030_);
                    v___x_4041_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4041_, 0, v_b_4029_);
                    return v___x_4041_;
                } else {
                    v___x_4042_ = leanh::lean_box(0);
                    v___x_4046_ = l_Array_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__20(v___x_4026_, v_i_4030_);
                    if v___x_4046_ == 0 {
                        v___x_4047_ = lean_array_fget_borrowed(v_fst_4027_, v_i_4030_);
                        leanh::lean_inc(v___x_4047_);
                        v___x_4048_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__9___redArg(v___x_4047_, v___y_4034_);
                        v_a_4049_ = leanh::lean_ctor_get(v___x_4048_, 0);
                        leanh::lean_inc(v_a_4049_);
                        leanh::lean_dec_ref(v___x_4048_);
                        v___x_4050_ = l_Lean_Expr_hasMVar(v_a_4049_);
                        leanh::lean_dec(v_a_4049_);
                        if v___x_4050_ == 0 {
                            state = 1;
                            continue;
                        } else {
                            if v___x_4046_ == 0 {
                                leanh::lean_dec(v_i_4030_);
                                v___x_4051_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg___closed__1_once), _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg___closed__1);
                                v___x_4052_ = l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__18___redArg(v___x_4051_, v___y_4033_, v___y_4034_, v___y_4035_, v___y_4036_);
                                return v___x_4052_;
                            } else {
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4044_ = lean_nat_add(v_i_4030_, v_step_4039_);
                leanh::lean_dec(v_i_4030_);
                v_b_4029_ = v___x_4042_;
                v_i_4030_ = v___x_4044_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg___boxed(
    mut v___x_4053_: *mut leanh::LeanObject,
    mut v_fst_4054_: *mut leanh::LeanObject,
    mut v_range_4055_: *mut leanh::LeanObject,
    mut v_b_4056_: *mut leanh::LeanObject,
    mut v_i_4057_: *mut leanh::LeanObject,
    mut v___y_4058_: *mut leanh::LeanObject,
    mut v___y_4059_: *mut leanh::LeanObject,
    mut v___y_4060_: *mut leanh::LeanObject,
    mut v___y_4061_: *mut leanh::LeanObject,
    mut v___y_4062_: *mut leanh::LeanObject,
    mut v___y_4063_: *mut leanh::LeanObject,
    mut v___y_4064_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4065_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4065_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg(v___x_4053_, v_fst_4054_, v_range_4055_, v_b_4056_, v_i_4057_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_);
    leanh::lean_dec(v___y_4063_);
    leanh::lean_dec_ref(v___y_4062_);
    leanh::lean_dec(v___y_4061_);
    leanh::lean_dec_ref(v___y_4060_);
    leanh::lean_dec(v___y_4059_);
    leanh::lean_dec_ref(v___y_4058_);
    leanh::lean_dec_ref(v_range_4055_);
    leanh::lean_dec_ref(v_fst_4054_);
    leanh::lean_dec_ref(v___x_4053_);
    return v_res_4065_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__19(
    mut v_fst_4066_: *mut leanh::LeanObject,
    mut v_className_4067_: *mut leanh::LeanObject,
    mut v_as_4068_: *mut leanh::LeanObject,
    mut v_sz_4069_: usize,
    mut v_i_4070_: usize,
    mut v_b_4071_: *mut leanh::LeanObject,
    mut v___y_4072_: *mut leanh::LeanObject,
    mut v___y_4073_: *mut leanh::LeanObject,
    mut v___y_4074_: *mut leanh::LeanObject,
    mut v___y_4075_: *mut leanh::LeanObject,
    mut v___y_4076_: *mut leanh::LeanObject,
    mut v___y_4077_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_4080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4081_: usize = 0;
    let mut v___x_4082_: usize = 0;
    let mut v___x_4084_: u8 = 0;
    let mut v___x_4085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4096_: u8 = 0;
    let mut v___x_4097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: u8 = 0;
    let mut v___x_4102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4107_: u8 = 0;
    let mut v___x_4109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4111_: u8 = 0;
    let mut v_a_4112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4115_: u8 = 0;
    let mut v___x_4117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4119_: u8 = 0;
    let mut v___x_4120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4125_: u8 = 0;
    let mut v___x_4127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4129_: u8 = 0;
    let mut v_a_4130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4133_: u8 = 0;
    let mut v___x_4135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4137_: u8 = 0;
    let mut v_a_4138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4141_: u8 = 0;
    let mut v___x_4143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4145_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4084_ = lean_usize_dec_lt(v_i_4070_, v_sz_4069_);
                if v___x_4084_ == 0 {
                    v___x_4085_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4085_, 0, v_b_4071_);
                    return v___x_4085_;
                } else {
                    v___x_4086_ = l_Lean_instInhabitedExpr;
                    v_a_4087_ = lean_array_uget_borrowed(v_as_4068_, v_i_4070_);
                    v___x_4088_ = lean_array_get_borrowed(v___x_4086_, v_fst_4066_, v_a_4087_);
                    leanh::lean_inc(v___y_4077_);
                    leanh::lean_inc_ref(v___y_4076_);
                    leanh::lean_inc(v___y_4075_);
                    leanh::lean_inc_ref(v___y_4074_);
                    leanh::lean_inc(v___x_4088_);
                    v___x_4089_ = lean_infer_type(
                        v___x_4088_,
                        v___y_4074_,
                        v___y_4075_,
                        v___y_4076_,
                        v___y_4077_,
                    );
                    if leanh::lean_obj_tag(v___x_4089_) == 0 {
                        v_a_4090_ = leanh::lean_ctor_get(v___x_4089_, 0);
                        leanh::lean_inc(v_a_4090_);
                        leanh::lean_dec_ref_known(v___x_4089_, 1);
                        leanh::lean_inc(v___y_4077_);
                        leanh::lean_inc_ref(v___y_4076_);
                        leanh::lean_inc(v___y_4075_);
                        leanh::lean_inc_ref(v___y_4074_);
                        v___x_4091_ = lean_whnf(
                            v_a_4090_,
                            v___y_4074_,
                            v___y_4075_,
                            v___y_4076_,
                            v___y_4077_,
                        );
                        if leanh::lean_obj_tag(v___x_4091_) == 0 {
                            v_a_4092_ = leanh::lean_ctor_get(v___x_4091_, 0);
                            leanh::lean_inc(v_a_4092_);
                            leanh::lean_dec_ref_known(v___x_4091_, 1);
                            v___x_4093_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__9___redArg(v_a_4092_, v___y_4075_);
                            if leanh::lean_obj_tag(v___x_4093_) == 0 {
                                v_a_4094_ = leanh::lean_ctor_get(v___x_4093_, 0);
                                leanh::lean_inc(v_a_4094_);
                                leanh::lean_dec_ref_known(v___x_4093_, 1);
                                v___x_4095_ = leanh::lean_unsigned_to_nat(1);
                                v___x_4096_ = l_Lean_Expr_isAppOfArity(
                                    v_a_4094_,
                                    v_className_4067_,
                                    v___x_4095_,
                                );
                                if v___x_4096_ == 0 {
                                    leanh::lean_dec(v_a_4094_);
                                    v___x_4097_ = leanh::lean_box(0);
                                    v___x_4098_ = l_Lean_Expr_mvarId_x21(v___x_4088_);
                                    v___x_4099_ = l_Lean_Elab_Term_synthesizeInstMVarCore(
                                        v___x_4098_,
                                        v___x_4097_,
                                        v___x_4097_,
                                        v___y_4072_,
                                        v___y_4073_,
                                        v___y_4074_,
                                        v___y_4075_,
                                        v___y_4076_,
                                        v___y_4077_,
                                    );
                                    if leanh::lean_obj_tag(v___x_4099_) == 0 {
                                        v_a_4100_ = leanh::lean_ctor_get(v___x_4099_, 0);
                                        leanh::lean_inc(v_a_4100_);
                                        leanh::lean_dec_ref_known(v___x_4099_, 1);
                                        v___x_4101_ = (leanh::lean_unbox(v_a_4100_) as u8);
                                        leanh::lean_dec(v_a_4100_);
                                        if v___x_4101_ == 0 {
                                            v___x_4102_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg___closed__1_once), _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg___closed__1);
                                            v___x_4103_ = l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__18___redArg(v___x_4102_, v___y_4074_, v___y_4075_, v___y_4076_, v___y_4077_);
                                            if leanh::lean_obj_tag(v___x_4103_) == 0 {
                                                leanh::lean_dec_ref_known(v___x_4103_, 1);
                                                v_a_4080_ = v_b_4071_;
                                                state = 1;
                                                continue;
                                            } else {
                                                leanh::lean_dec_ref(v_b_4071_);
                                                v_a_4104_ =
                                                    leanh::lean_ctor_get(v___x_4103_, 0);
                                                v_isSharedCheck_4111_ =
                                                    (!leanh::lean_is_exclusive(v___x_4103_))
                                                        as u8;
                                                if v_isSharedCheck_4111_ == 0 {
                                                    v___x_4106_ = v___x_4103_;
                                                    v_isShared_4107_ = v_isSharedCheck_4111_;
                                                    state = 2;
                                                    continue;
                                                } else {
                                                    leanh::lean_inc(v_a_4104_);
                                                    leanh::lean_dec(v___x_4103_);
                                                    v___x_4106_ = leanh::lean_box(0);
                                                    v_isShared_4107_ = v_isSharedCheck_4111_;
                                                    state = 2;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            v_a_4080_ = v_b_4071_;
                                            state = 1;
                                            continue;
                                        }
                                    } else {
                                        leanh::lean_dec_ref(v_b_4071_);
                                        v_a_4112_ = leanh::lean_ctor_get(v___x_4099_, 0);
                                        v_isSharedCheck_4119_ =
                                            (!leanh::lean_is_exclusive(v___x_4099_)) as u8;
                                        if v_isSharedCheck_4119_ == 0 {
                                            v___x_4114_ = v___x_4099_;
                                            v_isShared_4115_ = v_isSharedCheck_4119_;
                                            state = 4;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_4112_);
                                            leanh::lean_dec(v___x_4099_);
                                            v___x_4114_ = leanh::lean_box(0);
                                            v_isShared_4115_ = v_isSharedCheck_4119_;
                                            state = 4;
                                            continue;
                                        }
                                    }
                                } else {
                                    v___x_4120_ = l_Lean_Expr_appArg_x21(v_a_4094_);
                                    leanh::lean_dec(v_a_4094_);
                                    v___x_4121_ = lean_array_push(v_b_4071_, v___x_4120_);
                                    v_a_4080_ = v___x_4121_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec_ref(v_b_4071_);
                                v_a_4122_ = leanh::lean_ctor_get(v___x_4093_, 0);
                                v_isSharedCheck_4129_ =
                                    (!leanh::lean_is_exclusive(v___x_4093_)) as u8;
                                if v_isSharedCheck_4129_ == 0 {
                                    v___x_4124_ = v___x_4093_;
                                    v_isShared_4125_ = v_isSharedCheck_4129_;
                                    state = 6;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_4122_);
                                    leanh::lean_dec(v___x_4093_);
                                    v___x_4124_ = leanh::lean_box(0);
                                    v_isShared_4125_ = v_isSharedCheck_4129_;
                                    state = 6;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v_b_4071_);
                            v_a_4130_ = leanh::lean_ctor_get(v___x_4091_, 0);
                            v_isSharedCheck_4137_ =
                                (!leanh::lean_is_exclusive(v___x_4091_)) as u8;
                            if v_isSharedCheck_4137_ == 0 {
                                v___x_4132_ = v___x_4091_;
                                v_isShared_4133_ = v_isSharedCheck_4137_;
                                state = 8;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4130_);
                                leanh::lean_dec(v___x_4091_);
                                v___x_4132_ = leanh::lean_box(0);
                                v_isShared_4133_ = v_isSharedCheck_4137_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_b_4071_);
                        v_a_4138_ = leanh::lean_ctor_get(v___x_4089_, 0);
                        v_isSharedCheck_4145_ =
                            (!leanh::lean_is_exclusive(v___x_4089_)) as u8;
                        if v_isSharedCheck_4145_ == 0 {
                            v___x_4140_ = v___x_4089_;
                            v_isShared_4141_ = v_isSharedCheck_4145_;
                            state = 10;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4138_);
                            leanh::lean_dec(v___x_4089_);
                            v___x_4140_ = leanh::lean_box(0);
                            v_isShared_4141_ = v_isSharedCheck_4145_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4081_ = 1usize;
                v___x_4082_ = lean_usize_add(v_i_4070_, v___x_4081_);
                v_i_4070_ = v___x_4082_;
                v_b_4071_ = v_a_4080_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_4107_ == 0 {
                    v___x_4109_ = v___x_4106_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4110_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4110_, 0, v_a_4104_);
                    v___x_4109_ = v_reuseFailAlloc_4110_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4109_;
            }
            4 => {
                if v_isShared_4115_ == 0 {
                    v___x_4117_ = v___x_4114_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4118_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4118_, 0, v_a_4112_);
                    v___x_4117_ = v_reuseFailAlloc_4118_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4117_;
            }
            6 => {
                if v_isShared_4125_ == 0 {
                    v___x_4127_ = v___x_4124_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4128_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4128_, 0, v_a_4122_);
                    v___x_4127_ = v_reuseFailAlloc_4128_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4127_;
            }
            8 => {
                if v_isShared_4133_ == 0 {
                    v___x_4135_ = v___x_4132_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4136_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4136_, 0, v_a_4130_);
                    v___x_4135_ = v_reuseFailAlloc_4136_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4135_;
            }
            10 => {
                if v_isShared_4141_ == 0 {
                    v___x_4143_ = v___x_4140_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4144_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4144_, 0, v_a_4138_);
                    v___x_4143_ = v_reuseFailAlloc_4144_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4143_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__19___boxed(
    mut v_fst_4146_: *mut leanh::LeanObject,
    mut v_className_4147_: *mut leanh::LeanObject,
    mut v_as_4148_: *mut leanh::LeanObject,
    mut v_sz_4149_: *mut leanh::LeanObject,
    mut v_i_4150_: *mut leanh::LeanObject,
    mut v_b_4151_: *mut leanh::LeanObject,
    mut v___y_4152_: *mut leanh::LeanObject,
    mut v___y_4153_: *mut leanh::LeanObject,
    mut v___y_4154_: *mut leanh::LeanObject,
    mut v___y_4155_: *mut leanh::LeanObject,
    mut v___y_4156_: *mut leanh::LeanObject,
    mut v___y_4157_: *mut leanh::LeanObject,
    mut v___y_4158_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4159_: usize = 0;
    let mut v_i_boxed_4160_: usize = 0;
    let mut v_res_4161_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4159_ = leanh::lean_unbox_usize(v_sz_4149_);
    leanh::lean_dec(v_sz_4149_);
    v_i_boxed_4160_ = leanh::lean_unbox_usize(v_i_4150_);
    leanh::lean_dec(v_i_4150_);
    v_res_4161_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__19(v_fst_4146_, v_className_4147_, v_as_4148_, v_sz_boxed_4159_, v_i_boxed_4160_, v_b_4151_, v___y_4152_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_, v___y_4157_);
    leanh::lean_dec(v___y_4157_);
    leanh::lean_dec_ref(v___y_4156_);
    leanh::lean_dec(v___y_4155_);
    leanh::lean_dec_ref(v___y_4154_);
    leanh::lean_dec(v___y_4153_);
    leanh::lean_dec_ref(v___y_4152_);
    leanh::lean_dec_ref(v_as_4148_);
    leanh::lean_dec(v_className_4147_);
    leanh::lean_dec_ref(v_fst_4146_);
    return v_res_4161_;
}
pub unsafe fn _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4164_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4163_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__0;
    v___x_4164_ = l_Lean_stringToMessageData(v___x_4163_);
    return v___x_4164_;
}
pub unsafe fn _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_4168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4169_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4168_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__3;
    v___x_4169_ = l_Lean_stringToMessageData(v___x_4168_);
    return v___x_4169_;
}
pub unsafe fn l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes(
    mut v_className_4170_: *mut leanh::LeanObject,
    mut v_extraDeps_4171_: *mut leanh::LeanObject,
    mut v_plan_4172_: *mut leanh::LeanObject,
    mut v_processing_4173_: *mut leanh::LeanObject,
    mut v_depTypes_4174_: *mut leanh::LeanObject,
    mut v_a_4175_: *mut leanh::LeanObject,
    mut v_a_4176_: *mut leanh::LeanObject,
    mut v_a_4177_: *mut leanh::LeanObject,
    mut v_a_4178_: *mut leanh::LeanObject,
    mut v_a_4179_: *mut leanh::LeanObject,
    mut v_a_4180_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_4182_: usize = 0;
    let mut v___x_4183_: usize = 0;
    let mut v___y_4185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4192_: usize = 0;
    let mut v___x_4193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4203_: usize = 0;
    let mut v___x_4204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4208_: u8 = 0;
    let mut v_val_4209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4219_: u8 = 0;
    let mut v___x_4221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4223_: u8 = 0;
    let mut v_reuseFailAlloc_4224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4225_: u8 = 0;
    let mut v_unused_4226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: u8 = 0;
    let mut v___x_4240_: u8 = 0;
    let mut v___x_4241_: usize = 0;
    let mut v___x_4242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4243_: usize = 0;
    let mut v___x_4244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4246_: usize = 0;
    let mut v___x_4247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4251_: u8 = 0;
    let mut v_val_4252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4262_: u8 = 0;
    let mut v___x_4264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4266_: u8 = 0;
    let mut v_reuseFailAlloc_4267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4268_: u8 = 0;
    let mut v_unused_4269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_sz_4182_ = lean_array_size(v_depTypes_4174_);
                v___x_4183_ = 0usize;
                v___x_4227_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__10(v_sz_4182_, v___x_4183_, v_depTypes_4174_, v_a_4175_, v_a_4176_, v_a_4177_, v_a_4178_, v_a_4179_, v_a_4180_);
                if leanh::lean_obj_tag(v___x_4227_) == 0 {
                    v_a_4228_ = leanh::lean_ctor_get(v___x_4227_, 0);
                    leanh::lean_inc(v_a_4228_);
                    leanh::lean_dec_ref_known(v___x_4227_, 1);
                    v___x_4245_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__16___closed__0;
                    v_sz_4246_ = lean_array_size(v_a_4228_);
                    v___x_4247_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__16(v_a_4228_, v_sz_4246_, v___x_4183_, v___x_4245_);
                    v_fst_4248_ = leanh::lean_ctor_get(v___x_4247_, 0);
                    v_isSharedCheck_4268_ = (!leanh::lean_is_exclusive(v___x_4247_)) as u8;
                    if v_isSharedCheck_4268_ == 0 {
                        v_unused_4269_ = leanh::lean_ctor_get(v___x_4247_, 1);
                        leanh::lean_dec(v_unused_4269_);
                        v___x_4250_ = v___x_4247_;
                        v_isShared_4251_ = v_isSharedCheck_4268_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_fst_4248_);
                        leanh::lean_dec(v___x_4247_);
                        v___x_4250_ = leanh::lean_box(0);
                        v_isShared_4251_ = v_isSharedCheck_4268_;
                        state = 8;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_processing_4173_);
                    leanh::lean_dec_ref(v_plan_4172_);
                    leanh::lean_dec_ref(v_extraDeps_4171_);
                    leanh::lean_dec(v_className_4170_);
                    return v___x_4227_;
                }
            }
            1 => {
                v_sz_4192_ = lean_array_size(v___y_4185_);
                v___x_4193_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__11(v_processing_4173_, v_className_4170_, v_extraDeps_4171_, v___y_4185_, v_sz_4192_, v___x_4183_, v_plan_4172_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_, v___y_4190_, v___y_4191_);
                leanh::lean_dec_ref(v___y_4185_);
                return v___x_4193_;
            }
            2 => {
                v___x_4202_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__16___closed__0;
                v_sz_4203_ = lean_array_size(v___y_4201_);
                v___x_4204_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__13(v_processing_4173_, v___y_4201_, v_sz_4203_, v___x_4183_, v___x_4202_);
                v_fst_4205_ = leanh::lean_ctor_get(v___x_4204_, 0);
                v_isSharedCheck_4225_ = (!leanh::lean_is_exclusive(v___x_4204_)) as u8;
                if v_isSharedCheck_4225_ == 0 {
                    v_unused_4226_ = leanh::lean_ctor_get(v___x_4204_, 1);
                    leanh::lean_dec(v_unused_4226_);
                    v___x_4207_ = v___x_4204_;
                    v_isShared_4208_ = v_isSharedCheck_4225_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_fst_4205_);
                    leanh::lean_dec(v___x_4204_);
                    v___x_4207_ = leanh::lean_box(0);
                    v_isShared_4208_ = v_isSharedCheck_4225_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if leanh::lean_obj_tag(v_fst_4205_) == 0 {
                    leanh::lean_del_object(v___x_4207_);
                    v___y_4185_ = v___y_4201_;
                    v___y_4186_ = v___y_4199_;
                    v___y_4187_ = v___y_4196_;
                    v___y_4188_ = v___y_4195_;
                    v___y_4189_ = v___y_4198_;
                    v___y_4190_ = v___y_4197_;
                    v___y_4191_ = v___y_4200_;
                    state = 1;
                    continue;
                } else {
                    v_val_4209_ = leanh::lean_ctor_get(v_fst_4205_, 0);
                    leanh::lean_inc(v_val_4209_);
                    leanh::lean_dec_ref_known(v_fst_4205_, 1);
                    if leanh::lean_obj_tag(v_val_4209_) == 1 {
                        v_val_4210_ = leanh::lean_ctor_get(v_val_4209_, 0);
                        leanh::lean_inc(v_val_4210_);
                        leanh::lean_dec_ref_known(v_val_4209_, 1);
                        v___x_4211_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__1_once), _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__1);
                        v___x_4212_ = l_Lean_MessageData_ofExpr(v_val_4210_);
                        if v_isShared_4208_ == 0 {
                            leanh::lean_ctor_set_tag(v___x_4207_, 7);
                            leanh::lean_ctor_set(v___x_4207_, 1, v___x_4212_);
                            leanh::lean_ctor_set(v___x_4207_, 0, v___x_4211_);
                            v___x_4214_ = v___x_4207_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_4224_ =
                                leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4224_, 0, v___x_4211_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4224_, 1, v___x_4212_);
                            v___x_4214_ = v_reuseFailAlloc_4224_;
                            state = 4;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_val_4209_);
                        leanh::lean_del_object(v___x_4207_);
                        v___y_4185_ = v___y_4201_;
                        v___y_4186_ = v___y_4199_;
                        v___y_4187_ = v___y_4196_;
                        v___y_4188_ = v___y_4195_;
                        v___y_4189_ = v___y_4198_;
                        v___y_4190_ = v___y_4197_;
                        v___y_4191_ = v___y_4200_;
                        state = 1;
                        continue;
                    }
                }
            }
            4 => {
                v___x_4215_ = l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14___redArg(v___x_4214_, v___y_4199_, v___y_4196_, v___y_4195_, v___y_4198_, v___y_4197_, v___y_4200_);
                if leanh::lean_obj_tag(v___x_4215_) == 0 {
                    leanh::lean_dec_ref_known(v___x_4215_, 1);
                    v___y_4185_ = v___y_4201_;
                    v___y_4186_ = v___y_4199_;
                    v___y_4187_ = v___y_4196_;
                    v___y_4188_ = v___y_4195_;
                    v___y_4189_ = v___y_4198_;
                    v___y_4190_ = v___y_4197_;
                    v___y_4191_ = v___y_4200_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec_ref(v___y_4201_);
                    leanh::lean_dec_ref(v_processing_4173_);
                    leanh::lean_dec_ref(v_plan_4172_);
                    leanh::lean_dec_ref(v_extraDeps_4171_);
                    leanh::lean_dec(v_className_4170_);
                    v_a_4216_ = leanh::lean_ctor_get(v___x_4215_, 0);
                    v_isSharedCheck_4223_ = (!leanh::lean_is_exclusive(v___x_4215_)) as u8;
                    if v_isSharedCheck_4223_ == 0 {
                        v___x_4218_ = v___x_4215_;
                        v_isShared_4219_ = v_isSharedCheck_4223_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4216_);
                        leanh::lean_dec(v___x_4215_);
                        v___x_4218_ = leanh::lean_box(0);
                        v_isShared_4219_ = v_isSharedCheck_4223_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_4219_ == 0 {
                    v___x_4221_ = v___x_4218_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4222_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4222_, 0, v_a_4216_);
                    v___x_4221_ = v_reuseFailAlloc_4222_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4221_;
            }
            7 => {
                v___x_4236_ = leanh::lean_unsigned_to_nat(0);
                v___x_4237_ = lean_array_get_size(v_a_4228_);
                v___x_4238_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__2;
                v___x_4239_ = lean_nat_dec_lt(v___x_4236_, v___x_4237_);
                if v___x_4239_ == 0 {
                    leanh::lean_dec(v_a_4228_);
                    v___y_4195_ = v___y_4232_;
                    v___y_4196_ = v___y_4231_;
                    v___y_4197_ = v___y_4234_;
                    v___y_4198_ = v___y_4233_;
                    v___y_4199_ = v___y_4230_;
                    v___y_4200_ = v___y_4235_;
                    v___y_4201_ = v___x_4238_;
                    state = 2;
                    continue;
                } else {
                    v___x_4240_ = lean_nat_dec_le(v___x_4237_, v___x_4237_);
                    if v___x_4240_ == 0 {
                        if v___x_4239_ == 0 {
                            leanh::lean_dec(v_a_4228_);
                            v___y_4195_ = v___y_4232_;
                            v___y_4196_ = v___y_4231_;
                            v___y_4197_ = v___y_4234_;
                            v___y_4198_ = v___y_4233_;
                            v___y_4199_ = v___y_4230_;
                            v___y_4200_ = v___y_4235_;
                            v___y_4201_ = v___x_4238_;
                            state = 2;
                            continue;
                        } else {
                            v___x_4241_ = lean_usize_of_nat(v___x_4237_);
                            v___x_4242_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__15(v_plan_4172_, v_a_4228_, v___x_4183_, v___x_4241_, v___x_4238_);
                            leanh::lean_dec(v_a_4228_);
                            v___y_4195_ = v___y_4232_;
                            v___y_4196_ = v___y_4231_;
                            v___y_4197_ = v___y_4234_;
                            v___y_4198_ = v___y_4233_;
                            v___y_4199_ = v___y_4230_;
                            v___y_4200_ = v___y_4235_;
                            v___y_4201_ = v___x_4242_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___x_4243_ = lean_usize_of_nat(v___x_4237_);
                        v___x_4244_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__15(v_plan_4172_, v_a_4228_, v___x_4183_, v___x_4243_, v___x_4238_);
                        leanh::lean_dec(v_a_4228_);
                        v___y_4195_ = v___y_4232_;
                        v___y_4196_ = v___y_4231_;
                        v___y_4197_ = v___y_4234_;
                        v___y_4198_ = v___y_4233_;
                        v___y_4199_ = v___y_4230_;
                        v___y_4200_ = v___y_4235_;
                        v___y_4201_ = v___x_4244_;
                        state = 2;
                        continue;
                    }
                }
            }
            8 => {
                if leanh::lean_obj_tag(v_fst_4248_) == 0 {
                    leanh::lean_del_object(v___x_4250_);
                    v___y_4230_ = v_a_4175_;
                    v___y_4231_ = v_a_4176_;
                    v___y_4232_ = v_a_4177_;
                    v___y_4233_ = v_a_4178_;
                    v___y_4234_ = v_a_4179_;
                    v___y_4235_ = v_a_4180_;
                    state = 7;
                    continue;
                } else {
                    v_val_4252_ = leanh::lean_ctor_get(v_fst_4248_, 0);
                    leanh::lean_inc(v_val_4252_);
                    leanh::lean_dec_ref_known(v_fst_4248_, 1);
                    if leanh::lean_obj_tag(v_val_4252_) == 1 {
                        v_val_4253_ = leanh::lean_ctor_get(v_val_4252_, 0);
                        leanh::lean_inc(v_val_4253_);
                        leanh::lean_dec_ref_known(v_val_4252_, 1);
                        v___x_4254_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__4_once), _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__4);
                        v___x_4255_ = l_Lean_MessageData_ofExpr(v_val_4253_);
                        if v_isShared_4251_ == 0 {
                            leanh::lean_ctor_set_tag(v___x_4250_, 7);
                            leanh::lean_ctor_set(v___x_4250_, 1, v___x_4255_);
                            leanh::lean_ctor_set(v___x_4250_, 0, v___x_4254_);
                            v___x_4257_ = v___x_4250_;
                            state = 9;
                            continue;
                        } else {
                            v_reuseFailAlloc_4267_ =
                                leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4267_, 0, v___x_4254_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4267_, 1, v___x_4255_);
                            v___x_4257_ = v_reuseFailAlloc_4267_;
                            state = 9;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_val_4252_);
                        leanh::lean_del_object(v___x_4250_);
                        v___y_4230_ = v_a_4175_;
                        v___y_4231_ = v_a_4176_;
                        v___y_4232_ = v_a_4177_;
                        v___y_4233_ = v_a_4178_;
                        v___y_4234_ = v_a_4179_;
                        v___y_4235_ = v_a_4180_;
                        state = 7;
                        continue;
                    }
                }
            }
            9 => {
                v___x_4258_ = l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14___redArg(v___x_4257_, v_a_4175_, v_a_4176_, v_a_4177_, v_a_4178_, v_a_4179_, v_a_4180_);
                if leanh::lean_obj_tag(v___x_4258_) == 0 {
                    leanh::lean_dec_ref_known(v___x_4258_, 1);
                    v___y_4230_ = v_a_4175_;
                    v___y_4231_ = v_a_4176_;
                    v___y_4232_ = v_a_4177_;
                    v___y_4233_ = v_a_4178_;
                    v___y_4234_ = v_a_4179_;
                    v___y_4235_ = v_a_4180_;
                    state = 7;
                    continue;
                } else {
                    leanh::lean_dec(v_a_4228_);
                    leanh::lean_dec_ref(v_processing_4173_);
                    leanh::lean_dec_ref(v_plan_4172_);
                    leanh::lean_dec_ref(v_extraDeps_4171_);
                    leanh::lean_dec(v_className_4170_);
                    v_a_4259_ = leanh::lean_ctor_get(v___x_4258_, 0);
                    v_isSharedCheck_4266_ = (!leanh::lean_is_exclusive(v___x_4258_)) as u8;
                    if v_isSharedCheck_4266_ == 0 {
                        v___x_4261_ = v___x_4258_;
                        v_isShared_4262_ = v_isSharedCheck_4266_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4259_);
                        leanh::lean_dec(v___x_4258_);
                        v___x_4261_ = leanh::lean_box(0);
                        v_isShared_4262_ = v_isSharedCheck_4266_;
                        state = 10;
                        continue;
                    }
                }
            }
            10 => {
                if v_isShared_4262_ == 0 {
                    v___x_4264_ = v___x_4261_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4265_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4265_, 0, v_a_4259_);
                    v___x_4264_ = v_reuseFailAlloc_4265_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4264_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3()
-> *mut leanh::LeanObject {
    let mut v_cls_4278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4280_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cls_4278_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__2;
    v___x_4279_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___lam__0___closed__1;
    v___x_4280_ = l_Lean_Name_append(v___x_4279_, v_cls_4278_);
    return v___x_4280_;
}
pub unsafe fn _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_4282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4282_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__4;
    v___x_4283_ = l_Lean_stringToMessageData(v___x_4282_);
    return v___x_4283_;
}
pub unsafe fn _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_4285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4285_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__6;
    v___x_4286_ = l_Lean_stringToMessageData(v___x_4285_);
    return v___x_4286_;
}
pub unsafe fn _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_4288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4289_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4288_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__8;
    v___x_4289_ = l_Lean_stringToMessageData(v___x_4288_);
    return v___x_4289_;
}
pub unsafe fn _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_4291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4292_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4291_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__10;
    v___x_4292_ = l_Lean_stringToMessageData(v___x_4291_);
    return v___x_4292_;
}
pub unsafe fn _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_4294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4295_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4294_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__12;
    v___x_4295_ = l_Lean_stringToMessageData(v___x_4294_);
    return v___x_4295_;
}
pub unsafe fn l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst(
    mut v_className_4296_: *mut leanh::LeanObject,
    mut v_extraDeps_4297_: *mut leanh::LeanObject,
    mut v_plan_4298_: *mut leanh::LeanObject,
    mut v_processing_4299_: *mut leanh::LeanObject,
    mut v_cls_4300_: *mut leanh::LeanObject,
    mut v_inst_4301_: *mut leanh::LeanObject,
    mut v_a_4302_: *mut leanh::LeanObject,
    mut v_a_4303_: *mut leanh::LeanObject,
    mut v_a_4304_: *mut leanh::LeanObject,
    mut v_a_4305_: *mut leanh::LeanObject,
    mut v_a_4306_: *mut leanh::LeanObject,
    mut v_a_4307_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cls_4309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4321_: usize = 0;
    let mut v___x_4322_: usize = 0;
    let mut v___x_4323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_4331_: u8 = 0;
    let mut v___x_4332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_4333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: u8 = 0;
    let mut v___x_4336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4352_: u8 = 0;
    let mut v___x_4354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4356_: u8 = 0;
    let mut v_a_4357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4360_: u8 = 0;
    let mut v___x_4362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4364_: u8 = 0;
    let mut v___y_4366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4377_: u8 = 0;
    let mut v___x_4378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4383_: u8 = 0;
    let mut v___x_4385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4387_: u8 = 0;
    let mut v_a_4388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4391_: u8 = 0;
    let mut v___x_4393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4395_: u8 = 0;
    let mut v___y_4397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthOrder_4404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4407_: u8 = 0;
    let mut v___x_4408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4411_: u8 = 0;
    let mut v___x_4412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4418_: u8 = 0;
    let mut v_snd_4419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4422_: u8 = 0;
    let mut v___x_4423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4425_: u8 = 0;
    let mut v___x_4426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4443_: u8 = 0;
    let mut v___x_4445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4447_: u8 = 0;
    let mut v_reuseFailAlloc_4448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4454_: u8 = 0;
    let mut v___x_4456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4458_: u8 = 0;
    let mut v_isSharedCheck_4459_: u8 = 0;
    let mut v_unused_4460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4461_: u8 = 0;
    let mut v_a_4462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4465_: u8 = 0;
    let mut v___x_4467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4469_: u8 = 0;
    let mut v_a_4470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4473_: u8 = 0;
    let mut v___x_4475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4477_: u8 = 0;
    let mut v_isSharedCheck_4478_: u8 = 0;
    let mut v___x_4479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4481_: u8 = 0;
    let mut v___x_4482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4489_: u8 = 0;
    let mut v___x_4491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4493_: u8 = 0;
    let mut v_a_4494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4497_: u8 = 0;
    let mut v___x_4499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4501_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_cls_4309_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__2;
                v___x_4479_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___lam__0(v_cls_4309_, v_a_4302_, v_a_4303_, v_a_4304_, v_a_4305_, v_a_4306_, v_a_4307_);
                if leanh::lean_obj_tag(v___x_4479_) == 0 {
                    v_a_4480_ = leanh::lean_ctor_get(v___x_4479_, 0);
                    leanh::lean_inc(v_a_4480_);
                    leanh::lean_dec_ref_known(v___x_4479_, 1);
                    v___x_4481_ = (leanh::lean_unbox(v_a_4480_) as u8);
                    leanh::lean_dec(v_a_4480_);
                    if v___x_4481_ == 0 {
                        v___y_4397_ = v_a_4302_;
                        v___y_4398_ = v_a_4303_;
                        v___y_4399_ = v_a_4304_;
                        v___y_4400_ = v_a_4305_;
                        v___y_4401_ = v_a_4306_;
                        v___y_4402_ = v_a_4307_;
                        state = 11;
                        continue;
                    } else {
                        v___x_4482_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__13), core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__13_once), _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__13);
                        leanh::lean_inc_ref(v_cls_4300_);
                        v___x_4483_ = l_Lean_MessageData_ofExpr(v_cls_4300_);
                        v___x_4484_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_4484_, 0, v___x_4482_);
                        leanh::lean_ctor_set(v___x_4484_, 1, v___x_4483_);
                        v___x_4485_ = l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg(v_cls_4309_, v___x_4484_, v_a_4304_, v_a_4305_, v_a_4306_, v_a_4307_);
                        if leanh::lean_obj_tag(v___x_4485_) == 0 {
                            leanh::lean_dec_ref_known(v___x_4485_, 1);
                            v___y_4397_ = v_a_4302_;
                            v___y_4398_ = v_a_4303_;
                            v___y_4399_ = v_a_4304_;
                            v___y_4400_ = v_a_4305_;
                            v___y_4401_ = v_a_4306_;
                            v___y_4402_ = v_a_4307_;
                            state = 11;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v_inst_4301_);
                            leanh::lean_dec_ref(v_cls_4300_);
                            leanh::lean_dec_ref(v_processing_4299_);
                            leanh::lean_dec_ref(v_plan_4298_);
                            leanh::lean_dec_ref(v_extraDeps_4297_);
                            leanh::lean_dec(v_className_4296_);
                            v_a_4486_ = leanh::lean_ctor_get(v___x_4485_, 0);
                            v_isSharedCheck_4493_ =
                                (!leanh::lean_is_exclusive(v___x_4485_)) as u8;
                            if v_isSharedCheck_4493_ == 0 {
                                v___x_4488_ = v___x_4485_;
                                v_isShared_4489_ = v_isSharedCheck_4493_;
                                state = 26;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4486_);
                                leanh::lean_dec(v___x_4485_);
                                v___x_4488_ = leanh::lean_box(0);
                                v_isShared_4489_ = v_isSharedCheck_4493_;
                                state = 26;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_inst_4301_);
                    leanh::lean_dec_ref(v_cls_4300_);
                    leanh::lean_dec_ref(v_processing_4299_);
                    leanh::lean_dec_ref(v_plan_4298_);
                    leanh::lean_dec_ref(v_extraDeps_4297_);
                    leanh::lean_dec(v_className_4296_);
                    v_a_4494_ = leanh::lean_ctor_get(v___x_4479_, 0);
                    v_isSharedCheck_4501_ = (!leanh::lean_is_exclusive(v___x_4479_)) as u8;
                    if v_isSharedCheck_4501_ == 0 {
                        v___x_4496_ = v___x_4479_;
                        v_isShared_4497_ = v_isSharedCheck_4501_;
                        state = 28;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4494_);
                        leanh::lean_dec(v___x_4479_);
                        v___x_4496_ = leanh::lean_box(0);
                        v_isShared_4497_ = v_isSharedCheck_4501_;
                        state = 28;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4319_ = leanh::lean_unsigned_to_nat(0);
                v___x_4320_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__2;
                v_sz_4321_ = lean_array_size(v___y_4312_);
                v___x_4322_ = 0usize;
                v___x_4323_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__19(v___y_4316_, v_className_4296_, v___y_4312_, v_sz_4321_, v___x_4322_, v___x_4320_, v___y_4311_, v___y_4318_, v___y_4314_, v___y_4317_, v___y_4313_, v___y_4315_);
                if leanh::lean_obj_tag(v___x_4323_) == 0 {
                    v_a_4324_ = leanh::lean_ctor_get(v___x_4323_, 0);
                    leanh::lean_inc(v_a_4324_);
                    leanh::lean_dec_ref_known(v___x_4323_, 1);
                    v___x_4325_ = lean_array_get_size(v___y_4316_);
                    v___x_4326_ = leanh::lean_unsigned_to_nat(1);
                    v___x_4327_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_4327_, 0, v___x_4319_);
                    leanh::lean_ctor_set(v___x_4327_, 1, v___x_4325_);
                    leanh::lean_ctor_set(v___x_4327_, 2, v___x_4326_);
                    v___x_4328_ = leanh::lean_box(0);
                    v___x_4329_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg(v___y_4312_, v___y_4316_, v___x_4327_, v___x_4328_, v___x_4319_, v___y_4311_, v___y_4318_, v___y_4314_, v___y_4317_, v___y_4313_, v___y_4315_);
                    leanh::lean_dec_ref_known(v___x_4327_, 3);
                    leanh::lean_dec_ref(v___y_4316_);
                    leanh::lean_dec_ref(v___y_4312_);
                    if leanh::lean_obj_tag(v___x_4329_) == 0 {
                        leanh::lean_dec_ref_known(v___x_4329_, 1);
                        v_options_4330_ = leanh::lean_ctor_get(v___y_4313_, 2);
                        v_hasTrace_4331_ = leanh::lean_ctor_get_uint8(
                            v_options_4330_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        );
                        if v_hasTrace_4331_ == 0 {
                            leanh::lean_dec_ref(v_cls_4300_);
                            v___x_4332_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes(v_className_4296_, v_extraDeps_4297_, v_plan_4298_, v_processing_4299_, v_a_4324_, v___y_4311_, v___y_4318_, v___y_4314_, v___y_4317_, v___y_4313_, v___y_4315_);
                            return v___x_4332_;
                        } else {
                            v_inheritedTraceOptions_4333_ =
                                leanh::lean_ctor_get(v___y_4313_, 13);
                            v___x_4334_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3_once), _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3);
                            v___x_4335_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                v_inheritedTraceOptions_4333_,
                                v_options_4330_,
                                v___x_4334_,
                            );
                            if v___x_4335_ == 0 {
                                leanh::lean_dec_ref(v_cls_4300_);
                                v___x_4336_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes(v_className_4296_, v_extraDeps_4297_, v_plan_4298_, v_processing_4299_, v_a_4324_, v___y_4311_, v___y_4318_, v___y_4314_, v___y_4317_, v___y_4313_, v___y_4315_);
                                return v___x_4336_;
                            } else {
                                v___x_4337_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__5_once), _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__5);
                                v___x_4338_ = l_Lean_MessageData_ofExpr(v_cls_4300_);
                                v___x_4339_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_4339_, 0, v___x_4337_);
                                leanh::lean_ctor_set(v___x_4339_, 1, v___x_4338_);
                                v___x_4340_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__7_once), _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__7);
                                v___x_4341_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_4341_, 0, v___x_4339_);
                                leanh::lean_ctor_set(v___x_4341_, 1, v___x_4340_);
                                leanh::lean_inc(v_a_4324_);
                                v___x_4342_ = lean_array_to_list(v_a_4324_);
                                v___x_4343_ = leanh::lean_box(0);
                                v___x_4344_ = l_List_mapTR_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__2(v___x_4342_, v___x_4343_);
                                v___x_4345_ = l_Lean_MessageData_ofList(v___x_4344_);
                                v___x_4346_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_4346_, 0, v___x_4341_);
                                leanh::lean_ctor_set(v___x_4346_, 1, v___x_4345_);
                                v___x_4347_ = l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg(v_cls_4309_, v___x_4346_, v___y_4314_, v___y_4317_, v___y_4313_, v___y_4315_);
                                if leanh::lean_obj_tag(v___x_4347_) == 0 {
                                    leanh::lean_dec_ref_known(v___x_4347_, 1);
                                    v___x_4348_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes(v_className_4296_, v_extraDeps_4297_, v_plan_4298_, v_processing_4299_, v_a_4324_, v___y_4311_, v___y_4318_, v___y_4314_, v___y_4317_, v___y_4313_, v___y_4315_);
                                    return v___x_4348_;
                                } else {
                                    leanh::lean_dec(v_a_4324_);
                                    leanh::lean_dec_ref(v_processing_4299_);
                                    leanh::lean_dec_ref(v_plan_4298_);
                                    leanh::lean_dec_ref(v_extraDeps_4297_);
                                    leanh::lean_dec(v_className_4296_);
                                    v_a_4349_ = leanh::lean_ctor_get(v___x_4347_, 0);
                                    v_isSharedCheck_4356_ =
                                        (!leanh::lean_is_exclusive(v___x_4347_)) as u8;
                                    if v_isSharedCheck_4356_ == 0 {
                                        v___x_4351_ = v___x_4347_;
                                        v_isShared_4352_ = v_isSharedCheck_4356_;
                                        state = 2;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_4349_);
                                        leanh::lean_dec(v___x_4347_);
                                        v___x_4351_ = leanh::lean_box(0);
                                        v_isShared_4352_ = v_isSharedCheck_4356_;
                                        state = 2;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_4324_);
                        leanh::lean_dec_ref(v_cls_4300_);
                        leanh::lean_dec_ref(v_processing_4299_);
                        leanh::lean_dec_ref(v_plan_4298_);
                        leanh::lean_dec_ref(v_extraDeps_4297_);
                        leanh::lean_dec(v_className_4296_);
                        v_a_4357_ = leanh::lean_ctor_get(v___x_4329_, 0);
                        v_isSharedCheck_4364_ =
                            (!leanh::lean_is_exclusive(v___x_4329_)) as u8;
                        if v_isSharedCheck_4364_ == 0 {
                            v___x_4359_ = v___x_4329_;
                            v_isShared_4360_ = v_isSharedCheck_4364_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4357_);
                            leanh::lean_dec(v___x_4329_);
                            v___x_4359_ = leanh::lean_box(0);
                            v_isShared_4360_ = v_isSharedCheck_4364_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___y_4316_);
                    leanh::lean_dec_ref(v___y_4312_);
                    leanh::lean_dec_ref(v_cls_4300_);
                    leanh::lean_dec_ref(v_processing_4299_);
                    leanh::lean_dec_ref(v_plan_4298_);
                    leanh::lean_dec_ref(v_extraDeps_4297_);
                    leanh::lean_dec(v_className_4296_);
                    return v___x_4323_;
                }
            }
            2 => {
                if v_isShared_4352_ == 0 {
                    v___x_4354_ = v___x_4351_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4355_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4355_, 0, v_a_4349_);
                    v___x_4354_ = v_reuseFailAlloc_4355_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4354_;
            }
            4 => {
                if v_isShared_4360_ == 0 {
                    v___x_4362_ = v___x_4359_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4363_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4363_, 0, v_a_4357_);
                    v___x_4362_ = v_reuseFailAlloc_4363_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4362_;
            }
            6 => {
                leanh::lean_inc_ref(v_cls_4300_);
                v___x_4375_ = l_Lean_Meta_isExprDefEq(
                    v_cls_4300_,
                    v___y_4366_,
                    v___y_4371_,
                    v___y_4372_,
                    v___y_4373_,
                    v___y_4374_,
                );
                if leanh::lean_obj_tag(v___x_4375_) == 0 {
                    v_a_4376_ = leanh::lean_ctor_get(v___x_4375_, 0);
                    leanh::lean_inc(v_a_4376_);
                    leanh::lean_dec_ref_known(v___x_4375_, 1);
                    v___x_4377_ = (leanh::lean_unbox(v_a_4376_) as u8);
                    leanh::lean_dec(v_a_4376_);
                    if v___x_4377_ == 0 {
                        v___x_4378_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg___closed__1_once), _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg___closed__1);
                        v___x_4379_ = l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__18___redArg(v___x_4378_, v___y_4371_, v___y_4372_, v___y_4373_, v___y_4374_);
                        if leanh::lean_obj_tag(v___x_4379_) == 0 {
                            leanh::lean_dec_ref_known(v___x_4379_, 1);
                            v___y_4311_ = v___y_4369_;
                            v___y_4312_ = v___y_4367_;
                            v___y_4313_ = v___y_4373_;
                            v___y_4314_ = v___y_4371_;
                            v___y_4315_ = v___y_4374_;
                            v___y_4316_ = v___y_4368_;
                            v___y_4317_ = v___y_4372_;
                            v___y_4318_ = v___y_4370_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v___y_4368_);
                            leanh::lean_dec_ref(v___y_4367_);
                            leanh::lean_dec_ref(v_cls_4300_);
                            leanh::lean_dec_ref(v_processing_4299_);
                            leanh::lean_dec_ref(v_plan_4298_);
                            leanh::lean_dec_ref(v_extraDeps_4297_);
                            leanh::lean_dec(v_className_4296_);
                            v_a_4380_ = leanh::lean_ctor_get(v___x_4379_, 0);
                            v_isSharedCheck_4387_ =
                                (!leanh::lean_is_exclusive(v___x_4379_)) as u8;
                            if v_isSharedCheck_4387_ == 0 {
                                v___x_4382_ = v___x_4379_;
                                v_isShared_4383_ = v_isSharedCheck_4387_;
                                state = 7;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4380_);
                                leanh::lean_dec(v___x_4379_);
                                v___x_4382_ = leanh::lean_box(0);
                                v_isShared_4383_ = v_isSharedCheck_4387_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        v___y_4311_ = v___y_4369_;
                        v___y_4312_ = v___y_4367_;
                        v___y_4313_ = v___y_4373_;
                        v___y_4314_ = v___y_4371_;
                        v___y_4315_ = v___y_4374_;
                        v___y_4316_ = v___y_4368_;
                        v___y_4317_ = v___y_4372_;
                        v___y_4318_ = v___y_4370_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v___y_4368_);
                    leanh::lean_dec_ref(v___y_4367_);
                    leanh::lean_dec_ref(v_cls_4300_);
                    leanh::lean_dec_ref(v_processing_4299_);
                    leanh::lean_dec_ref(v_plan_4298_);
                    leanh::lean_dec_ref(v_extraDeps_4297_);
                    leanh::lean_dec(v_className_4296_);
                    v_a_4388_ = leanh::lean_ctor_get(v___x_4375_, 0);
                    v_isSharedCheck_4395_ = (!leanh::lean_is_exclusive(v___x_4375_)) as u8;
                    if v_isSharedCheck_4395_ == 0 {
                        v___x_4390_ = v___x_4375_;
                        v_isShared_4391_ = v_isSharedCheck_4395_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4388_);
                        leanh::lean_dec(v___x_4375_);
                        v___x_4390_ = leanh::lean_box(0);
                        v_isShared_4391_ = v_isSharedCheck_4395_;
                        state = 9;
                        continue;
                    }
                }
            }
            7 => {
                if v_isShared_4383_ == 0 {
                    v___x_4385_ = v___x_4382_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4386_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4386_, 0, v_a_4380_);
                    v___x_4385_ = v_reuseFailAlloc_4386_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4385_;
            }
            9 => {
                if v_isShared_4391_ == 0 {
                    v___x_4393_ = v___x_4390_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4394_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4394_, 0, v_a_4388_);
                    v___x_4393_ = v_reuseFailAlloc_4394_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4393_;
            }
            11 => {
                v_val_4403_ = leanh::lean_ctor_get(v_inst_4301_, 0);
                v_synthOrder_4404_ = leanh::lean_ctor_get(v_inst_4301_, 1);
                v_isSharedCheck_4478_ = (!leanh::lean_is_exclusive(v_inst_4301_)) as u8;
                if v_isSharedCheck_4478_ == 0 {
                    v___x_4406_ = v_inst_4301_;
                    v_isShared_4407_ = v_isSharedCheck_4478_;
                    state = 12;
                    continue;
                } else {
                    leanh::lean_inc(v_synthOrder_4404_);
                    leanh::lean_inc(v_val_4403_);
                    leanh::lean_dec(v_inst_4301_);
                    v___x_4406_ = leanh::lean_box(0);
                    v_isShared_4407_ = v_isSharedCheck_4478_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                leanh::lean_inc(v___y_4402_);
                leanh::lean_inc_ref(v___y_4401_);
                leanh::lean_inc(v___y_4400_);
                leanh::lean_inc_ref(v___y_4399_);
                v___x_4408_ = lean_infer_type(
                    v_val_4403_,
                    v___y_4399_,
                    v___y_4400_,
                    v___y_4401_,
                    v___y_4402_,
                );
                if leanh::lean_obj_tag(v___x_4408_) == 0 {
                    v_a_4409_ = leanh::lean_ctor_get(v___x_4408_, 0);
                    leanh::lean_inc(v_a_4409_);
                    leanh::lean_dec_ref_known(v___x_4408_, 1);
                    v___x_4410_ = leanh::lean_box(0);
                    v___x_4411_ = 0;
                    v___x_4412_ = l_Lean_Meta_forallMetaTelescopeReducing(
                        v_a_4409_,
                        v___x_4410_,
                        v___x_4411_,
                        v___y_4399_,
                        v___y_4400_,
                        v___y_4401_,
                        v___y_4402_,
                    );
                    if leanh::lean_obj_tag(v___x_4412_) == 0 {
                        v_a_4413_ = leanh::lean_ctor_get(v___x_4412_, 0);
                        leanh::lean_inc(v_a_4413_);
                        leanh::lean_dec_ref_known(v___x_4412_, 1);
                        v_snd_4414_ = leanh::lean_ctor_get(v_a_4413_, 1);
                        v_fst_4415_ = leanh::lean_ctor_get(v_a_4413_, 0);
                        v_isSharedCheck_4461_ = (!leanh::lean_is_exclusive(v_a_4413_)) as u8;
                        if v_isSharedCheck_4461_ == 0 {
                            v___x_4417_ = v_a_4413_;
                            v_isShared_4418_ = v_isSharedCheck_4461_;
                            state = 13;
                            continue;
                        } else {
                            leanh::lean_inc(v_snd_4414_);
                            leanh::lean_inc(v_fst_4415_);
                            leanh::lean_dec(v_a_4413_);
                            v___x_4417_ = leanh::lean_box(0);
                            v_isShared_4418_ = v_isSharedCheck_4461_;
                            state = 13;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_4406_);
                        leanh::lean_dec_ref(v_synthOrder_4404_);
                        leanh::lean_dec_ref(v_cls_4300_);
                        leanh::lean_dec_ref(v_processing_4299_);
                        leanh::lean_dec_ref(v_plan_4298_);
                        leanh::lean_dec_ref(v_extraDeps_4297_);
                        leanh::lean_dec(v_className_4296_);
                        v_a_4462_ = leanh::lean_ctor_get(v___x_4412_, 0);
                        v_isSharedCheck_4469_ =
                            (!leanh::lean_is_exclusive(v___x_4412_)) as u8;
                        if v_isSharedCheck_4469_ == 0 {
                            v___x_4464_ = v___x_4412_;
                            v_isShared_4465_ = v_isSharedCheck_4469_;
                            state = 22;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4462_);
                            leanh::lean_dec(v___x_4412_);
                            v___x_4464_ = leanh::lean_box(0);
                            v_isShared_4465_ = v_isSharedCheck_4469_;
                            state = 22;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_4406_);
                    leanh::lean_dec_ref(v_synthOrder_4404_);
                    leanh::lean_dec_ref(v_cls_4300_);
                    leanh::lean_dec_ref(v_processing_4299_);
                    leanh::lean_dec_ref(v_plan_4298_);
                    leanh::lean_dec_ref(v_extraDeps_4297_);
                    leanh::lean_dec(v_className_4296_);
                    v_a_4470_ = leanh::lean_ctor_get(v___x_4408_, 0);
                    v_isSharedCheck_4477_ = (!leanh::lean_is_exclusive(v___x_4408_)) as u8;
                    if v_isSharedCheck_4477_ == 0 {
                        v___x_4472_ = v___x_4408_;
                        v_isShared_4473_ = v_isSharedCheck_4477_;
                        state = 24;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4470_);
                        leanh::lean_dec(v___x_4408_);
                        v___x_4472_ = leanh::lean_box(0);
                        v_isShared_4473_ = v_isSharedCheck_4477_;
                        state = 24;
                        continue;
                    }
                }
            }
            13 => {
                v_snd_4419_ = leanh::lean_ctor_get(v_snd_4414_, 1);
                v_isSharedCheck_4459_ = (!leanh::lean_is_exclusive(v_snd_4414_)) as u8;
                if v_isSharedCheck_4459_ == 0 {
                    v_unused_4460_ = leanh::lean_ctor_get(v_snd_4414_, 0);
                    leanh::lean_dec(v_unused_4460_);
                    v___x_4421_ = v_snd_4414_;
                    v_isShared_4422_ = v_isSharedCheck_4459_;
                    state = 14;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_4419_);
                    leanh::lean_dec(v_snd_4414_);
                    v___x_4421_ = leanh::lean_box(0);
                    v_isShared_4422_ = v_isSharedCheck_4459_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_4423_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___lam__0(v_cls_4309_, v___y_4397_, v___y_4398_, v___y_4399_, v___y_4400_, v___y_4401_, v___y_4402_);
                if leanh::lean_obj_tag(v___x_4423_) == 0 {
                    v_a_4424_ = leanh::lean_ctor_get(v___x_4423_, 0);
                    leanh::lean_inc(v_a_4424_);
                    leanh::lean_dec_ref_known(v___x_4423_, 1);
                    v___x_4425_ = (leanh::lean_unbox(v_a_4424_) as u8);
                    leanh::lean_dec(v_a_4424_);
                    if v___x_4425_ == 0 {
                        leanh::lean_del_object(v___x_4421_);
                        leanh::lean_del_object(v___x_4417_);
                        leanh::lean_del_object(v___x_4406_);
                        v___y_4366_ = v_snd_4419_;
                        v___y_4367_ = v_synthOrder_4404_;
                        v___y_4368_ = v_fst_4415_;
                        v___y_4369_ = v___y_4397_;
                        v___y_4370_ = v___y_4398_;
                        v___y_4371_ = v___y_4399_;
                        v___y_4372_ = v___y_4400_;
                        v___y_4373_ = v___y_4401_;
                        v___y_4374_ = v___y_4402_;
                        state = 6;
                        continue;
                    } else {
                        v___x_4426_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__9_once), _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__9);
                        leanh::lean_inc(v_fst_4415_);
                        v___x_4427_ = lean_array_to_list(v_fst_4415_);
                        v___x_4428_ = leanh::lean_box(0);
                        v___x_4429_ = l_List_mapTR_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__2(v___x_4427_, v___x_4428_);
                        v___x_4430_ = l_Lean_MessageData_ofList(v___x_4429_);
                        if v_isShared_4422_ == 0 {
                            leanh::lean_ctor_set_tag(v___x_4421_, 7);
                            leanh::lean_ctor_set(v___x_4421_, 1, v___x_4430_);
                            leanh::lean_ctor_set(v___x_4421_, 0, v___x_4426_);
                            v___x_4432_ = v___x_4421_;
                            state = 15;
                            continue;
                        } else {
                            v_reuseFailAlloc_4450_ =
                                leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4450_, 0, v___x_4426_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4450_, 1, v___x_4430_);
                            v___x_4432_ = v_reuseFailAlloc_4450_;
                            state = 15;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_4421_);
                    leanh::lean_dec(v_snd_4419_);
                    leanh::lean_del_object(v___x_4417_);
                    leanh::lean_dec(v_fst_4415_);
                    leanh::lean_del_object(v___x_4406_);
                    leanh::lean_dec_ref(v_synthOrder_4404_);
                    leanh::lean_dec_ref(v_cls_4300_);
                    leanh::lean_dec_ref(v_processing_4299_);
                    leanh::lean_dec_ref(v_plan_4298_);
                    leanh::lean_dec_ref(v_extraDeps_4297_);
                    leanh::lean_dec(v_className_4296_);
                    v_a_4451_ = leanh::lean_ctor_get(v___x_4423_, 0);
                    v_isSharedCheck_4458_ = (!leanh::lean_is_exclusive(v___x_4423_)) as u8;
                    if v_isSharedCheck_4458_ == 0 {
                        v___x_4453_ = v___x_4423_;
                        v_isShared_4454_ = v_isSharedCheck_4458_;
                        state = 20;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4451_);
                        leanh::lean_dec(v___x_4423_);
                        v___x_4453_ = leanh::lean_box(0);
                        v_isShared_4454_ = v_isSharedCheck_4458_;
                        state = 20;
                        continue;
                    }
                }
            }
            15 => {
                v___x_4433_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__11_once), _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__11);
                if v_isShared_4418_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4417_, 7);
                    leanh::lean_ctor_set(v___x_4417_, 1, v___x_4433_);
                    leanh::lean_ctor_set(v___x_4417_, 0, v___x_4432_);
                    v___x_4435_ = v___x_4417_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4449_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4449_, 0, v___x_4432_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4449_, 1, v___x_4433_);
                    v___x_4435_ = v_reuseFailAlloc_4449_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                leanh::lean_inc(v_snd_4419_);
                v___x_4436_ = l_Lean_MessageData_ofExpr(v_snd_4419_);
                if v_isShared_4407_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4406_, 7);
                    leanh::lean_ctor_set(v___x_4406_, 1, v___x_4436_);
                    leanh::lean_ctor_set(v___x_4406_, 0, v___x_4435_);
                    v___x_4438_ = v___x_4406_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_4448_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4448_, 0, v___x_4435_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4448_, 1, v___x_4436_);
                    v___x_4438_ = v_reuseFailAlloc_4448_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_4439_ = l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg(v_cls_4309_, v___x_4438_, v___y_4399_, v___y_4400_, v___y_4401_, v___y_4402_);
                if leanh::lean_obj_tag(v___x_4439_) == 0 {
                    leanh::lean_dec_ref_known(v___x_4439_, 1);
                    v___y_4366_ = v_snd_4419_;
                    v___y_4367_ = v_synthOrder_4404_;
                    v___y_4368_ = v_fst_4415_;
                    v___y_4369_ = v___y_4397_;
                    v___y_4370_ = v___y_4398_;
                    v___y_4371_ = v___y_4399_;
                    v___y_4372_ = v___y_4400_;
                    v___y_4373_ = v___y_4401_;
                    v___y_4374_ = v___y_4402_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_dec(v_snd_4419_);
                    leanh::lean_dec(v_fst_4415_);
                    leanh::lean_dec_ref(v_synthOrder_4404_);
                    leanh::lean_dec_ref(v_cls_4300_);
                    leanh::lean_dec_ref(v_processing_4299_);
                    leanh::lean_dec_ref(v_plan_4298_);
                    leanh::lean_dec_ref(v_extraDeps_4297_);
                    leanh::lean_dec(v_className_4296_);
                    v_a_4440_ = leanh::lean_ctor_get(v___x_4439_, 0);
                    v_isSharedCheck_4447_ = (!leanh::lean_is_exclusive(v___x_4439_)) as u8;
                    if v_isSharedCheck_4447_ == 0 {
                        v___x_4442_ = v___x_4439_;
                        v_isShared_4443_ = v_isSharedCheck_4447_;
                        state = 18;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4440_);
                        leanh::lean_dec(v___x_4439_);
                        v___x_4442_ = leanh::lean_box(0);
                        v_isShared_4443_ = v_isSharedCheck_4447_;
                        state = 18;
                        continue;
                    }
                }
            }
            18 => {
                if v_isShared_4443_ == 0 {
                    v___x_4445_ = v___x_4442_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_4446_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4446_, 0, v_a_4440_);
                    v___x_4445_ = v_reuseFailAlloc_4446_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_4445_;
            }
            20 => {
                if v_isShared_4454_ == 0 {
                    v___x_4456_ = v___x_4453_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_4457_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4457_, 0, v_a_4451_);
                    v___x_4456_ = v_reuseFailAlloc_4457_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_4456_;
            }
            22 => {
                if v_isShared_4465_ == 0 {
                    v___x_4467_ = v___x_4464_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_4468_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4468_, 0, v_a_4462_);
                    v___x_4467_ = v_reuseFailAlloc_4468_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_4467_;
            }
            24 => {
                if v_isShared_4473_ == 0 {
                    v___x_4475_ = v___x_4472_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_4476_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4476_, 0, v_a_4470_);
                    v___x_4475_ = v_reuseFailAlloc_4476_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_4475_;
            }
            26 => {
                if v_isShared_4489_ == 0 {
                    v___x_4491_ = v___x_4488_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_4492_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4492_, 0, v_a_4486_);
                    v___x_4491_ = v_reuseFailAlloc_4492_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_4491_;
            }
            28 => {
                if v_isShared_4497_ == 0 {
                    v___x_4499_ = v___x_4496_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_4500_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4500_, 0, v_a_4494_);
                    v___x_4499_ = v_reuseFailAlloc_4500_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_4499_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__1(
    mut v_className_4502_: *mut leanh::LeanObject,
    mut v_extraDeps_4503_: *mut leanh::LeanObject,
    mut v_plan_4504_: *mut leanh::LeanObject,
    mut v_processing_4505_: *mut leanh::LeanObject,
    mut v_a_4506_: *mut leanh::LeanObject,
    mut v_as_4507_: *mut leanh::LeanObject,
    mut v_sz_4508_: usize,
    mut v_i_4509_: usize,
    mut v_b_4510_: *mut leanh::LeanObject,
    mut v___y_4511_: *mut leanh::LeanObject,
    mut v___y_4512_: *mut leanh::LeanObject,
    mut v___y_4513_: *mut leanh::LeanObject,
    mut v___y_4514_: *mut leanh::LeanObject,
    mut v___y_4515_: *mut leanh::LeanObject,
    mut v___y_4516_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4518_: u8 = 0;
    let mut v___x_4519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4526_: u8 = 0;
    let mut v___x_4527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4532_: u8 = 0;
    let mut v_a_4533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4536_: u8 = 0;
    let mut v___x_4537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4539_: u8 = 0;
    let mut v___x_4540_: usize = 0;
    let mut v___x_4541_: usize = 0;
    let mut v___x_4544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4546_: u8 = 0;
    let mut v___x_4547_: u8 = 0;
    let mut v_isSharedCheck_4548_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4518_ = lean_usize_dec_lt(v_i_4509_, v_sz_4508_);
                if v___x_4518_ == 0 {
                    leanh::lean_dec_ref(v_a_4506_);
                    leanh::lean_dec_ref(v_processing_4505_);
                    leanh::lean_dec_ref(v_plan_4504_);
                    leanh::lean_dec_ref(v_extraDeps_4503_);
                    leanh::lean_dec(v_className_4502_);
                    v___x_4519_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4519_, 0, v_b_4510_);
                    return v___x_4519_;
                } else {
                    leanh::lean_dec_ref(v_b_4510_);
                    v___x_4520_ = leanh::lean_box(0);
                    v_a_4521_ = lean_array_uget_borrowed(v_as_4507_, v_i_4509_);
                    leanh::lean_inc(v_a_4521_);
                    leanh::lean_inc_ref(v_a_4506_);
                    leanh::lean_inc_ref(v_processing_4505_);
                    leanh::lean_inc_ref(v_plan_4504_);
                    leanh::lean_inc_ref(v_extraDeps_4503_);
                    leanh::lean_inc(v_className_4502_);
                    v___x_4522_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst(v_className_4502_, v_extraDeps_4503_, v_plan_4504_, v_processing_4505_, v_a_4506_, v_a_4521_, v___y_4511_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_, v___y_4516_);
                    if leanh::lean_obj_tag(v___x_4522_) == 0 {
                        leanh::lean_dec_ref(v_a_4506_);
                        leanh::lean_dec_ref(v_processing_4505_);
                        leanh::lean_dec_ref(v_plan_4504_);
                        leanh::lean_dec_ref(v_extraDeps_4503_);
                        leanh::lean_dec(v_className_4502_);
                        v_a_4523_ = leanh::lean_ctor_get(v___x_4522_, 0);
                        v_isSharedCheck_4532_ =
                            (!leanh::lean_is_exclusive(v___x_4522_)) as u8;
                        if v_isSharedCheck_4532_ == 0 {
                            v___x_4525_ = v___x_4522_;
                            v_isShared_4526_ = v_isSharedCheck_4532_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4523_);
                            leanh::lean_dec(v___x_4522_);
                            v___x_4525_ = leanh::lean_box(0);
                            v_isShared_4526_ = v_isSharedCheck_4532_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4533_ = leanh::lean_ctor_get(v___x_4522_, 0);
                        v_isSharedCheck_4548_ =
                            (!leanh::lean_is_exclusive(v___x_4522_)) as u8;
                        if v_isSharedCheck_4548_ == 0 {
                            v___x_4535_ = v___x_4522_;
                            v_isShared_4536_ = v_isSharedCheck_4548_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4533_);
                            leanh::lean_dec(v___x_4522_);
                            v___x_4535_ = leanh::lean_box(0);
                            v_isShared_4536_ = v_isSharedCheck_4548_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4527_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4527_, 0, v_a_4523_);
                v___x_4528_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4528_, 0, v___x_4527_);
                leanh::lean_ctor_set(v___x_4528_, 1, v___x_4520_);
                if v_isShared_4526_ == 0 {
                    leanh::lean_ctor_set(v___x_4525_, 0, v___x_4528_);
                    v___x_4530_ = v___x_4525_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4531_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4531_, 0, v___x_4528_);
                    v___x_4530_ = v_reuseFailAlloc_4531_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4530_;
            }
            3 => {
                v___x_4537_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__1___closed__0;
                v___x_4546_ = l_Lean_Exception_isInterrupt(v_a_4533_);
                if v___x_4546_ == 0 {
                    leanh::lean_inc(v_a_4533_);
                    v___x_4547_ = l_Lean_Exception_isRuntime(v_a_4533_);
                    v___y_4539_ = v___x_4547_;
                    state = 4;
                    continue;
                } else {
                    v___y_4539_ = v___x_4546_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v___y_4539_ == 0 {
                    leanh::lean_del_object(v___x_4535_);
                    leanh::lean_dec(v_a_4533_);
                    v___x_4540_ = 1usize;
                    v___x_4541_ = lean_usize_add(v_i_4509_, v___x_4540_);
                    v_i_4509_ = v___x_4541_;
                    v_b_4510_ = v___x_4537_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_a_4506_);
                    leanh::lean_dec_ref(v_processing_4505_);
                    leanh::lean_dec_ref(v_plan_4504_);
                    leanh::lean_dec_ref(v_extraDeps_4503_);
                    leanh::lean_dec(v_className_4502_);
                    if v_isShared_4536_ == 0 {
                        v___x_4544_ = v___x_4535_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4545_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4545_, 0, v_a_4533_);
                        v___x_4544_ = v_reuseFailAlloc_4545_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_4544_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4551_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4550_ =
        l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__0;
    v___x_4551_ = l_Lean_stringToMessageData(v___x_4550_);
    return v___x_4551_;
}
pub unsafe fn _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_4553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4554_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4553_ =
        l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__2;
    v___x_4554_ = l_Lean_stringToMessageData(v___x_4553_);
    return v___x_4554_;
}
pub unsafe fn _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_4556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4556_ =
        l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__4;
    v___x_4557_ = l_Lean_stringToMessageData(v___x_4556_);
    return v___x_4557_;
}
pub unsafe fn _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_4559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4560_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4559_ =
        l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__6;
    v___x_4560_ = l_Lean_stringToMessageData(v___x_4559_);
    return v___x_4560_;
}
pub unsafe fn _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_4562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4563_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4562_ =
        l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__8;
    v___x_4563_ = l_Lean_stringToMessageData(v___x_4562_);
    return v___x_4563_;
}
pub unsafe fn _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_4565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4566_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4565_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__10;
    v___x_4566_ = l_Lean_stringToMessageData(v___x_4565_);
    return v___x_4566_;
}
pub unsafe fn l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go(
    mut v_className_4567_: *mut leanh::LeanObject,
    mut v_extraDeps_4568_: *mut leanh::LeanObject,
    mut v_plan_4569_: *mut leanh::LeanObject,
    mut v_processing_4570_: *mut leanh::LeanObject,
    mut v_type_4571_: *mut leanh::LeanObject,
    mut v_a_4572_: *mut leanh::LeanObject,
    mut v_a_4573_: *mut leanh::LeanObject,
    mut v_a_4574_: *mut leanh::LeanObject,
    mut v_a_4575_: *mut leanh::LeanObject,
    mut v_a_4576_: *mut leanh::LeanObject,
    mut v_a_4577_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4591_: u8 = 0;
    let mut v___x_4592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4596_: u8 = 0;
    let mut v_fileName_4597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_4601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_4605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_4606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4609_: u8 = 0;
    let mut v_cancelTk_x3f_4610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4611_: u8 = 0;
    let mut v_inheritedTraceOptions_4612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cls_4613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4624_: usize = 0;
    let mut v___x_4625_: usize = 0;
    let mut v___x_4626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4630_: u8 = 0;
    let mut v_fst_4631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4634_: u8 = 0;
    let mut v___x_4635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_4637_: u8 = 0;
    let mut v_a_4638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_4640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4642_: u8 = 0;
    let mut v___x_4643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4658_: u8 = 0;
    let mut v___x_4660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4662_: u8 = 0;
    let mut v_reuseFailAlloc_4663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4668_: u8 = 0;
    let mut v_unused_4669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4670_: u8 = 0;
    let mut v_a_4671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4674_: u8 = 0;
    let mut v___x_4676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4678_: u8 = 0;
    let mut v___y_4680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4686_: u8 = 0;
    let mut v___x_4687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4696_: u8 = 0;
    let mut v___x_4697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4711_: u8 = 0;
    let mut v___x_4713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4715_: u8 = 0;
    let mut v_a_4716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4719_: u8 = 0;
    let mut v___x_4721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4723_: u8 = 0;
    let mut v_a_4724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4727_: u8 = 0;
    let mut v___x_4729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4731_: u8 = 0;
    let mut v_a_4732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4735_: u8 = 0;
    let mut v___x_4737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4739_: u8 = 0;
    let mut v___x_4740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4757_: u8 = 0;
    let mut v___x_4759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4761_: u8 = 0;
    let mut v___x_4763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4768_: u8 = 0;
    let mut v_buckets_4769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4780_: u8 = 0;
    let mut v___x_4781_: usize = 0;
    let mut v___x_4782_: usize = 0;
    let mut v___x_4783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4787_: u8 = 0;
    let mut v___x_4789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4791_: u8 = 0;
    let mut v___x_4792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4793_: u8 = 0;
    let mut v___x_4794_: u8 = 0;
    let mut v___x_4795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_4597_ = leanh::lean_ctor_get(v_a_4576_, 0);
                v_fileMap_4598_ = leanh::lean_ctor_get(v_a_4576_, 1);
                v_options_4599_ = leanh::lean_ctor_get(v_a_4576_, 2);
                v_currRecDepth_4600_ = leanh::lean_ctor_get(v_a_4576_, 3);
                v_maxRecDepth_4601_ = leanh::lean_ctor_get(v_a_4576_, 4);
                v_ref_4602_ = leanh::lean_ctor_get(v_a_4576_, 5);
                v_currNamespace_4603_ = leanh::lean_ctor_get(v_a_4576_, 6);
                v_openDecls_4604_ = leanh::lean_ctor_get(v_a_4576_, 7);
                v_initHeartbeats_4605_ = leanh::lean_ctor_get(v_a_4576_, 8);
                v_maxHeartbeats_4606_ = leanh::lean_ctor_get(v_a_4576_, 9);
                v_quotContext_4607_ = leanh::lean_ctor_get(v_a_4576_, 10);
                v_currMacroScope_4608_ = leanh::lean_ctor_get(v_a_4576_, 11);
                v_diag_4609_ = leanh::lean_ctor_get_uint8(
                    v_a_4576_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_4610_ = leanh::lean_ctor_get(v_a_4576_, 12);
                v_suppressElabErrors_4611_ = leanh::lean_ctor_get_uint8(
                    v_a_4576_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_4612_ = leanh::lean_ctor_get(v_a_4576_, 13);
                v_cls_4613_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__2;
                v___x_4792_ = leanh::lean_unsigned_to_nat(0);
                v___x_4793_ = lean_nat_dec_eq(v_maxRecDepth_4601_, v___x_4792_);
                if v___x_4793_ == 0 {
                    v___x_4794_ = lean_nat_dec_eq(v_currRecDepth_4600_, v_maxRecDepth_4601_);
                    if v___x_4794_ == 0 {
                        state = 25;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_type_4571_);
                        leanh::lean_dec_ref(v_processing_4570_);
                        leanh::lean_dec_ref(v_plan_4569_);
                        leanh::lean_dec_ref(v_extraDeps_4568_);
                        leanh::lean_dec(v_className_4567_);
                        leanh::lean_inc(v_ref_4602_);
                        v___x_4795_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg(v_ref_4602_);
                        return v___x_4795_;
                    }
                } else {
                    state = 25;
                    continue;
                }
            }
            1 => {
                v___x_4587_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes(v_className_4567_, v_extraDeps_4568_, v_plan_4569_, v_processing_4570_, v___y_4580_, v___y_4581_, v___y_4582_, v___y_4583_, v___y_4584_, v___y_4585_, v___y_4586_);
                leanh::lean_dec_ref(v___y_4585_);
                if leanh::lean_obj_tag(v___x_4587_) == 0 {
                    v_a_4588_ = leanh::lean_ctor_get(v___x_4587_, 0);
                    v_isSharedCheck_4596_ = (!leanh::lean_is_exclusive(v___x_4587_)) as u8;
                    if v_isSharedCheck_4596_ == 0 {
                        v___x_4590_ = v___x_4587_;
                        v_isShared_4591_ = v_isSharedCheck_4596_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4588_);
                        leanh::lean_dec(v___x_4587_);
                        v___x_4590_ = leanh::lean_box(0);
                        v_isShared_4591_ = v_isSharedCheck_4596_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_type_4571_);
                    return v___x_4587_;
                }
            }
            2 => {
                v___x_4592_ = lean_array_push(v_a_4588_, v_type_4571_);
                if v_isShared_4591_ == 0 {
                    leanh::lean_ctor_set(v___x_4590_, 0, v___x_4592_);
                    v___x_4594_ = v___x_4590_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4595_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4595_, 0, v___x_4592_);
                    v___x_4594_ = v_reuseFailAlloc_4595_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4594_;
            }
            4 => {
                v___x_4623_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__1___closed__0;
                v_sz_4624_ = lean_array_size(v___y_4616_);
                v___x_4625_ = 0usize;
                leanh::lean_inc_ref(v_processing_4570_);
                leanh::lean_inc_ref(v_plan_4569_);
                leanh::lean_inc_ref(v_extraDeps_4568_);
                leanh::lean_inc(v_className_4567_);
                v___x_4626_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__1(v_className_4567_, v_extraDeps_4568_, v_plan_4569_, v_processing_4570_, v___y_4615_, v___y_4616_, v_sz_4624_, v___x_4625_, v___x_4623_, v___y_4617_, v___y_4618_, v___y_4619_, v___y_4620_, v___y_4621_, v___y_4622_);
                leanh::lean_dec_ref(v___y_4616_);
                if leanh::lean_obj_tag(v___x_4626_) == 0 {
                    v_a_4627_ = leanh::lean_ctor_get(v___x_4626_, 0);
                    v_isSharedCheck_4670_ = (!leanh::lean_is_exclusive(v___x_4626_)) as u8;
                    if v_isSharedCheck_4670_ == 0 {
                        v___x_4629_ = v___x_4626_;
                        v_isShared_4630_ = v_isSharedCheck_4670_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4627_);
                        leanh::lean_dec(v___x_4626_);
                        v___x_4629_ = leanh::lean_box(0);
                        v_isShared_4630_ = v_isSharedCheck_4670_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v___y_4621_);
                    leanh::lean_dec_ref(v_type_4571_);
                    leanh::lean_dec_ref(v_processing_4570_);
                    leanh::lean_dec_ref(v_plan_4569_);
                    leanh::lean_dec_ref(v_extraDeps_4568_);
                    leanh::lean_dec(v_className_4567_);
                    v_a_4671_ = leanh::lean_ctor_get(v___x_4626_, 0);
                    v_isSharedCheck_4678_ = (!leanh::lean_is_exclusive(v___x_4626_)) as u8;
                    if v_isSharedCheck_4678_ == 0 {
                        v___x_4673_ = v___x_4626_;
                        v_isShared_4674_ = v_isSharedCheck_4678_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4671_);
                        leanh::lean_dec(v___x_4626_);
                        v___x_4673_ = leanh::lean_box(0);
                        v_isShared_4674_ = v_isSharedCheck_4678_;
                        state = 11;
                        continue;
                    }
                }
            }
            5 => {
                v_fst_4631_ = leanh::lean_ctor_get(v_a_4627_, 0);
                v_isSharedCheck_4668_ = (!leanh::lean_is_exclusive(v_a_4627_)) as u8;
                if v_isSharedCheck_4668_ == 0 {
                    v_unused_4669_ = leanh::lean_ctor_get(v_a_4627_, 1);
                    leanh::lean_dec(v_unused_4669_);
                    v___x_4633_ = v_a_4627_;
                    v_isShared_4634_ = v_isSharedCheck_4668_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_inc(v_fst_4631_);
                    leanh::lean_dec(v_a_4627_);
                    v___x_4633_ = leanh::lean_box(0);
                    v_isShared_4634_ = v_isSharedCheck_4668_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if leanh::lean_obj_tag(v_fst_4631_) == 0 {
                    leanh::lean_del_object(v___x_4629_);
                    leanh::lean_inc_ref(v_extraDeps_4568_);
                    leanh::lean_inc(v___y_4622_);
                    leanh::lean_inc_ref(v___y_4621_);
                    leanh::lean_inc(v___y_4620_);
                    leanh::lean_inc_ref(v___y_4619_);
                    leanh::lean_inc(v___y_4618_);
                    leanh::lean_inc_ref(v___y_4617_);
                    leanh::lean_inc_ref(v_type_4571_);
                    v___x_4635_ = leanh::lean_apply_8(
                        v_extraDeps_4568_,
                        v_type_4571_,
                        v___y_4617_,
                        v___y_4618_,
                        v___y_4619_,
                        v___y_4620_,
                        v___y_4621_,
                        v___y_4622_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_4635_) == 0 {
                        v_options_4636_ = leanh::lean_ctor_get(v___y_4621_, 2);
                        v_hasTrace_4637_ = leanh::lean_ctor_get_uint8(
                            v_options_4636_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        );
                        if v_hasTrace_4637_ == 0 {
                            leanh::lean_del_object(v___x_4633_);
                            v_a_4638_ = leanh::lean_ctor_get(v___x_4635_, 0);
                            leanh::lean_inc(v_a_4638_);
                            leanh::lean_dec_ref_known(v___x_4635_, 1);
                            v___y_4580_ = v_a_4638_;
                            v___y_4581_ = v___y_4617_;
                            v___y_4582_ = v___y_4618_;
                            v___y_4583_ = v___y_4619_;
                            v___y_4584_ = v___y_4620_;
                            v___y_4585_ = v___y_4621_;
                            v___y_4586_ = v___y_4622_;
                            state = 1;
                            continue;
                        } else {
                            v_a_4639_ = leanh::lean_ctor_get(v___x_4635_, 0);
                            leanh::lean_inc(v_a_4639_);
                            leanh::lean_dec_ref_known(v___x_4635_, 1);
                            v_inheritedTraceOptions_4640_ =
                                leanh::lean_ctor_get(v___y_4621_, 13);
                            v___x_4641_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3_once), _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3);
                            v___x_4642_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                v_inheritedTraceOptions_4640_,
                                v_options_4636_,
                                v___x_4641_,
                            );
                            if v___x_4642_ == 0 {
                                leanh::lean_del_object(v___x_4633_);
                                v___y_4580_ = v_a_4639_;
                                v___y_4581_ = v___y_4617_;
                                v___y_4582_ = v___y_4618_;
                                v___y_4583_ = v___y_4619_;
                                v___y_4584_ = v___y_4620_;
                                v___y_4585_ = v___y_4621_;
                                v___y_4586_ = v___y_4622_;
                                state = 1;
                                continue;
                            } else {
                                v___x_4643_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__1_once), _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__1);
                                leanh::lean_inc_ref(v_type_4571_);
                                v___x_4644_ = l_Lean_MessageData_ofExpr(v_type_4571_);
                                if v_isShared_4634_ == 0 {
                                    leanh::lean_ctor_set_tag(v___x_4633_, 7);
                                    leanh::lean_ctor_set(v___x_4633_, 1, v___x_4644_);
                                    leanh::lean_ctor_set(v___x_4633_, 0, v___x_4643_);
                                    v___x_4646_ = v___x_4633_;
                                    state = 7;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_4663_ =
                                        leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4663_,
                                        0,
                                        v___x_4643_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4663_,
                                        1,
                                        v___x_4644_,
                                    );
                                    v___x_4646_ = v_reuseFailAlloc_4663_;
                                    state = 7;
                                    continue;
                                }
                            }
                        }
                    } else {
                        leanh::lean_del_object(v___x_4633_);
                        leanh::lean_dec_ref(v___y_4621_);
                        leanh::lean_dec_ref(v_type_4571_);
                        leanh::lean_dec_ref(v_processing_4570_);
                        leanh::lean_dec_ref(v_plan_4569_);
                        leanh::lean_dec_ref(v_extraDeps_4568_);
                        leanh::lean_dec(v_className_4567_);
                        return v___x_4635_;
                    }
                } else {
                    leanh::lean_del_object(v___x_4633_);
                    leanh::lean_dec_ref(v___y_4621_);
                    leanh::lean_dec_ref(v_type_4571_);
                    leanh::lean_dec_ref(v_processing_4570_);
                    leanh::lean_dec_ref(v_plan_4569_);
                    leanh::lean_dec_ref(v_extraDeps_4568_);
                    leanh::lean_dec(v_className_4567_);
                    v_val_4664_ = leanh::lean_ctor_get(v_fst_4631_, 0);
                    leanh::lean_inc(v_val_4664_);
                    leanh::lean_dec_ref_known(v_fst_4631_, 1);
                    if v_isShared_4630_ == 0 {
                        leanh::lean_ctor_set(v___x_4629_, 0, v_val_4664_);
                        v___x_4666_ = v___x_4629_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_4667_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4667_, 0, v_val_4664_);
                        v___x_4666_ = v_reuseFailAlloc_4667_;
                        state = 10;
                        continue;
                    }
                }
            }
            7 => {
                v___x_4647_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__3_once), _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__3);
                v___x_4648_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4648_, 0, v___x_4646_);
                leanh::lean_ctor_set(v___x_4648_, 1, v___x_4647_);
                leanh::lean_inc(v_a_4639_);
                v___x_4649_ = lean_array_to_list(v_a_4639_);
                v___x_4650_ = leanh::lean_box(0);
                v___x_4651_ = l_List_mapTR_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__2(v___x_4649_, v___x_4650_);
                v___x_4652_ = l_Lean_MessageData_ofList(v___x_4651_);
                v___x_4653_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4653_, 0, v___x_4648_);
                leanh::lean_ctor_set(v___x_4653_, 1, v___x_4652_);
                v___x_4654_ = l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg(v_cls_4613_, v___x_4653_, v___y_4619_, v___y_4620_, v___y_4621_, v___y_4622_);
                if leanh::lean_obj_tag(v___x_4654_) == 0 {
                    leanh::lean_dec_ref_known(v___x_4654_, 1);
                    v___y_4580_ = v_a_4639_;
                    v___y_4581_ = v___y_4617_;
                    v___y_4582_ = v___y_4618_;
                    v___y_4583_ = v___y_4619_;
                    v___y_4584_ = v___y_4620_;
                    v___y_4585_ = v___y_4621_;
                    v___y_4586_ = v___y_4622_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v_a_4639_);
                    leanh::lean_dec_ref(v___y_4621_);
                    leanh::lean_dec_ref(v_type_4571_);
                    leanh::lean_dec_ref(v_processing_4570_);
                    leanh::lean_dec_ref(v_plan_4569_);
                    leanh::lean_dec_ref(v_extraDeps_4568_);
                    leanh::lean_dec(v_className_4567_);
                    v_a_4655_ = leanh::lean_ctor_get(v___x_4654_, 0);
                    v_isSharedCheck_4662_ = (!leanh::lean_is_exclusive(v___x_4654_)) as u8;
                    if v_isSharedCheck_4662_ == 0 {
                        v___x_4657_ = v___x_4654_;
                        v_isShared_4658_ = v_isSharedCheck_4662_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4655_);
                        leanh::lean_dec(v___x_4654_);
                        v___x_4657_ = leanh::lean_box(0);
                        v_isShared_4658_ = v_isSharedCheck_4662_;
                        state = 8;
                        continue;
                    }
                }
            }
            8 => {
                if v_isShared_4658_ == 0 {
                    v___x_4660_ = v___x_4657_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4661_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4661_, 0, v_a_4655_);
                    v___x_4660_ = v_reuseFailAlloc_4661_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4660_;
            }
            10 => {
                return v___x_4666_;
            }
            11 => {
                if v_isShared_4674_ == 0 {
                    v___x_4676_ = v___x_4673_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4677_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4677_, 0, v_a_4671_);
                    v___x_4676_ = v_reuseFailAlloc_4677_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4676_;
            }
            13 => {
                v___x_4686_ = l_Array_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__0(v_plan_4569_, v_type_4571_);
                if v___x_4686_ == 0 {
                    v___x_4687_ = leanh::lean_unsigned_to_nat(1);
                    v___x_4688_ = lean_mk_empty_array_with_capacity(v___x_4687_);
                    leanh::lean_inc_ref(v_type_4571_);
                    v___x_4689_ = lean_array_push(v___x_4688_, v_type_4571_);
                    leanh::lean_inc(v_className_4567_);
                    v___x_4690_ = l_Lean_Meta_mkAppM(
                        v_className_4567_,
                        v___x_4689_,
                        v___y_4682_,
                        v___y_4683_,
                        v___y_4684_,
                        v___y_4685_,
                    );
                    if leanh::lean_obj_tag(v___x_4690_) == 0 {
                        v_a_4691_ = leanh::lean_ctor_get(v___x_4690_, 0);
                        leanh::lean_inc_n(v_a_4691_, 2);
                        leanh::lean_dec_ref_known(v___x_4690_, 1);
                        v___x_4692_ = l_Lean_Meta_SynthInstance_getInstances(
                            v_a_4691_,
                            v___y_4682_,
                            v___y_4683_,
                            v___y_4684_,
                            v___y_4685_,
                        );
                        if leanh::lean_obj_tag(v___x_4692_) == 0 {
                            v_a_4693_ = leanh::lean_ctor_get(v___x_4692_, 0);
                            leanh::lean_inc(v_a_4693_);
                            leanh::lean_dec_ref_known(v___x_4692_, 1);
                            v___x_4694_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___lam__0(v_cls_4613_, v___y_4680_, v___y_4681_, v___y_4682_, v___y_4683_, v___y_4684_, v___y_4685_);
                            if leanh::lean_obj_tag(v___x_4694_) == 0 {
                                v_a_4695_ = leanh::lean_ctor_get(v___x_4694_, 0);
                                leanh::lean_inc(v_a_4695_);
                                leanh::lean_dec_ref_known(v___x_4694_, 1);
                                v___x_4696_ = (leanh::lean_unbox(v_a_4695_) as u8);
                                leanh::lean_dec(v_a_4695_);
                                if v___x_4696_ == 0 {
                                    v___y_4615_ = v_a_4691_;
                                    v___y_4616_ = v_a_4693_;
                                    v___y_4617_ = v___y_4680_;
                                    v___y_4618_ = v___y_4681_;
                                    v___y_4619_ = v___y_4682_;
                                    v___y_4620_ = v___y_4683_;
                                    v___y_4621_ = v___y_4684_;
                                    v___y_4622_ = v___y_4685_;
                                    state = 4;
                                    continue;
                                } else {
                                    v___x_4697_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__5_once), _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__5);
                                    leanh::lean_inc(v_a_4691_);
                                    v___x_4698_ = l_Lean_MessageData_ofExpr(v_a_4691_);
                                    v___x_4699_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_4699_, 0, v___x_4697_);
                                    leanh::lean_ctor_set(v___x_4699_, 1, v___x_4698_);
                                    v___x_4700_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__3_once), _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__3);
                                    v___x_4701_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_4701_, 0, v___x_4699_);
                                    leanh::lean_ctor_set(v___x_4701_, 1, v___x_4700_);
                                    v___x_4702_ = lean_array_get_size(v_a_4693_);
                                    v___x_4703_ = l_Nat_reprFast(v___x_4702_);
                                    v___x_4704_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                                    leanh::lean_ctor_set(v___x_4704_, 0, v___x_4703_);
                                    v___x_4705_ = l_Lean_MessageData_ofFormat(v___x_4704_);
                                    v___x_4706_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_4706_, 0, v___x_4701_);
                                    leanh::lean_ctor_set(v___x_4706_, 1, v___x_4705_);
                                    v___x_4707_ = l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg(v_cls_4613_, v___x_4706_, v___y_4682_, v___y_4683_, v___y_4684_, v___y_4685_);
                                    if leanh::lean_obj_tag(v___x_4707_) == 0 {
                                        leanh::lean_dec_ref_known(v___x_4707_, 1);
                                        v___y_4615_ = v_a_4691_;
                                        v___y_4616_ = v_a_4693_;
                                        v___y_4617_ = v___y_4680_;
                                        v___y_4618_ = v___y_4681_;
                                        v___y_4619_ = v___y_4682_;
                                        v___y_4620_ = v___y_4683_;
                                        v___y_4621_ = v___y_4684_;
                                        v___y_4622_ = v___y_4685_;
                                        state = 4;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v_a_4693_);
                                        leanh::lean_dec(v_a_4691_);
                                        leanh::lean_dec_ref(v___y_4684_);
                                        leanh::lean_dec_ref(v_type_4571_);
                                        leanh::lean_dec_ref(v_processing_4570_);
                                        leanh::lean_dec_ref(v_plan_4569_);
                                        leanh::lean_dec_ref(v_extraDeps_4568_);
                                        leanh::lean_dec(v_className_4567_);
                                        v_a_4708_ = leanh::lean_ctor_get(v___x_4707_, 0);
                                        v_isSharedCheck_4715_ =
                                            (!leanh::lean_is_exclusive(v___x_4707_)) as u8;
                                        if v_isSharedCheck_4715_ == 0 {
                                            v___x_4710_ = v___x_4707_;
                                            v_isShared_4711_ = v_isSharedCheck_4715_;
                                            state = 14;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_4708_);
                                            leanh::lean_dec(v___x_4707_);
                                            v___x_4710_ = leanh::lean_box(0);
                                            v_isShared_4711_ = v_isSharedCheck_4715_;
                                            state = 14;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                leanh::lean_dec(v_a_4693_);
                                leanh::lean_dec(v_a_4691_);
                                leanh::lean_dec_ref(v___y_4684_);
                                leanh::lean_dec_ref(v_type_4571_);
                                leanh::lean_dec_ref(v_processing_4570_);
                                leanh::lean_dec_ref(v_plan_4569_);
                                leanh::lean_dec_ref(v_extraDeps_4568_);
                                leanh::lean_dec(v_className_4567_);
                                v_a_4716_ = leanh::lean_ctor_get(v___x_4694_, 0);
                                v_isSharedCheck_4723_ =
                                    (!leanh::lean_is_exclusive(v___x_4694_)) as u8;
                                if v_isSharedCheck_4723_ == 0 {
                                    v___x_4718_ = v___x_4694_;
                                    v_isShared_4719_ = v_isSharedCheck_4723_;
                                    state = 16;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_4716_);
                                    leanh::lean_dec(v___x_4694_);
                                    v___x_4718_ = leanh::lean_box(0);
                                    v_isShared_4719_ = v_isSharedCheck_4723_;
                                    state = 16;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_a_4691_);
                            leanh::lean_dec_ref(v___y_4684_);
                            leanh::lean_dec_ref(v_type_4571_);
                            leanh::lean_dec_ref(v_processing_4570_);
                            leanh::lean_dec_ref(v_plan_4569_);
                            leanh::lean_dec_ref(v_extraDeps_4568_);
                            leanh::lean_dec(v_className_4567_);
                            v_a_4724_ = leanh::lean_ctor_get(v___x_4692_, 0);
                            v_isSharedCheck_4731_ =
                                (!leanh::lean_is_exclusive(v___x_4692_)) as u8;
                            if v_isSharedCheck_4731_ == 0 {
                                v___x_4726_ = v___x_4692_;
                                v_isShared_4727_ = v_isSharedCheck_4731_;
                                state = 18;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4724_);
                                leanh::lean_dec(v___x_4692_);
                                v___x_4726_ = leanh::lean_box(0);
                                v_isShared_4727_ = v_isSharedCheck_4731_;
                                state = 18;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v___y_4684_);
                        leanh::lean_dec_ref(v_type_4571_);
                        leanh::lean_dec_ref(v_processing_4570_);
                        leanh::lean_dec_ref(v_plan_4569_);
                        leanh::lean_dec_ref(v_extraDeps_4568_);
                        leanh::lean_dec(v_className_4567_);
                        v_a_4732_ = leanh::lean_ctor_get(v___x_4690_, 0);
                        v_isSharedCheck_4739_ =
                            (!leanh::lean_is_exclusive(v___x_4690_)) as u8;
                        if v_isSharedCheck_4739_ == 0 {
                            v___x_4734_ = v___x_4690_;
                            v_isShared_4735_ = v_isSharedCheck_4739_;
                            state = 20;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4732_);
                            leanh::lean_dec(v___x_4690_);
                            v___x_4734_ = leanh::lean_box(0);
                            v_isShared_4735_ = v_isSharedCheck_4739_;
                            state = 20;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___y_4684_);
                    leanh::lean_dec_ref(v_type_4571_);
                    leanh::lean_dec_ref(v_processing_4570_);
                    leanh::lean_dec_ref(v_extraDeps_4568_);
                    leanh::lean_dec(v_className_4567_);
                    v___x_4740_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4740_, 0, v_plan_4569_);
                    return v___x_4740_;
                }
            }
            14 => {
                if v_isShared_4711_ == 0 {
                    v___x_4713_ = v___x_4710_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4714_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4714_, 0, v_a_4708_);
                    v___x_4713_ = v_reuseFailAlloc_4714_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_4713_;
            }
            16 => {
                if v_isShared_4719_ == 0 {
                    v___x_4721_ = v___x_4718_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_4722_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4722_, 0, v_a_4716_);
                    v___x_4721_ = v_reuseFailAlloc_4722_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_4721_;
            }
            18 => {
                if v_isShared_4727_ == 0 {
                    v___x_4729_ = v___x_4726_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_4730_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4730_, 0, v_a_4724_);
                    v___x_4729_ = v_reuseFailAlloc_4730_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_4729_;
            }
            20 => {
                if v_isShared_4735_ == 0 {
                    v___x_4737_ = v___x_4734_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_4738_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4738_, 0, v_a_4732_);
                    v___x_4737_ = v_reuseFailAlloc_4738_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_4737_;
            }
            22 => {
                v___x_4746_ = l_List_mapTR_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__2(v___y_4745_, v___y_4744_);
                v___x_4747_ = l_Lean_MessageData_ofList(v___x_4746_);
                v___x_4748_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4748_, 0, v___y_4743_);
                leanh::lean_ctor_set(v___x_4748_, 1, v___x_4747_);
                v___x_4749_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__7_once), _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__7);
                v___x_4750_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4750_, 0, v___x_4748_);
                leanh::lean_ctor_set(v___x_4750_, 1, v___x_4749_);
                leanh::lean_inc_ref(v_type_4571_);
                v___x_4751_ = l_Lean_MessageData_ofExpr(v_type_4571_);
                v___x_4752_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4752_, 0, v___x_4750_);
                leanh::lean_ctor_set(v___x_4752_, 1, v___x_4751_);
                v___x_4753_ = l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg(v_cls_4613_, v___x_4752_, v_a_4574_, v_a_4575_, v___y_4742_, v_a_4577_);
                if leanh::lean_obj_tag(v___x_4753_) == 0 {
                    leanh::lean_dec_ref_known(v___x_4753_, 1);
                    v___y_4680_ = v_a_4572_;
                    v___y_4681_ = v_a_4573_;
                    v___y_4682_ = v_a_4574_;
                    v___y_4683_ = v_a_4575_;
                    v___y_4684_ = v___y_4742_;
                    v___y_4685_ = v_a_4577_;
                    state = 13;
                    continue;
                } else {
                    leanh::lean_dec_ref(v___y_4742_);
                    leanh::lean_dec_ref(v_type_4571_);
                    leanh::lean_dec_ref(v_processing_4570_);
                    leanh::lean_dec_ref(v_plan_4569_);
                    leanh::lean_dec_ref(v_extraDeps_4568_);
                    leanh::lean_dec(v_className_4567_);
                    v_a_4754_ = leanh::lean_ctor_get(v___x_4753_, 0);
                    v_isSharedCheck_4761_ = (!leanh::lean_is_exclusive(v___x_4753_)) as u8;
                    if v_isSharedCheck_4761_ == 0 {
                        v___x_4756_ = v___x_4753_;
                        v_isShared_4757_ = v_isSharedCheck_4761_;
                        state = 23;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4754_);
                        leanh::lean_dec(v___x_4753_);
                        v___x_4756_ = leanh::lean_box(0);
                        v_isShared_4757_ = v_isSharedCheck_4761_;
                        state = 23;
                        continue;
                    }
                }
            }
            23 => {
                if v_isShared_4757_ == 0 {
                    v___x_4759_ = v___x_4756_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_4760_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4760_, 0, v_a_4754_);
                    v___x_4759_ = v_reuseFailAlloc_4760_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_4759_;
            }
            25 => {
                v___x_4763_ = leanh::lean_unsigned_to_nat(1);
                v___x_4764_ = lean_nat_add(v_currRecDepth_4600_, v___x_4763_);
                leanh::lean_inc_ref(v_inheritedTraceOptions_4612_);
                leanh::lean_inc(v_cancelTk_x3f_4610_);
                leanh::lean_inc(v_currMacroScope_4608_);
                leanh::lean_inc(v_quotContext_4607_);
                leanh::lean_inc(v_maxHeartbeats_4606_);
                leanh::lean_inc(v_initHeartbeats_4605_);
                leanh::lean_inc(v_openDecls_4604_);
                leanh::lean_inc(v_currNamespace_4603_);
                leanh::lean_inc(v_ref_4602_);
                leanh::lean_inc(v_maxRecDepth_4601_);
                leanh::lean_inc_ref(v_options_4599_);
                leanh::lean_inc_ref(v_fileMap_4598_);
                leanh::lean_inc_ref(v_fileName_4597_);
                v___x_4765_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
                leanh::lean_ctor_set(v___x_4765_, 0, v_fileName_4597_);
                leanh::lean_ctor_set(v___x_4765_, 1, v_fileMap_4598_);
                leanh::lean_ctor_set(v___x_4765_, 2, v_options_4599_);
                leanh::lean_ctor_set(v___x_4765_, 3, v___x_4764_);
                leanh::lean_ctor_set(v___x_4765_, 4, v_maxRecDepth_4601_);
                leanh::lean_ctor_set(v___x_4765_, 5, v_ref_4602_);
                leanh::lean_ctor_set(v___x_4765_, 6, v_currNamespace_4603_);
                leanh::lean_ctor_set(v___x_4765_, 7, v_openDecls_4604_);
                leanh::lean_ctor_set(v___x_4765_, 8, v_initHeartbeats_4605_);
                leanh::lean_ctor_set(v___x_4765_, 9, v_maxHeartbeats_4606_);
                leanh::lean_ctor_set(v___x_4765_, 10, v_quotContext_4607_);
                leanh::lean_ctor_set(v___x_4765_, 11, v_currMacroScope_4608_);
                leanh::lean_ctor_set(v___x_4765_, 12, v_cancelTk_x3f_4610_);
                leanh::lean_ctor_set(v___x_4765_, 13, v_inheritedTraceOptions_4612_);
                leanh::lean_ctor_set_uint8(
                    v___x_4765_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                    v_diag_4609_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_4765_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_4611_,
                );
                v___x_4766_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___lam__0(v_cls_4613_, v_a_4572_, v_a_4573_, v_a_4574_, v_a_4575_, v___x_4765_, v_a_4577_);
                if leanh::lean_obj_tag(v___x_4766_) == 0 {
                    v_a_4767_ = leanh::lean_ctor_get(v___x_4766_, 0);
                    leanh::lean_inc(v_a_4767_);
                    leanh::lean_dec_ref_known(v___x_4766_, 1);
                    v___x_4768_ = (leanh::lean_unbox(v_a_4767_) as u8);
                    leanh::lean_dec(v_a_4767_);
                    if v___x_4768_ == 0 {
                        v___y_4680_ = v_a_4572_;
                        v___y_4681_ = v_a_4573_;
                        v___y_4682_ = v_a_4574_;
                        v___y_4683_ = v_a_4575_;
                        v___y_4684_ = v___x_4765_;
                        v___y_4685_ = v_a_4577_;
                        state = 13;
                        continue;
                    } else {
                        v_buckets_4769_ = leanh::lean_ctor_get(v_processing_4570_, 1);
                        v___x_4770_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__9_once), _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__9);
                        leanh::lean_inc_ref(v_plan_4569_);
                        v___x_4771_ = lean_array_to_list(v_plan_4569_);
                        v___x_4772_ = leanh::lean_box(0);
                        v___x_4773_ = l_List_mapTR_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__2(v___x_4771_, v___x_4772_);
                        v___x_4774_ = l_Lean_MessageData_ofList(v___x_4773_);
                        v___x_4775_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_4775_, 0, v___x_4770_);
                        leanh::lean_ctor_set(v___x_4775_, 1, v___x_4774_);
                        v___x_4776_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__11_once), _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__11);
                        v___x_4777_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_4777_, 0, v___x_4775_);
                        leanh::lean_ctor_set(v___x_4777_, 1, v___x_4776_);
                        v___x_4778_ = lean_array_get_size(v_buckets_4769_);
                        v___x_4779_ = leanh::lean_unsigned_to_nat(0);
                        v___x_4780_ = lean_nat_dec_lt(v___x_4779_, v___x_4778_);
                        if v___x_4780_ == 0 {
                            v___y_4742_ = v___x_4765_;
                            v___y_4743_ = v___x_4777_;
                            v___y_4744_ = v___x_4772_;
                            v___y_4745_ = v___x_4772_;
                            state = 22;
                            continue;
                        } else {
                            v___x_4781_ = lean_usize_of_nat(v___x_4778_);
                            v___x_4782_ = 0usize;
                            v___x_4783_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__5(v_buckets_4769_, v___x_4781_, v___x_4782_, v___x_4772_);
                            v___y_4742_ = v___x_4765_;
                            v___y_4743_ = v___x_4777_;
                            v___y_4744_ = v___x_4772_;
                            v___y_4745_ = v___x_4783_;
                            state = 22;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref_known(v___x_4765_, 14);
                    leanh::lean_dec_ref(v_type_4571_);
                    leanh::lean_dec_ref(v_processing_4570_);
                    leanh::lean_dec_ref(v_plan_4569_);
                    leanh::lean_dec_ref(v_extraDeps_4568_);
                    leanh::lean_dec(v_className_4567_);
                    v_a_4784_ = leanh::lean_ctor_get(v___x_4766_, 0);
                    v_isSharedCheck_4791_ = (!leanh::lean_is_exclusive(v___x_4766_)) as u8;
                    if v_isSharedCheck_4791_ == 0 {
                        v___x_4786_ = v___x_4766_;
                        v_isShared_4787_ = v_isSharedCheck_4791_;
                        state = 26;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4784_);
                        leanh::lean_dec(v___x_4766_);
                        v___x_4786_ = leanh::lean_box(0);
                        v_isShared_4787_ = v_isSharedCheck_4791_;
                        state = 26;
                        continue;
                    }
                }
            }
            26 => {
                if v_isShared_4787_ == 0 {
                    v___x_4789_ = v___x_4786_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_4790_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4790_, 0, v_a_4784_);
                    v___x_4789_ = v_reuseFailAlloc_4790_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_4789_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__11(
    mut v_processing_4796_: *mut leanh::LeanObject,
    mut v_className_4797_: *mut leanh::LeanObject,
    mut v_extraDeps_4798_: *mut leanh::LeanObject,
    mut v_as_4799_: *mut leanh::LeanObject,
    mut v_sz_4800_: usize,
    mut v_i_4801_: usize,
    mut v_b_4802_: *mut leanh::LeanObject,
    mut v___y_4803_: *mut leanh::LeanObject,
    mut v___y_4804_: *mut leanh::LeanObject,
    mut v___y_4805_: *mut leanh::LeanObject,
    mut v___y_4806_: *mut leanh::LeanObject,
    mut v___y_4807_: *mut leanh::LeanObject,
    mut v___y_4808_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4810_: u8 = 0;
    let mut v___x_4811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4817_: usize = 0;
    let mut v___x_4818_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4810_ = lean_usize_dec_lt(v_i_4801_, v_sz_4800_);
                if v___x_4810_ == 0 {
                    leanh::lean_dec_ref(v_extraDeps_4798_);
                    leanh::lean_dec(v_className_4797_);
                    leanh::lean_dec_ref(v_processing_4796_);
                    v___x_4811_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4811_, 0, v_b_4802_);
                    return v___x_4811_;
                } else {
                    v_a_4812_ = lean_array_uget_borrowed(v_as_4799_, v_i_4801_);
                    v___x_4813_ = leanh::lean_box(0);
                    leanh::lean_inc_n(v_a_4812_, 2);
                    leanh::lean_inc_ref(v_processing_4796_);
                    v___x_4814_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8___redArg(v_processing_4796_, v_a_4812_, v___x_4813_);
                    leanh::lean_inc_ref(v_extraDeps_4798_);
                    leanh::lean_inc(v_className_4797_);
                    v___x_4815_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go(v_className_4797_, v_extraDeps_4798_, v_b_4802_, v___x_4814_, v_a_4812_, v___y_4803_, v___y_4804_, v___y_4805_, v___y_4806_, v___y_4807_, v___y_4808_);
                    if leanh::lean_obj_tag(v___x_4815_) == 0 {
                        v_a_4816_ = leanh::lean_ctor_get(v___x_4815_, 0);
                        leanh::lean_inc(v_a_4816_);
                        leanh::lean_dec_ref_known(v___x_4815_, 1);
                        v___x_4817_ = 1usize;
                        v___x_4818_ = lean_usize_add(v_i_4801_, v___x_4817_);
                        v_i_4801_ = v___x_4818_;
                        v_b_4802_ = v_a_4816_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_extraDeps_4798_);
                        leanh::lean_dec(v_className_4797_);
                        leanh::lean_dec_ref(v_processing_4796_);
                        return v___x_4815_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__11___boxed(
    mut v_processing_4820_: *mut leanh::LeanObject,
    mut v_className_4821_: *mut leanh::LeanObject,
    mut v_extraDeps_4822_: *mut leanh::LeanObject,
    mut v_as_4823_: *mut leanh::LeanObject,
    mut v_sz_4824_: *mut leanh::LeanObject,
    mut v_i_4825_: *mut leanh::LeanObject,
    mut v_b_4826_: *mut leanh::LeanObject,
    mut v___y_4827_: *mut leanh::LeanObject,
    mut v___y_4828_: *mut leanh::LeanObject,
    mut v___y_4829_: *mut leanh::LeanObject,
    mut v___y_4830_: *mut leanh::LeanObject,
    mut v___y_4831_: *mut leanh::LeanObject,
    mut v___y_4832_: *mut leanh::LeanObject,
    mut v___y_4833_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4834_: usize = 0;
    let mut v_i_boxed_4835_: usize = 0;
    let mut v_res_4836_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4834_ = leanh::lean_unbox_usize(v_sz_4824_);
    leanh::lean_dec(v_sz_4824_);
    v_i_boxed_4835_ = leanh::lean_unbox_usize(v_i_4825_);
    leanh::lean_dec(v_i_4825_);
    v_res_4836_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__11(v_processing_4820_, v_className_4821_, v_extraDeps_4822_, v_as_4823_, v_sz_boxed_4834_, v_i_boxed_4835_, v_b_4826_, v___y_4827_, v___y_4828_, v___y_4829_, v___y_4830_, v___y_4831_, v___y_4832_);
    leanh::lean_dec(v___y_4832_);
    leanh::lean_dec_ref(v___y_4831_);
    leanh::lean_dec(v___y_4830_);
    leanh::lean_dec_ref(v___y_4829_);
    leanh::lean_dec(v___y_4828_);
    leanh::lean_dec_ref(v___y_4827_);
    leanh::lean_dec_ref(v_as_4823_);
    return v_res_4836_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__1___boxed(
    mut v_className_4837_: *mut leanh::LeanObject,
    mut v_extraDeps_4838_: *mut leanh::LeanObject,
    mut v_plan_4839_: *mut leanh::LeanObject,
    mut v_processing_4840_: *mut leanh::LeanObject,
    mut v_a_4841_: *mut leanh::LeanObject,
    mut v_as_4842_: *mut leanh::LeanObject,
    mut v_sz_4843_: *mut leanh::LeanObject,
    mut v_i_4844_: *mut leanh::LeanObject,
    mut v_b_4845_: *mut leanh::LeanObject,
    mut v___y_4846_: *mut leanh::LeanObject,
    mut v___y_4847_: *mut leanh::LeanObject,
    mut v___y_4848_: *mut leanh::LeanObject,
    mut v___y_4849_: *mut leanh::LeanObject,
    mut v___y_4850_: *mut leanh::LeanObject,
    mut v___y_4851_: *mut leanh::LeanObject,
    mut v___y_4852_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4853_: usize = 0;
    let mut v_i_boxed_4854_: usize = 0;
    let mut v_res_4855_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4853_ = leanh::lean_unbox_usize(v_sz_4843_);
    leanh::lean_dec(v_sz_4843_);
    v_i_boxed_4854_ = leanh::lean_unbox_usize(v_i_4844_);
    leanh::lean_dec(v_i_4844_);
    v_res_4855_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__1(v_className_4837_, v_extraDeps_4838_, v_plan_4839_, v_processing_4840_, v_a_4841_, v_as_4842_, v_sz_boxed_4853_, v_i_boxed_4854_, v_b_4845_, v___y_4846_, v___y_4847_, v___y_4848_, v___y_4849_, v___y_4850_, v___y_4851_);
    leanh::lean_dec(v___y_4851_);
    leanh::lean_dec_ref(v___y_4850_);
    leanh::lean_dec(v___y_4849_);
    leanh::lean_dec_ref(v___y_4848_);
    leanh::lean_dec(v___y_4847_);
    leanh::lean_dec_ref(v___y_4846_);
    leanh::lean_dec_ref(v_as_4842_);
    return v_res_4855_;
}
pub unsafe fn l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___boxed(
    mut v_className_4856_: *mut leanh::LeanObject,
    mut v_extraDeps_4857_: *mut leanh::LeanObject,
    mut v_plan_4858_: *mut leanh::LeanObject,
    mut v_processing_4859_: *mut leanh::LeanObject,
    mut v_depTypes_4860_: *mut leanh::LeanObject,
    mut v_a_4861_: *mut leanh::LeanObject,
    mut v_a_4862_: *mut leanh::LeanObject,
    mut v_a_4863_: *mut leanh::LeanObject,
    mut v_a_4864_: *mut leanh::LeanObject,
    mut v_a_4865_: *mut leanh::LeanObject,
    mut v_a_4866_: *mut leanh::LeanObject,
    mut v_a_4867_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4868_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4868_ =
        l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes(
            v_className_4856_,
            v_extraDeps_4857_,
            v_plan_4858_,
            v_processing_4859_,
            v_depTypes_4860_,
            v_a_4861_,
            v_a_4862_,
            v_a_4863_,
            v_a_4864_,
            v_a_4865_,
            v_a_4866_,
        );
    leanh::lean_dec(v_a_4866_);
    leanh::lean_dec_ref(v_a_4865_);
    leanh::lean_dec(v_a_4864_);
    leanh::lean_dec_ref(v_a_4863_);
    leanh::lean_dec(v_a_4862_);
    leanh::lean_dec_ref(v_a_4861_);
    return v_res_4868_;
}
pub unsafe fn l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___boxed(
    mut v_className_4869_: *mut leanh::LeanObject,
    mut v_extraDeps_4870_: *mut leanh::LeanObject,
    mut v_plan_4871_: *mut leanh::LeanObject,
    mut v_processing_4872_: *mut leanh::LeanObject,
    mut v_cls_4873_: *mut leanh::LeanObject,
    mut v_inst_4874_: *mut leanh::LeanObject,
    mut v_a_4875_: *mut leanh::LeanObject,
    mut v_a_4876_: *mut leanh::LeanObject,
    mut v_a_4877_: *mut leanh::LeanObject,
    mut v_a_4878_: *mut leanh::LeanObject,
    mut v_a_4879_: *mut leanh::LeanObject,
    mut v_a_4880_: *mut leanh::LeanObject,
    mut v_a_4881_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4882_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4882_ =
        l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst(
            v_className_4869_,
            v_extraDeps_4870_,
            v_plan_4871_,
            v_processing_4872_,
            v_cls_4873_,
            v_inst_4874_,
            v_a_4875_,
            v_a_4876_,
            v_a_4877_,
            v_a_4878_,
            v_a_4879_,
            v_a_4880_,
        );
    leanh::lean_dec(v_a_4880_);
    leanh::lean_dec_ref(v_a_4879_);
    leanh::lean_dec(v_a_4878_);
    leanh::lean_dec_ref(v_a_4877_);
    leanh::lean_dec(v_a_4876_);
    leanh::lean_dec_ref(v_a_4875_);
    return v_res_4882_;
}
pub unsafe fn l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___boxed(
    mut v_className_4883_: *mut leanh::LeanObject,
    mut v_extraDeps_4884_: *mut leanh::LeanObject,
    mut v_plan_4885_: *mut leanh::LeanObject,
    mut v_processing_4886_: *mut leanh::LeanObject,
    mut v_type_4887_: *mut leanh::LeanObject,
    mut v_a_4888_: *mut leanh::LeanObject,
    mut v_a_4889_: *mut leanh::LeanObject,
    mut v_a_4890_: *mut leanh::LeanObject,
    mut v_a_4891_: *mut leanh::LeanObject,
    mut v_a_4892_: *mut leanh::LeanObject,
    mut v_a_4893_: *mut leanh::LeanObject,
    mut v_a_4894_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4895_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4895_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go(
        v_className_4883_,
        v_extraDeps_4884_,
        v_plan_4885_,
        v_processing_4886_,
        v_type_4887_,
        v_a_4888_,
        v_a_4889_,
        v_a_4890_,
        v_a_4891_,
        v_a_4892_,
        v_a_4893_,
    );
    leanh::lean_dec(v_a_4893_);
    leanh::lean_dec_ref(v_a_4892_);
    leanh::lean_dec(v_a_4891_);
    leanh::lean_dec_ref(v_a_4890_);
    leanh::lean_dec(v_a_4889_);
    leanh::lean_dec_ref(v_a_4888_);
    return v_res_4895_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__9(
    mut v_e_4896_: *mut leanh::LeanObject,
    mut v___y_4897_: *mut leanh::LeanObject,
    mut v___y_4898_: *mut leanh::LeanObject,
    mut v___y_4899_: *mut leanh::LeanObject,
    mut v___y_4900_: *mut leanh::LeanObject,
    mut v___y_4901_: *mut leanh::LeanObject,
    mut v___y_4902_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4904_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4904_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__9___redArg(v_e_4896_, v___y_4900_);
    return v___x_4904_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__9___boxed(
    mut v_e_4905_: *mut leanh::LeanObject,
    mut v___y_4906_: *mut leanh::LeanObject,
    mut v___y_4907_: *mut leanh::LeanObject,
    mut v___y_4908_: *mut leanh::LeanObject,
    mut v___y_4909_: *mut leanh::LeanObject,
    mut v___y_4910_: *mut leanh::LeanObject,
    mut v___y_4911_: *mut leanh::LeanObject,
    mut v___y_4912_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4913_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4913_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__9(v_e_4905_, v___y_4906_, v___y_4907_, v___y_4908_, v___y_4909_, v___y_4910_, v___y_4911_);
    leanh::lean_dec(v___y_4911_);
    leanh::lean_dec_ref(v___y_4910_);
    leanh::lean_dec(v___y_4909_);
    leanh::lean_dec_ref(v___y_4908_);
    leanh::lean_dec(v___y_4907_);
    leanh::lean_dec_ref(v___y_4906_);
    return v_res_4913_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3(
    mut v_cls_4914_: *mut leanh::LeanObject,
    mut v_msg_4915_: *mut leanh::LeanObject,
    mut v___y_4916_: *mut leanh::LeanObject,
    mut v___y_4917_: *mut leanh::LeanObject,
    mut v___y_4918_: *mut leanh::LeanObject,
    mut v___y_4919_: *mut leanh::LeanObject,
    mut v___y_4920_: *mut leanh::LeanObject,
    mut v___y_4921_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4923_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4923_ = l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg(v_cls_4914_, v_msg_4915_, v___y_4918_, v___y_4919_, v___y_4920_, v___y_4921_);
    return v___x_4923_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___boxed(
    mut v_cls_4924_: *mut leanh::LeanObject,
    mut v_msg_4925_: *mut leanh::LeanObject,
    mut v___y_4926_: *mut leanh::LeanObject,
    mut v___y_4927_: *mut leanh::LeanObject,
    mut v___y_4928_: *mut leanh::LeanObject,
    mut v___y_4929_: *mut leanh::LeanObject,
    mut v___y_4930_: *mut leanh::LeanObject,
    mut v___y_4931_: *mut leanh::LeanObject,
    mut v___y_4932_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4933_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4933_ = l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3(v_cls_4924_, v_msg_4925_, v___y_4926_, v___y_4927_, v___y_4928_, v___y_4929_, v___y_4930_, v___y_4931_);
    leanh::lean_dec(v___y_4931_);
    leanh::lean_dec_ref(v___y_4930_);
    leanh::lean_dec(v___y_4929_);
    leanh::lean_dec_ref(v___y_4928_);
    leanh::lean_dec(v___y_4927_);
    leanh::lean_dec_ref(v___y_4926_);
    return v_res_4933_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8(
    mut v_00_u03b2_4934_: *mut leanh::LeanObject,
    mut v_m_4935_: *mut leanh::LeanObject,
    mut v_a_4936_: *mut leanh::LeanObject,
    mut v_b_4937_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4938_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4938_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8___redArg(v_m_4935_, v_a_4936_, v_b_4937_);
    return v___x_4938_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__12(
    mut v_00_u03b2_4939_: *mut leanh::LeanObject,
    mut v_m_4940_: *mut leanh::LeanObject,
    mut v_a_4941_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4942_: u8 = 0;
    v___x_4942_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__12___redArg(v_m_4940_, v_a_4941_);
    return v___x_4942_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__12___boxed(
    mut v_00_u03b2_4943_: *mut leanh::LeanObject,
    mut v_m_4944_: *mut leanh::LeanObject,
    mut v_a_4945_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4946_: u8 = 0;
    let mut v_r_4947_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4946_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__12(v_00_u03b2_4943_, v_m_4944_, v_a_4945_);
    leanh::lean_dec_ref(v_a_4945_);
    leanh::lean_dec_ref(v_m_4944_);
    v_r_4947_ = leanh::lean_box((v_res_4946_) as usize);
    return v_r_4947_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14(
    mut v_00_u03b1_4948_: *mut leanh::LeanObject,
    mut v_msg_4949_: *mut leanh::LeanObject,
    mut v___y_4950_: *mut leanh::LeanObject,
    mut v___y_4951_: *mut leanh::LeanObject,
    mut v___y_4952_: *mut leanh::LeanObject,
    mut v___y_4953_: *mut leanh::LeanObject,
    mut v___y_4954_: *mut leanh::LeanObject,
    mut v___y_4955_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4957_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4957_ = l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14___redArg(v_msg_4949_, v___y_4950_, v___y_4951_, v___y_4952_, v___y_4953_, v___y_4954_, v___y_4955_);
    return v___x_4957_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14___boxed(
    mut v_00_u03b1_4958_: *mut leanh::LeanObject,
    mut v_msg_4959_: *mut leanh::LeanObject,
    mut v___y_4960_: *mut leanh::LeanObject,
    mut v___y_4961_: *mut leanh::LeanObject,
    mut v___y_4962_: *mut leanh::LeanObject,
    mut v___y_4963_: *mut leanh::LeanObject,
    mut v___y_4964_: *mut leanh::LeanObject,
    mut v___y_4965_: *mut leanh::LeanObject,
    mut v___y_4966_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4967_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4967_ = l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14(v_00_u03b1_4958_, v_msg_4959_, v___y_4960_, v___y_4961_, v___y_4962_, v___y_4963_, v___y_4964_, v___y_4965_);
    leanh::lean_dec(v___y_4965_);
    leanh::lean_dec_ref(v___y_4964_);
    leanh::lean_dec(v___y_4963_);
    leanh::lean_dec_ref(v___y_4962_);
    leanh::lean_dec(v___y_4961_);
    leanh::lean_dec_ref(v___y_4960_);
    return v_res_4967_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__18(
    mut v_00_u03b1_4968_: *mut leanh::LeanObject,
    mut v_msg_4969_: *mut leanh::LeanObject,
    mut v___y_4970_: *mut leanh::LeanObject,
    mut v___y_4971_: *mut leanh::LeanObject,
    mut v___y_4972_: *mut leanh::LeanObject,
    mut v___y_4973_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4975_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4975_ = l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__18___redArg(v_msg_4969_, v___y_4970_, v___y_4971_, v___y_4972_, v___y_4973_);
    return v___x_4975_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__18___boxed(
    mut v_00_u03b1_4976_: *mut leanh::LeanObject,
    mut v_msg_4977_: *mut leanh::LeanObject,
    mut v___y_4978_: *mut leanh::LeanObject,
    mut v___y_4979_: *mut leanh::LeanObject,
    mut v___y_4980_: *mut leanh::LeanObject,
    mut v___y_4981_: *mut leanh::LeanObject,
    mut v___y_4982_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4983_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4983_ = l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__18(v_00_u03b1_4976_, v_msg_4977_, v___y_4978_, v___y_4979_, v___y_4980_, v___y_4981_);
    leanh::lean_dec(v___y_4981_);
    leanh::lean_dec_ref(v___y_4980_);
    leanh::lean_dec(v___y_4979_);
    leanh::lean_dec_ref(v___y_4978_);
    return v_res_4983_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21(
    mut v___x_4984_: *mut leanh::LeanObject,
    mut v_fst_4985_: *mut leanh::LeanObject,
    mut v_range_4986_: *mut leanh::LeanObject,
    mut v_b_4987_: *mut leanh::LeanObject,
    mut v_i_4988_: *mut leanh::LeanObject,
    mut v_hs_4989_: *mut leanh::LeanObject,
    mut v_hl_4990_: *mut leanh::LeanObject,
    mut v___y_4991_: *mut leanh::LeanObject,
    mut v___y_4992_: *mut leanh::LeanObject,
    mut v___y_4993_: *mut leanh::LeanObject,
    mut v___y_4994_: *mut leanh::LeanObject,
    mut v___y_4995_: *mut leanh::LeanObject,
    mut v___y_4996_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4998_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4998_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg(v___x_4984_, v_fst_4985_, v_range_4986_, v_b_4987_, v_i_4988_, v___y_4991_, v___y_4992_, v___y_4993_, v___y_4994_, v___y_4995_, v___y_4996_);
    return v___x_4998_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___boxed(
    mut v___x_4999_: *mut leanh::LeanObject,
    mut v_fst_5000_: *mut leanh::LeanObject,
    mut v_range_5001_: *mut leanh::LeanObject,
    mut v_b_5002_: *mut leanh::LeanObject,
    mut v_i_5003_: *mut leanh::LeanObject,
    mut v_hs_5004_: *mut leanh::LeanObject,
    mut v_hl_5005_: *mut leanh::LeanObject,
    mut v___y_5006_: *mut leanh::LeanObject,
    mut v___y_5007_: *mut leanh::LeanObject,
    mut v___y_5008_: *mut leanh::LeanObject,
    mut v___y_5009_: *mut leanh::LeanObject,
    mut v___y_5010_: *mut leanh::LeanObject,
    mut v___y_5011_: *mut leanh::LeanObject,
    mut v___y_5012_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5013_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5013_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21(v___x_4999_, v_fst_5000_, v_range_5001_, v_b_5002_, v_i_5003_, v_hs_5004_, v_hl_5005_, v___y_5006_, v___y_5007_, v___y_5008_, v___y_5009_, v___y_5010_, v___y_5011_);
    leanh::lean_dec(v___y_5011_);
    leanh::lean_dec_ref(v___y_5010_);
    leanh::lean_dec(v___y_5009_);
    leanh::lean_dec_ref(v___y_5008_);
    leanh::lean_dec(v___y_5007_);
    leanh::lean_dec_ref(v___y_5006_);
    leanh::lean_dec_ref(v_range_5001_);
    leanh::lean_dec_ref(v_fst_5000_);
    leanh::lean_dec_ref(v___x_4999_);
    return v_res_5013_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__10(
    mut v_00_u03b2_5014_: *mut leanh::LeanObject,
    mut v_a_5015_: *mut leanh::LeanObject,
    mut v_x_5016_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5017_: u8 = 0;
    v___x_5017_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__10___redArg(v_a_5015_, v_x_5016_);
    return v___x_5017_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__10___boxed(
    mut v_00_u03b2_5018_: *mut leanh::LeanObject,
    mut v_a_5019_: *mut leanh::LeanObject,
    mut v_x_5020_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5021_: u8 = 0;
    let mut v_r_5022_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5021_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__10(v_00_u03b2_5018_, v_a_5019_, v_x_5020_);
    leanh::lean_dec(v_x_5020_);
    leanh::lean_dec_ref(v_a_5019_);
    v_r_5022_ = leanh::lean_box((v_res_5021_) as usize);
    return v_r_5022_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__11(
    mut v_00_u03b2_5023_: *mut leanh::LeanObject,
    mut v_data_5024_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5025_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5025_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__11___redArg(v_data_5024_);
    return v___x_5025_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18(
    mut v_msgData_5026_: *mut leanh::LeanObject,
    mut v_macroStack_5027_: *mut leanh::LeanObject,
    mut v___y_5028_: *mut leanh::LeanObject,
    mut v___y_5029_: *mut leanh::LeanObject,
    mut v___y_5030_: *mut leanh::LeanObject,
    mut v___y_5031_: *mut leanh::LeanObject,
    mut v___y_5032_: *mut leanh::LeanObject,
    mut v___y_5033_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5035_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5035_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18___redArg(v_msgData_5026_, v_macroStack_5027_, v___y_5032_);
    return v___x_5035_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18___boxed(
    mut v_msgData_5036_: *mut leanh::LeanObject,
    mut v_macroStack_5037_: *mut leanh::LeanObject,
    mut v___y_5038_: *mut leanh::LeanObject,
    mut v___y_5039_: *mut leanh::LeanObject,
    mut v___y_5040_: *mut leanh::LeanObject,
    mut v___y_5041_: *mut leanh::LeanObject,
    mut v___y_5042_: *mut leanh::LeanObject,
    mut v___y_5043_: *mut leanh::LeanObject,
    mut v___y_5044_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5045_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5045_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18(v_msgData_5036_, v_macroStack_5037_, v___y_5038_, v___y_5039_, v___y_5040_, v___y_5041_, v___y_5042_, v___y_5043_);
    leanh::lean_dec(v___y_5043_);
    leanh::lean_dec_ref(v___y_5042_);
    leanh::lean_dec(v___y_5041_);
    leanh::lean_dec_ref(v___y_5040_);
    leanh::lean_dec(v___y_5039_);
    leanh::lean_dec_ref(v___y_5038_);
    return v_res_5045_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__11_spec__14(
    mut v_00_u03b2_5046_: *mut leanh::LeanObject,
    mut v_i_5047_: *mut leanh::LeanObject,
    mut v_source_5048_: *mut leanh::LeanObject,
    mut v_target_5049_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5050_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5050_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__11_spec__14___redArg(v_i_5047_, v_source_5048_, v_target_5049_);
    return v___x_5050_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__11_spec__14_spec__26(
    mut v_00_u03b2_5051_: *mut leanh::LeanObject,
    mut v_x_5052_: *mut leanh::LeanObject,
    mut v_x_5053_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5054_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5054_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__11_spec__14_spec__26___redArg(v_x_5052_, v_x_5053_);
    return v___x_5054_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_5055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5057_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5055_ = leanh::lean_unsigned_to_nat(32);
    v___x_5056_ = lean_mk_empty_array_with_capacity(v___x_5055_);
    v___x_5057_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_5057_, 0, v___x_5056_);
    return v___x_5057_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_5058_: usize = 0;
    let mut v___x_5059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5063_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5058_ = 5usize;
    v___x_5059_ = leanh::lean_unsigned_to_nat(0);
    v___x_5060_ = leanh::lean_unsigned_to_nat(32);
    v___x_5061_ = lean_mk_empty_array_with_capacity(v___x_5060_);
    v___x_5062_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___redArg___closed__0_once), _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___redArg___closed__0);
    v___x_5063_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_5063_, 0, v___x_5062_);
    leanh::lean_ctor_set(v___x_5063_, 1, v___x_5061_);
    leanh::lean_ctor_set(v___x_5063_, 2, v___x_5059_);
    leanh::lean_ctor_set(v___x_5063_, 3, v___x_5059_);
    leanh::lean_ctor_set_usize(v___x_5063_, 4, v___x_5058_);
    return v___x_5063_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___redArg(
    mut v___y_5064_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traces_5068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_5075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5081_: u8 = 0;
    let mut v_tid_5082_: u64 = 0;
    let mut v___x_5084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5085_: u8 = 0;
    let mut v___x_5086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5095_: u8 = 0;
    let mut v_unused_5096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5097_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5066_ = lean_st_ref_get(v___y_5064_);
                v_traceState_5067_ = leanh::lean_ctor_get(v___x_5066_, 4);
                leanh::lean_inc_ref(v_traceState_5067_);
                leanh::lean_dec(v___x_5066_);
                v_traces_5068_ = leanh::lean_ctor_get(v_traceState_5067_, 0);
                leanh::lean_inc_ref(v_traces_5068_);
                leanh::lean_dec_ref(v_traceState_5067_);
                v___x_5069_ = lean_st_ref_take(v___y_5064_);
                v_traceState_5070_ = leanh::lean_ctor_get(v___x_5069_, 4);
                v_env_5071_ = leanh::lean_ctor_get(v___x_5069_, 0);
                v_nextMacroScope_5072_ = leanh::lean_ctor_get(v___x_5069_, 1);
                v_ngen_5073_ = leanh::lean_ctor_get(v___x_5069_, 2);
                v_auxDeclNGen_5074_ = leanh::lean_ctor_get(v___x_5069_, 3);
                v_cache_5075_ = leanh::lean_ctor_get(v___x_5069_, 5);
                v_messages_5076_ = leanh::lean_ctor_get(v___x_5069_, 6);
                v_infoState_5077_ = leanh::lean_ctor_get(v___x_5069_, 7);
                v_snapshotTasks_5078_ = leanh::lean_ctor_get(v___x_5069_, 8);
                v_isSharedCheck_5097_ = (!leanh::lean_is_exclusive(v___x_5069_)) as u8;
                if v_isSharedCheck_5097_ == 0 {
                    v___x_5080_ = v___x_5069_;
                    v_isShared_5081_ = v_isSharedCheck_5097_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_5078_);
                    leanh::lean_inc(v_infoState_5077_);
                    leanh::lean_inc(v_messages_5076_);
                    leanh::lean_inc(v_cache_5075_);
                    leanh::lean_inc(v_traceState_5070_);
                    leanh::lean_inc(v_auxDeclNGen_5074_);
                    leanh::lean_inc(v_ngen_5073_);
                    leanh::lean_inc(v_nextMacroScope_5072_);
                    leanh::lean_inc(v_env_5071_);
                    leanh::lean_dec(v___x_5069_);
                    v___x_5080_ = leanh::lean_box(0);
                    v_isShared_5081_ = v_isSharedCheck_5097_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_tid_5082_ = leanh::lean_ctor_get_uint64(
                    v_traceState_5070_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_5095_ =
                    (!leanh::lean_is_exclusive(v_traceState_5070_)) as u8;
                if v_isSharedCheck_5095_ == 0 {
                    v_unused_5096_ = leanh::lean_ctor_get(v_traceState_5070_, 0);
                    leanh::lean_dec(v_unused_5096_);
                    v___x_5084_ = v_traceState_5070_;
                    v_isShared_5085_ = v_isSharedCheck_5095_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_traceState_5070_);
                    v___x_5084_ = leanh::lean_box(0);
                    v_isShared_5085_ = v_isSharedCheck_5095_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5086_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___redArg___closed__1_once), _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___redArg___closed__1);
                if v_isShared_5085_ == 0 {
                    leanh::lean_ctor_set(v___x_5084_, 0, v___x_5086_);
                    v___x_5088_ = v___x_5084_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5094_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5094_, 0, v___x_5086_);
                    leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_5094_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_tid_5082_,
                    );
                    v___x_5088_ = v_reuseFailAlloc_5094_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5081_ == 0 {
                    leanh::lean_ctor_set(v___x_5080_, 4, v___x_5088_);
                    v___x_5090_ = v___x_5080_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5093_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5093_, 0, v_env_5071_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5093_, 1, v_nextMacroScope_5072_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5093_, 2, v_ngen_5073_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5093_, 3, v_auxDeclNGen_5074_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5093_, 4, v___x_5088_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5093_, 5, v_cache_5075_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5093_, 6, v_messages_5076_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5093_, 7, v_infoState_5077_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5093_, 8, v_snapshotTasks_5078_);
                    v___x_5090_ = v_reuseFailAlloc_5093_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5091_ = lean_st_ref_set(v___y_5064_, v___x_5090_);
                v___x_5092_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5092_, 0, v_traces_5068_);
                return v___x_5092_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___redArg___boxed(
    mut v___y_5098_: *mut leanh::LeanObject,
    mut v___y_5099_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5100_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5100_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___redArg(v___y_5098_);
    leanh::lean_dec(v___y_5098_);
    return v_res_5100_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0(
    mut v___y_5101_: *mut leanh::LeanObject,
    mut v___y_5102_: *mut leanh::LeanObject,
    mut v___y_5103_: *mut leanh::LeanObject,
    mut v___y_5104_: *mut leanh::LeanObject,
    mut v___y_5105_: *mut leanh::LeanObject,
    mut v___y_5106_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5108_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5108_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___redArg(v___y_5106_);
    return v___x_5108_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___boxed(
    mut v___y_5109_: *mut leanh::LeanObject,
    mut v___y_5110_: *mut leanh::LeanObject,
    mut v___y_5111_: *mut leanh::LeanObject,
    mut v___y_5112_: *mut leanh::LeanObject,
    mut v___y_5113_: *mut leanh::LeanObject,
    mut v___y_5114_: *mut leanh::LeanObject,
    mut v___y_5115_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5116_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5116_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0(v___y_5109_, v___y_5110_, v___y_5111_, v___y_5112_, v___y_5113_, v___y_5114_);
    leanh::lean_dec(v___y_5114_);
    leanh::lean_dec_ref(v___y_5113_);
    leanh::lean_dec(v___y_5112_);
    leanh::lean_dec_ref(v___y_5111_);
    leanh::lean_dec(v___y_5110_);
    leanh::lean_dec_ref(v___y_5109_);
    return v_res_5116_;
}
pub unsafe fn _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_5118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5119_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5118_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___closed__0;
    v___x_5119_ = l_Lean_stringToMessageData(v___x_5118_);
    return v___x_5119_;
}
pub unsafe fn _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_5121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5122_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5121_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___closed__2;
    v___x_5122_ = l_Lean_stringToMessageData(v___x_5121_);
    return v___x_5122_;
}
pub unsafe fn l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0(
    mut v_className_5123_: *mut leanh::LeanObject,
    mut v_type_5124_: *mut leanh::LeanObject,
    mut v_r_5125_: *mut leanh::LeanObject,
    mut v___y_5126_: *mut leanh::LeanObject,
    mut v___y_5127_: *mut leanh::LeanObject,
    mut v___y_5128_: *mut leanh::LeanObject,
    mut v___y_5129_: *mut leanh::LeanObject,
    mut v___y_5130_: *mut leanh::LeanObject,
    mut v___y_5131_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5134_: u8 = 0;
    let mut v___x_5135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5133_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___closed__1_once), _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___closed__1);
                v___x_5134_ = 0;
                v___x_5135_ = l_Lean_MessageData_ofConstName(v_className_5123_, v___x_5134_);
                v___x_5136_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5136_, 0, v___x_5133_);
                leanh::lean_ctor_set(v___x_5136_, 1, v___x_5135_);
                v___x_5137_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___closed__3_once), _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___closed__3);
                v___x_5138_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5138_, 0, v___x_5136_);
                leanh::lean_ctor_set(v___x_5138_, 1, v___x_5137_);
                v___x_5139_ = l_Lean_MessageData_ofExpr(v_type_5124_);
                v___x_5140_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5140_, 0, v___x_5138_);
                leanh::lean_ctor_set(v___x_5140_, 1, v___x_5139_);
                v___x_5141_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__3_once), _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__3);
                v___x_5142_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5142_, 0, v___x_5140_);
                leanh::lean_ctor_set(v___x_5142_, 1, v___x_5141_);
                if leanh::lean_obj_tag(v_r_5125_) == 0 {
                    v_a_5147_ = leanh::lean_ctor_get(v_r_5125_, 0);
                    leanh::lean_inc(v_a_5147_);
                    leanh::lean_dec_ref_known(v_r_5125_, 1);
                    v___x_5148_ = l_Lean_Exception_toMessageData(v_a_5147_);
                    v___y_5144_ = v___x_5148_;
                    state = 1;
                    continue;
                } else {
                    v_a_5149_ = leanh::lean_ctor_get(v_r_5125_, 0);
                    leanh::lean_inc(v_a_5149_);
                    leanh::lean_dec_ref_known(v_r_5125_, 1);
                    v___x_5150_ = lean_array_to_list(v_a_5149_);
                    v___x_5151_ = leanh::lean_box(0);
                    v___x_5152_ = l_List_mapTR_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__2(v___x_5150_, v___x_5151_);
                    v___x_5153_ = l_Lean_MessageData_ofList(v___x_5152_);
                    v___y_5144_ = v___x_5153_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5145_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5145_, 0, v___x_5142_);
                leanh::lean_ctor_set(v___x_5145_, 1, v___y_5144_);
                v___x_5146_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5146_, 0, v___x_5145_);
                return v___x_5146_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___boxed(
    mut v_className_5154_: *mut leanh::LeanObject,
    mut v_type_5155_: *mut leanh::LeanObject,
    mut v_r_5156_: *mut leanh::LeanObject,
    mut v___y_5157_: *mut leanh::LeanObject,
    mut v___y_5158_: *mut leanh::LeanObject,
    mut v___y_5159_: *mut leanh::LeanObject,
    mut v___y_5160_: *mut leanh::LeanObject,
    mut v___y_5161_: *mut leanh::LeanObject,
    mut v___y_5162_: *mut leanh::LeanObject,
    mut v___y_5163_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5164_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5164_ =
        l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0(
            v_className_5154_,
            v_type_5155_,
            v_r_5156_,
            v___y_5157_,
            v___y_5158_,
            v___y_5159_,
            v___y_5160_,
            v___y_5161_,
            v___y_5162_,
        );
    leanh::lean_dec(v___y_5162_);
    leanh::lean_dec_ref(v___y_5161_);
    leanh::lean_dec(v___y_5160_);
    leanh::lean_dec_ref(v___y_5159_);
    leanh::lean_dec(v___y_5158_);
    leanh::lean_dec_ref(v___y_5157_);
    return v_res_5164_;
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__4(
    mut v_opts_5165_: *mut leanh::LeanObject,
    mut v_opt_5166_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_name_5167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_5168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_5169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5170_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_5167_ = leanh::lean_ctor_get(v_opt_5166_, 0);
    v_defValue_5168_ = leanh::lean_ctor_get(v_opt_5166_, 1);
    v_map_5169_ = leanh::lean_ctor_get(v_opts_5165_, 0);
    v___x_5170_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_5169_,
            v_name_5167_,
        );
    if leanh::lean_obj_tag(v___x_5170_) == 0 {
        leanh::lean_inc(v_defValue_5168_);
        return v_defValue_5168_;
    } else {
        let mut v_val_5171_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_5171_ = leanh::lean_ctor_get(v___x_5170_, 0);
        leanh::lean_inc(v_val_5171_);
        leanh::lean_dec_ref_known(v___x_5170_, 1);
        if leanh::lean_obj_tag(v_val_5171_) == 3 {
            let mut v_v_5172_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_v_5172_ = leanh::lean_ctor_get(v_val_5171_, 0);
            leanh::lean_inc(v_v_5172_);
            leanh::lean_dec_ref_known(v_val_5171_, 1);
            return v_v_5172_;
        } else {
            leanh::lean_dec(v_val_5171_);
            leanh::lean_inc(v_defValue_5168_);
            return v_defValue_5168_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__4___boxed(
    mut v_opts_5173_: *mut leanh::LeanObject,
    mut v_opt_5174_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5175_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5175_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__4(v_opts_5173_, v_opt_5174_);
    leanh::lean_dec_ref(v_opt_5174_);
    leanh::lean_dec_ref(v_opts_5173_);
    return v_res_5175_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__2_spec__3(
    mut v_sz_5176_: usize,
    mut v_i_5177_: usize,
    mut v_bs_5178_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5179_: u8 = 0;
    let mut v_v_5180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_5181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5184_: usize = 0;
    let mut v___x_5185_: usize = 0;
    let mut v___x_5186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5179_ = lean_usize_dec_lt(v_i_5177_, v_sz_5176_);
                if v___x_5179_ == 0 {
                    return v_bs_5178_;
                } else {
                    v_v_5180_ = lean_array_uget_borrowed(v_bs_5178_, v_i_5177_);
                    v_msg_5181_ = leanh::lean_ctor_get(v_v_5180_, 1);
                    leanh::lean_inc_ref(v_msg_5181_);
                    v___x_5182_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_5183_ = lean_array_uset(v_bs_5178_, v_i_5177_, v___x_5182_);
                    v___x_5184_ = 1usize;
                    v___x_5185_ = lean_usize_add(v_i_5177_, v___x_5184_);
                    v___x_5186_ = lean_array_uset(v_bs_x27_5183_, v_i_5177_, v_msg_5181_);
                    v_i_5177_ = v___x_5185_;
                    v_bs_5178_ = v___x_5186_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__2_spec__3___boxed(
    mut v_sz_5188_: *mut leanh::LeanObject,
    mut v_i_5189_: *mut leanh::LeanObject,
    mut v_bs_5190_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5191_: usize = 0;
    let mut v_i_boxed_5192_: usize = 0;
    let mut v_res_5193_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5191_ = leanh::lean_unbox_usize(v_sz_5188_);
    leanh::lean_dec(v_sz_5188_);
    v_i_boxed_5192_ = leanh::lean_unbox_usize(v_i_5189_);
    leanh::lean_dec(v_i_5189_);
    v_res_5193_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__2_spec__3(v_sz_boxed_5191_, v_i_boxed_5192_, v_bs_5190_);
    return v_res_5193_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__2___redArg(
    mut v_oldTraces_5194_: *mut leanh::LeanObject,
    mut v_data_5195_: *mut leanh::LeanObject,
    mut v_ref_5196_: *mut leanh::LeanObject,
    mut v_msg_5197_: *mut leanh::LeanObject,
    mut v___y_5198_: *mut leanh::LeanObject,
    mut v___y_5199_: *mut leanh::LeanObject,
    mut v___y_5200_: *mut leanh::LeanObject,
    mut v___y_5201_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_5203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_5204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_5205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_5206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_5207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_5211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_5212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_5213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5215_: u8 = 0;
    let mut v_cancelTk_x3f_5216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_5217_: u8 = 0;
    let mut v_inheritedTraceOptions_5218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traces_5221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5225_: usize = 0;
    let mut v___x_5226_: usize = 0;
    let mut v___x_5227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_5228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5233_: u8 = 0;
    let mut v___x_5234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_5240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5246_: u8 = 0;
    let mut v_tid_5247_: u64 = 0;
    let mut v___x_5249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5250_: u8 = 0;
    let mut v___x_5251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5264_: u8 = 0;
    let mut v_unused_5265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5266_: u8 = 0;
    let mut v_isSharedCheck_5267_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_5203_ = leanh::lean_ctor_get(v___y_5200_, 0);
                v_fileMap_5204_ = leanh::lean_ctor_get(v___y_5200_, 1);
                v_options_5205_ = leanh::lean_ctor_get(v___y_5200_, 2);
                v_currRecDepth_5206_ = leanh::lean_ctor_get(v___y_5200_, 3);
                v_maxRecDepth_5207_ = leanh::lean_ctor_get(v___y_5200_, 4);
                v_ref_5208_ = leanh::lean_ctor_get(v___y_5200_, 5);
                v_currNamespace_5209_ = leanh::lean_ctor_get(v___y_5200_, 6);
                v_openDecls_5210_ = leanh::lean_ctor_get(v___y_5200_, 7);
                v_initHeartbeats_5211_ = leanh::lean_ctor_get(v___y_5200_, 8);
                v_maxHeartbeats_5212_ = leanh::lean_ctor_get(v___y_5200_, 9);
                v_quotContext_5213_ = leanh::lean_ctor_get(v___y_5200_, 10);
                v_currMacroScope_5214_ = leanh::lean_ctor_get(v___y_5200_, 11);
                v_diag_5215_ = leanh::lean_ctor_get_uint8(
                    v___y_5200_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_5216_ = leanh::lean_ctor_get(v___y_5200_, 12);
                v_suppressElabErrors_5217_ = leanh::lean_ctor_get_uint8(
                    v___y_5200_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_5218_ = leanh::lean_ctor_get(v___y_5200_, 13);
                v___x_5219_ = lean_st_ref_get(v___y_5201_);
                v_traceState_5220_ = leanh::lean_ctor_get(v___x_5219_, 4);
                leanh::lean_inc_ref(v_traceState_5220_);
                leanh::lean_dec(v___x_5219_);
                v_traces_5221_ = leanh::lean_ctor_get(v_traceState_5220_, 0);
                leanh::lean_inc_ref(v_traces_5221_);
                leanh::lean_dec_ref(v_traceState_5220_);
                v_ref_5222_ = l_Lean_replaceRef(v_ref_5196_, v_ref_5208_);
                leanh::lean_inc_ref(v_inheritedTraceOptions_5218_);
                leanh::lean_inc(v_cancelTk_x3f_5216_);
                leanh::lean_inc(v_currMacroScope_5214_);
                leanh::lean_inc(v_quotContext_5213_);
                leanh::lean_inc(v_maxHeartbeats_5212_);
                leanh::lean_inc(v_initHeartbeats_5211_);
                leanh::lean_inc(v_openDecls_5210_);
                leanh::lean_inc(v_currNamespace_5209_);
                leanh::lean_inc(v_maxRecDepth_5207_);
                leanh::lean_inc(v_currRecDepth_5206_);
                leanh::lean_inc_ref(v_options_5205_);
                leanh::lean_inc_ref(v_fileMap_5204_);
                leanh::lean_inc_ref(v_fileName_5203_);
                v___x_5223_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
                leanh::lean_ctor_set(v___x_5223_, 0, v_fileName_5203_);
                leanh::lean_ctor_set(v___x_5223_, 1, v_fileMap_5204_);
                leanh::lean_ctor_set(v___x_5223_, 2, v_options_5205_);
                leanh::lean_ctor_set(v___x_5223_, 3, v_currRecDepth_5206_);
                leanh::lean_ctor_set(v___x_5223_, 4, v_maxRecDepth_5207_);
                leanh::lean_ctor_set(v___x_5223_, 5, v_ref_5222_);
                leanh::lean_ctor_set(v___x_5223_, 6, v_currNamespace_5209_);
                leanh::lean_ctor_set(v___x_5223_, 7, v_openDecls_5210_);
                leanh::lean_ctor_set(v___x_5223_, 8, v_initHeartbeats_5211_);
                leanh::lean_ctor_set(v___x_5223_, 9, v_maxHeartbeats_5212_);
                leanh::lean_ctor_set(v___x_5223_, 10, v_quotContext_5213_);
                leanh::lean_ctor_set(v___x_5223_, 11, v_currMacroScope_5214_);
                leanh::lean_ctor_set(v___x_5223_, 12, v_cancelTk_x3f_5216_);
                leanh::lean_ctor_set(v___x_5223_, 13, v_inheritedTraceOptions_5218_);
                leanh::lean_ctor_set_uint8(
                    v___x_5223_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                    v_diag_5215_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_5223_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_5217_,
                );
                v___x_5224_ = l_Lean_PersistentArray_toArray___redArg(v_traces_5221_);
                leanh::lean_dec_ref(v_traces_5221_);
                v_sz_5225_ = lean_array_size(v___x_5224_);
                v___x_5226_ = 0usize;
                v___x_5227_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__2_spec__3(v_sz_5225_, v___x_5226_, v___x_5224_);
                v_msg_5228_ = leanh::lean_alloc_ctor(9, 3, (0) as u32);
                leanh::lean_ctor_set(v_msg_5228_, 0, v_data_5195_);
                leanh::lean_ctor_set(v_msg_5228_, 1, v_msg_5197_);
                leanh::lean_ctor_set(v_msg_5228_, 2, v___x_5227_);
                v___x_5229_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3_spec__4(v_msg_5228_, v___y_5198_, v___y_5199_, v___x_5223_, v___y_5201_);
                leanh::lean_dec_ref_known(v___x_5223_, 14);
                v_a_5230_ = leanh::lean_ctor_get(v___x_5229_, 0);
                v_isSharedCheck_5267_ = (!leanh::lean_is_exclusive(v___x_5229_)) as u8;
                if v_isSharedCheck_5267_ == 0 {
                    v___x_5232_ = v___x_5229_;
                    v_isShared_5233_ = v_isSharedCheck_5267_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_5230_);
                    leanh::lean_dec(v___x_5229_);
                    v___x_5232_ = leanh::lean_box(0);
                    v_isShared_5233_ = v_isSharedCheck_5267_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5234_ = lean_st_ref_take(v___y_5201_);
                v_traceState_5235_ = leanh::lean_ctor_get(v___x_5234_, 4);
                v_env_5236_ = leanh::lean_ctor_get(v___x_5234_, 0);
                v_nextMacroScope_5237_ = leanh::lean_ctor_get(v___x_5234_, 1);
                v_ngen_5238_ = leanh::lean_ctor_get(v___x_5234_, 2);
                v_auxDeclNGen_5239_ = leanh::lean_ctor_get(v___x_5234_, 3);
                v_cache_5240_ = leanh::lean_ctor_get(v___x_5234_, 5);
                v_messages_5241_ = leanh::lean_ctor_get(v___x_5234_, 6);
                v_infoState_5242_ = leanh::lean_ctor_get(v___x_5234_, 7);
                v_snapshotTasks_5243_ = leanh::lean_ctor_get(v___x_5234_, 8);
                v_isSharedCheck_5266_ = (!leanh::lean_is_exclusive(v___x_5234_)) as u8;
                if v_isSharedCheck_5266_ == 0 {
                    v___x_5245_ = v___x_5234_;
                    v_isShared_5246_ = v_isSharedCheck_5266_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_5243_);
                    leanh::lean_inc(v_infoState_5242_);
                    leanh::lean_inc(v_messages_5241_);
                    leanh::lean_inc(v_cache_5240_);
                    leanh::lean_inc(v_traceState_5235_);
                    leanh::lean_inc(v_auxDeclNGen_5239_);
                    leanh::lean_inc(v_ngen_5238_);
                    leanh::lean_inc(v_nextMacroScope_5237_);
                    leanh::lean_inc(v_env_5236_);
                    leanh::lean_dec(v___x_5234_);
                    v___x_5245_ = leanh::lean_box(0);
                    v_isShared_5246_ = v_isSharedCheck_5266_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_5247_ = leanh::lean_ctor_get_uint64(
                    v_traceState_5235_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_5264_ =
                    (!leanh::lean_is_exclusive(v_traceState_5235_)) as u8;
                if v_isSharedCheck_5264_ == 0 {
                    v_unused_5265_ = leanh::lean_ctor_get(v_traceState_5235_, 0);
                    leanh::lean_dec(v_unused_5265_);
                    v___x_5249_ = v_traceState_5235_;
                    v_isShared_5250_ = v_isSharedCheck_5264_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_dec(v_traceState_5235_);
                    v___x_5249_ = leanh::lean_box(0);
                    v_isShared_5250_ = v_isSharedCheck_5264_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5251_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5251_, 0, v_ref_5196_);
                leanh::lean_ctor_set(v___x_5251_, 1, v_a_5230_);
                v___x_5252_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_5194_, v___x_5251_);
                if v_isShared_5250_ == 0 {
                    leanh::lean_ctor_set(v___x_5249_, 0, v___x_5252_);
                    v___x_5254_ = v___x_5249_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5263_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5263_, 0, v___x_5252_);
                    leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_5263_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_tid_5247_,
                    );
                    v___x_5254_ = v_reuseFailAlloc_5263_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_5246_ == 0 {
                    leanh::lean_ctor_set(v___x_5245_, 4, v___x_5254_);
                    v___x_5256_ = v___x_5245_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5262_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5262_, 0, v_env_5236_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5262_, 1, v_nextMacroScope_5237_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5262_, 2, v_ngen_5238_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5262_, 3, v_auxDeclNGen_5239_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5262_, 4, v___x_5254_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5262_, 5, v_cache_5240_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5262_, 6, v_messages_5241_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5262_, 7, v_infoState_5242_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5262_, 8, v_snapshotTasks_5243_);
                    v___x_5256_ = v_reuseFailAlloc_5262_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5257_ = lean_st_ref_set(v___y_5201_, v___x_5256_);
                v___x_5258_ = leanh::lean_box(0);
                if v_isShared_5233_ == 0 {
                    leanh::lean_ctor_set(v___x_5232_, 0, v___x_5258_);
                    v___x_5260_ = v___x_5232_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5261_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5261_, 0, v___x_5258_);
                    v___x_5260_ = v_reuseFailAlloc_5261_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5260_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__2___redArg___boxed(
    mut v_oldTraces_5268_: *mut leanh::LeanObject,
    mut v_data_5269_: *mut leanh::LeanObject,
    mut v_ref_5270_: *mut leanh::LeanObject,
    mut v_msg_5271_: *mut leanh::LeanObject,
    mut v___y_5272_: *mut leanh::LeanObject,
    mut v___y_5273_: *mut leanh::LeanObject,
    mut v___y_5274_: *mut leanh::LeanObject,
    mut v___y_5275_: *mut leanh::LeanObject,
    mut v___y_5276_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5277_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5277_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__2___redArg(v_oldTraces_5268_, v_data_5269_, v_ref_5270_, v_msg_5271_, v___y_5272_, v___y_5273_, v___y_5274_, v___y_5275_);
    leanh::lean_dec(v___y_5275_);
    leanh::lean_dec_ref(v___y_5274_);
    leanh::lean_dec(v___y_5273_);
    leanh::lean_dec_ref(v___y_5272_);
    return v_res_5277_;
}
pub unsafe fn l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__1(
    mut v_e_5278_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_e_5278_) == 0 {
        let mut v___x_5279_: u8 = 0;
        v___x_5279_ = 2;
        return v___x_5279_;
    } else {
        let mut v___x_5280_: u8 = 0;
        v___x_5280_ = 0;
        return v___x_5280_;
    }
}
pub unsafe fn l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__1___boxed(
    mut v_e_5281_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5282_: u8 = 0;
    let mut v_r_5283_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5282_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__1(v_e_5281_);
    leanh::lean_dec_ref(v_e_5281_);
    v_r_5283_ = leanh::lean_box((v_res_5282_) as usize);
    return v_r_5283_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__3___redArg(
    mut v_x_5284_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_5286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5289_: u8 = 0;
    let mut v___x_5291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5293_: u8 = 0;
    let mut v_a_5294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5297_: u8 = 0;
    let mut v___x_5299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5301_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5284_) == 0 {
                    v_a_5286_ = leanh::lean_ctor_get(v_x_5284_, 0);
                    v_isSharedCheck_5293_ = (!leanh::lean_is_exclusive(v_x_5284_)) as u8;
                    if v_isSharedCheck_5293_ == 0 {
                        v___x_5288_ = v_x_5284_;
                        v_isShared_5289_ = v_isSharedCheck_5293_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5286_);
                        leanh::lean_dec(v_x_5284_);
                        v___x_5288_ = leanh::lean_box(0);
                        v_isShared_5289_ = v_isSharedCheck_5293_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5294_ = leanh::lean_ctor_get(v_x_5284_, 0);
                    v_isSharedCheck_5301_ = (!leanh::lean_is_exclusive(v_x_5284_)) as u8;
                    if v_isSharedCheck_5301_ == 0 {
                        v___x_5296_ = v_x_5284_;
                        v_isShared_5297_ = v_isSharedCheck_5301_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5294_);
                        leanh::lean_dec(v_x_5284_);
                        v___x_5296_ = leanh::lean_box(0);
                        v_isShared_5297_ = v_isSharedCheck_5301_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5289_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5288_, 1);
                    v___x_5291_ = v___x_5288_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5292_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5292_, 0, v_a_5286_);
                    v___x_5291_ = v_reuseFailAlloc_5292_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5291_;
            }
            3 => {
                if v_isShared_5297_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5296_, 0);
                    v___x_5299_ = v___x_5296_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5300_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5300_, 0, v_a_5294_);
                    v___x_5299_ = v_reuseFailAlloc_5300_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5299_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__3___redArg___boxed(
    mut v_x_5302_: *mut leanh::LeanObject,
    mut v___y_5303_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5304_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5304_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__3___redArg(v_x_5302_);
    return v_res_5304_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_5306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5307_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5306_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___closed__0;
    v___x_5307_ = l_Lean_stringToMessageData(v___x_5306_);
    return v___x_5307_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_5309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5310_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5309_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___closed__2;
    v___x_5310_ = l_Lean_stringToMessageData(v___x_5309_);
    return v___x_5310_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___closed__4()
-> f64 {
    let mut v___x_5311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5312_: f64 = 0.0;
    v___x_5311_ = leanh::lean_unsigned_to_nat(1000);
    v___x_5312_ = lean_float_of_nat(v___x_5311_);
    return v___x_5312_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1(
    mut v_cls_5313_: *mut leanh::LeanObject,
    mut v_collapsed_5314_: u8,
    mut v_tag_5315_: *mut leanh::LeanObject,
    mut v_opts_5316_: *mut leanh::LeanObject,
    mut v_clsEnabled_5317_: u8,
    mut v_oldTraces_5318_: *mut leanh::LeanObject,
    mut v_msg_5319_: *mut leanh::LeanObject,
    mut v_resStartStop_5320_: *mut leanh::LeanObject,
    mut v___y_5321_: *mut leanh::LeanObject,
    mut v___y_5322_: *mut leanh::LeanObject,
    mut v___y_5323_: *mut leanh::LeanObject,
    mut v___y_5324_: *mut leanh::LeanObject,
    mut v___y_5325_: *mut leanh::LeanObject,
    mut v___y_5326_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_5328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5332_: u8 = 0;
    let mut v___y_5334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_5336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5342_: u8 = 0;
    let mut v___x_5344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5346_: u8 = 0;
    let mut v_fst_5347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5351_: u8 = 0;
    let mut v___x_5352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5353_: u8 = 0;
    let mut v___y_5355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_5357_: u8 = 0;
    let mut v___x_5358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_5364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5367_: f64 = 0.0;
    let mut v_data_5368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_5369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5370_: f64 = 0.0;
    let mut v___x_5371_: f64 = 0.0;
    let mut v_reuseFailAlloc_5372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5380_: u8 = 0;
    let mut v___x_5381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_5387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5393_: u8 = 0;
    let mut v_tid_5394_: u64 = 0;
    let mut v_traces_5395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5398_: u8 = 0;
    let mut v___x_5399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5408_: u8 = 0;
    let mut v_isSharedCheck_5409_: u8 = 0;
    let mut v___y_5411_: f64 = 0.0;
    let mut v___x_5412_: f64 = 0.0;
    let mut v___x_5413_: f64 = 0.0;
    let mut v___x_5414_: f64 = 0.0;
    let mut v___x_5415_: u8 = 0;
    let mut v___x_5416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5417_: u8 = 0;
    let mut v___x_5418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5420_: f64 = 0.0;
    let mut v___x_5421_: f64 = 0.0;
    let mut v___x_5422_: f64 = 0.0;
    let mut v___x_5423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5425_: f64 = 0.0;
    let mut v_isSharedCheck_5426_: u8 = 0;
    let mut v_isSharedCheck_5427_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_5328_ = leanh::lean_ctor_get(v_resStartStop_5320_, 0);
                v_snd_5329_ = leanh::lean_ctor_get(v_resStartStop_5320_, 1);
                v_isSharedCheck_5427_ =
                    (!leanh::lean_is_exclusive(v_resStartStop_5320_)) as u8;
                if v_isSharedCheck_5427_ == 0 {
                    v___x_5331_ = v_resStartStop_5320_;
                    v_isShared_5332_ = v_isSharedCheck_5427_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_5329_);
                    leanh::lean_inc(v_fst_5328_);
                    leanh::lean_dec(v_resStartStop_5320_);
                    v___x_5331_ = leanh::lean_box(0);
                    v_isShared_5332_ = v_isSharedCheck_5427_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_5347_ = leanh::lean_ctor_get(v_snd_5329_, 0);
                v_snd_5348_ = leanh::lean_ctor_get(v_snd_5329_, 1);
                v_isSharedCheck_5426_ = (!leanh::lean_is_exclusive(v_snd_5329_)) as u8;
                if v_isSharedCheck_5426_ == 0 {
                    v___x_5350_ = v_snd_5329_;
                    v_isShared_5351_ = v_isSharedCheck_5426_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_5348_);
                    leanh::lean_inc(v_fst_5347_);
                    leanh::lean_dec(v_snd_5329_);
                    v___x_5350_ = leanh::lean_box(0);
                    v_isShared_5351_ = v_isSharedCheck_5426_;
                    state = 5;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc(v___y_5334_);
                v___x_5337_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__2___redArg(v_oldTraces_5318_, v_data_5336_, v___y_5334_, v___y_5335_, v___y_5323_, v___y_5324_, v___y_5325_, v___y_5326_);
                if leanh::lean_obj_tag(v___x_5337_) == 0 {
                    leanh::lean_dec_ref_known(v___x_5337_, 1);
                    v___x_5338_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__3___redArg(v_fst_5328_);
                    return v___x_5338_;
                } else {
                    leanh::lean_dec(v_fst_5328_);
                    v_a_5339_ = leanh::lean_ctor_get(v___x_5337_, 0);
                    v_isSharedCheck_5346_ = (!leanh::lean_is_exclusive(v___x_5337_)) as u8;
                    if v_isSharedCheck_5346_ == 0 {
                        v___x_5341_ = v___x_5337_;
                        v_isShared_5342_ = v_isSharedCheck_5346_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5339_);
                        leanh::lean_dec(v___x_5337_);
                        v___x_5341_ = leanh::lean_box(0);
                        v_isShared_5342_ = v_isSharedCheck_5346_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_5342_ == 0 {
                    v___x_5344_ = v___x_5341_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5345_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5345_, 0, v_a_5339_);
                    v___x_5344_ = v_reuseFailAlloc_5345_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5344_;
            }
            5 => {
                v___x_5352_ = l_Lean_trace_profiler;
                v___x_5353_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__21(v_opts_5316_, v___x_5352_);
                if v___x_5353_ == 0 {
                    v___y_5380_ = v___x_5353_;
                    state = 10;
                    continue;
                } else {
                    v___x_5416_ = l_Lean_trace_profiler_useHeartbeats;
                    v___x_5417_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__21(v_opts_5316_, v___x_5416_);
                    if v___x_5417_ == 0 {
                        v___x_5418_ = l_Lean_trace_profiler_threshold;
                        v___x_5419_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__4(v_opts_5316_, v___x_5418_);
                        v___x_5420_ = lean_float_of_nat(v___x_5419_);
                        v___x_5421_ = leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___closed__4_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___closed__4);
                        v___x_5422_ = lean_float_div(v___x_5420_, v___x_5421_);
                        v___y_5411_ = v___x_5422_;
                        state = 15;
                        continue;
                    } else {
                        v___x_5423_ = l_Lean_trace_profiler_threshold;
                        v___x_5424_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__4(v_opts_5316_, v___x_5423_);
                        v___x_5425_ = lean_float_of_nat(v___x_5424_);
                        v___y_5411_ = v___x_5425_;
                        state = 15;
                        continue;
                    }
                }
            }
            6 => {
                v_result_5357_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__1(v_fst_5328_);
                v___x_5358_ = l_Lean_TraceResult_toEmoji(v_result_5357_);
                v___x_5359_ = l_Lean_stringToMessageData(v___x_5358_);
                v___x_5360_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___closed__1_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___closed__1);
                if v_isShared_5351_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5350_, 7);
                    leanh::lean_ctor_set(v___x_5350_, 1, v___x_5360_);
                    leanh::lean_ctor_set(v___x_5350_, 0, v___x_5359_);
                    v___x_5362_ = v___x_5350_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5373_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5373_, 0, v___x_5359_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5373_, 1, v___x_5360_);
                    v___x_5362_ = v_reuseFailAlloc_5373_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_5332_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5331_, 7);
                    leanh::lean_ctor_set(v___x_5331_, 1, v_a_5356_);
                    leanh::lean_ctor_set(v___x_5331_, 0, v___x_5362_);
                    v_m_5364_ = v___x_5331_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5372_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5372_, 0, v___x_5362_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5372_, 1, v_a_5356_);
                    v_m_5364_ = v_reuseFailAlloc_5372_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_5365_ = leanh::lean_box((v_result_5357_) as usize);
                v___x_5366_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5366_, 0, v___x_5365_);
                v___x_5367_ = leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg___closed__0_once), _init_l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg___closed__0);
                leanh::lean_inc_ref(v_tag_5315_);
                leanh::lean_inc_ref(v___x_5366_);
                leanh::lean_inc(v_cls_5313_);
                v_data_5368_ = leanh::lean_alloc_ctor(0, 3, (17) as u32);
                leanh::lean_ctor_set(v_data_5368_, 0, v_cls_5313_);
                leanh::lean_ctor_set(v_data_5368_, 1, v___x_5366_);
                leanh::lean_ctor_set(v_data_5368_, 2, v_tag_5315_);
                leanh::lean_ctor_set_float(
                    v_data_5368_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_5367_,
                );
                leanh::lean_ctor_set_float(
                    v_data_5368_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_5367_,
                );
                leanh::lean_ctor_set_uint8(
                    v_data_5368_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16) as u32,
                    v_collapsed_5314_,
                );
                if v___x_5353_ == 0 {
                    leanh::lean_dec_ref_known(v___x_5366_, 1);
                    leanh::lean_dec(v_snd_5348_);
                    leanh::lean_dec(v_fst_5347_);
                    leanh::lean_dec_ref(v_tag_5315_);
                    leanh::lean_dec(v_cls_5313_);
                    v___y_5334_ = v___y_5355_;
                    v___y_5335_ = v_m_5364_;
                    v_data_5336_ = v_data_5368_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec_ref_known(v_data_5368_, 3);
                    v_data_5369_ = leanh::lean_alloc_ctor(0, 3, (17) as u32);
                    leanh::lean_ctor_set(v_data_5369_, 0, v_cls_5313_);
                    leanh::lean_ctor_set(v_data_5369_, 1, v___x_5366_);
                    leanh::lean_ctor_set(v_data_5369_, 2, v_tag_5315_);
                    v___x_5370_ = leanh::lean_unbox_float(v_fst_5347_);
                    leanh::lean_dec(v_fst_5347_);
                    leanh::lean_ctor_set_float(
                        v_data_5369_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        v___x_5370_,
                    );
                    v___x_5371_ = leanh::lean_unbox_float(v_snd_5348_);
                    leanh::lean_dec(v_snd_5348_);
                    leanh::lean_ctor_set_float(
                        v_data_5369_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                        v___x_5371_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_data_5369_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16) as u32,
                        v_collapsed_5314_,
                    );
                    v___y_5334_ = v___y_5355_;
                    v___y_5335_ = v_m_5364_;
                    v_data_5336_ = v_data_5369_;
                    state = 2;
                    continue;
                }
            }
            9 => {
                v_ref_5375_ = leanh::lean_ctor_get(v___y_5325_, 5);
                leanh::lean_inc(v___y_5326_);
                leanh::lean_inc_ref(v___y_5325_);
                leanh::lean_inc(v___y_5324_);
                leanh::lean_inc_ref(v___y_5323_);
                leanh::lean_inc(v___y_5322_);
                leanh::lean_inc_ref(v___y_5321_);
                leanh::lean_inc(v_fst_5328_);
                v___x_5376_ = leanh::lean_apply_8(
                    v_msg_5319_,
                    v_fst_5328_,
                    v___y_5321_,
                    v___y_5322_,
                    v___y_5323_,
                    v___y_5324_,
                    v___y_5325_,
                    v___y_5326_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_5376_) == 0 {
                    v_a_5377_ = leanh::lean_ctor_get(v___x_5376_, 0);
                    leanh::lean_inc(v_a_5377_);
                    leanh::lean_dec_ref_known(v___x_5376_, 1);
                    v___y_5355_ = v_ref_5375_;
                    v_a_5356_ = v_a_5377_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_dec_ref_known(v___x_5376_, 1);
                    v___x_5378_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___closed__3_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___closed__3);
                    v___y_5355_ = v_ref_5375_;
                    v_a_5356_ = v___x_5378_;
                    state = 6;
                    continue;
                }
            }
            10 => {
                if v_clsEnabled_5317_ == 0 {
                    if v___y_5380_ == 0 {
                        leanh::lean_del_object(v___x_5350_);
                        leanh::lean_dec(v_snd_5348_);
                        leanh::lean_dec(v_fst_5347_);
                        leanh::lean_del_object(v___x_5331_);
                        leanh::lean_dec_ref(v_msg_5319_);
                        leanh::lean_dec_ref(v_tag_5315_);
                        leanh::lean_dec(v_cls_5313_);
                        v___x_5381_ = lean_st_ref_take(v___y_5326_);
                        v_traceState_5382_ = leanh::lean_ctor_get(v___x_5381_, 4);
                        v_env_5383_ = leanh::lean_ctor_get(v___x_5381_, 0);
                        v_nextMacroScope_5384_ = leanh::lean_ctor_get(v___x_5381_, 1);
                        v_ngen_5385_ = leanh::lean_ctor_get(v___x_5381_, 2);
                        v_auxDeclNGen_5386_ = leanh::lean_ctor_get(v___x_5381_, 3);
                        v_cache_5387_ = leanh::lean_ctor_get(v___x_5381_, 5);
                        v_messages_5388_ = leanh::lean_ctor_get(v___x_5381_, 6);
                        v_infoState_5389_ = leanh::lean_ctor_get(v___x_5381_, 7);
                        v_snapshotTasks_5390_ = leanh::lean_ctor_get(v___x_5381_, 8);
                        v_isSharedCheck_5409_ =
                            (!leanh::lean_is_exclusive(v___x_5381_)) as u8;
                        if v_isSharedCheck_5409_ == 0 {
                            v___x_5392_ = v___x_5381_;
                            v_isShared_5393_ = v_isSharedCheck_5409_;
                            state = 11;
                            continue;
                        } else {
                            leanh::lean_inc(v_snapshotTasks_5390_);
                            leanh::lean_inc(v_infoState_5389_);
                            leanh::lean_inc(v_messages_5388_);
                            leanh::lean_inc(v_cache_5387_);
                            leanh::lean_inc(v_traceState_5382_);
                            leanh::lean_inc(v_auxDeclNGen_5386_);
                            leanh::lean_inc(v_ngen_5385_);
                            leanh::lean_inc(v_nextMacroScope_5384_);
                            leanh::lean_inc(v_env_5383_);
                            leanh::lean_dec(v___x_5381_);
                            v___x_5392_ = leanh::lean_box(0);
                            v_isShared_5393_ = v_isSharedCheck_5409_;
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
                v_tid_5394_ = leanh::lean_ctor_get_uint64(
                    v_traceState_5382_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_traces_5395_ = leanh::lean_ctor_get(v_traceState_5382_, 0);
                v_isSharedCheck_5408_ =
                    (!leanh::lean_is_exclusive(v_traceState_5382_)) as u8;
                if v_isSharedCheck_5408_ == 0 {
                    v___x_5397_ = v_traceState_5382_;
                    v_isShared_5398_ = v_isSharedCheck_5408_;
                    state = 12;
                    continue;
                } else {
                    leanh::lean_inc(v_traces_5395_);
                    leanh::lean_dec(v_traceState_5382_);
                    v___x_5397_ = leanh::lean_box(0);
                    v_isShared_5398_ = v_isSharedCheck_5408_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_5399_ =
                    l_Lean_PersistentArray_append___redArg(v_oldTraces_5318_, v_traces_5395_);
                leanh::lean_dec_ref(v_traces_5395_);
                if v_isShared_5398_ == 0 {
                    leanh::lean_ctor_set(v___x_5397_, 0, v___x_5399_);
                    v___x_5401_ = v___x_5397_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_5407_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5407_, 0, v___x_5399_);
                    leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_5407_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_tid_5394_,
                    );
                    v___x_5401_ = v_reuseFailAlloc_5407_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_5393_ == 0 {
                    leanh::lean_ctor_set(v___x_5392_, 4, v___x_5401_);
                    v___x_5403_ = v___x_5392_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5406_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5406_, 0, v_env_5383_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5406_, 1, v_nextMacroScope_5384_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5406_, 2, v_ngen_5385_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5406_, 3, v_auxDeclNGen_5386_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5406_, 4, v___x_5401_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5406_, 5, v_cache_5387_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5406_, 6, v_messages_5388_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5406_, 7, v_infoState_5389_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5406_, 8, v_snapshotTasks_5390_);
                    v___x_5403_ = v_reuseFailAlloc_5406_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_5404_ = lean_st_ref_set(v___y_5326_, v___x_5403_);
                v___x_5405_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__3___redArg(v_fst_5328_);
                return v___x_5405_;
            }
            15 => {
                v___x_5412_ = leanh::lean_unbox_float(v_snd_5348_);
                v___x_5413_ = leanh::lean_unbox_float(v_fst_5347_);
                v___x_5414_ = lean_float_sub(v___x_5412_, v___x_5413_);
                v___x_5415_ = lean_float_decLt(v___y_5411_, v___x_5414_);
                v___y_5380_ = v___x_5415_;
                state = 10;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___boxed(
    mut v_cls_5428_: *mut leanh::LeanObject,
    mut v_collapsed_5429_: *mut leanh::LeanObject,
    mut v_tag_5430_: *mut leanh::LeanObject,
    mut v_opts_5431_: *mut leanh::LeanObject,
    mut v_clsEnabled_5432_: *mut leanh::LeanObject,
    mut v_oldTraces_5433_: *mut leanh::LeanObject,
    mut v_msg_5434_: *mut leanh::LeanObject,
    mut v_resStartStop_5435_: *mut leanh::LeanObject,
    mut v___y_5436_: *mut leanh::LeanObject,
    mut v___y_5437_: *mut leanh::LeanObject,
    mut v___y_5438_: *mut leanh::LeanObject,
    mut v___y_5439_: *mut leanh::LeanObject,
    mut v___y_5440_: *mut leanh::LeanObject,
    mut v___y_5441_: *mut leanh::LeanObject,
    mut v___y_5442_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_collapsed_boxed_5443_: u8 = 0;
    let mut v_clsEnabled_boxed_5444_: u8 = 0;
    let mut v_res_5445_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_5443_ = (leanh::lean_unbox(v_collapsed_5429_) as u8);
    v_clsEnabled_boxed_5444_ = (leanh::lean_unbox(v_clsEnabled_5432_) as u8);
    v_res_5445_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1(v_cls_5428_, v_collapsed_boxed_5443_, v_tag_5430_, v_opts_5431_, v_clsEnabled_boxed_5444_, v_oldTraces_5433_, v_msg_5434_, v_resStartStop_5435_, v___y_5436_, v___y_5437_, v___y_5438_, v___y_5439_, v___y_5440_, v___y_5441_);
    leanh::lean_dec(v___y_5441_);
    leanh::lean_dec_ref(v___y_5440_);
    leanh::lean_dec(v___y_5439_);
    leanh::lean_dec_ref(v___y_5438_);
    leanh::lean_dec(v___y_5437_);
    leanh::lean_dec_ref(v___y_5436_);
    leanh::lean_dec_ref(v_opts_5431_);
    return v_res_5445_;
}
pub unsafe fn _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_5446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5448_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5446_ = leanh::lean_box(0);
    v___x_5447_ = leanh::lean_unsigned_to_nat(16);
    v___x_5448_ = lean_mk_array(v___x_5447_, v___x_5446_);
    return v___x_5448_;
}
pub unsafe fn _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_5449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5451_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5449_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___closed__0_once), _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___closed__0);
    v___x_5450_ = leanh::lean_unsigned_to_nat(0);
    v___x_5451_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5451_, 0, v___x_5450_);
    leanh::lean_ctor_set(v___x_5451_, 1, v___x_5449_);
    return v___x_5451_;
}
pub unsafe fn _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___closed__2()
-> f64 {
    let mut v___x_5452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5453_: f64 = 0.0;
    v___x_5452_ = leanh::lean_unsigned_to_nat(1000000000);
    v___x_5453_ = lean_float_of_nat(v___x_5452_);
    return v___x_5453_;
}
pub unsafe fn l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation(
    mut v_className_5454_: *mut leanh::LeanObject,
    mut v_type_5455_: *mut leanh::LeanObject,
    mut v_extraDeps_5456_: *mut leanh::LeanObject,
    mut v_a_5457_: *mut leanh::LeanObject,
    mut v_a_5458_: *mut leanh::LeanObject,
    mut v_a_5459_: *mut leanh::LeanObject,
    mut v_a_5460_: *mut leanh::LeanObject,
    mut v_a_5461_: *mut leanh::LeanObject,
    mut v_a_5462_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_options_5464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_5465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_5466_: u8 = 0;
    let mut v___x_5467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5476_: u8 = 0;
    let mut v___y_5478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5482_: f64 = 0.0;
    let mut v___x_5483_: f64 = 0.0;
    let mut v___x_5484_: f64 = 0.0;
    let mut v___x_5485_: f64 = 0.0;
    let mut v___x_5486_: f64 = 0.0;
    let mut v___x_5487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5497_: f64 = 0.0;
    let mut v___x_5498_: f64 = 0.0;
    let mut v___x_5499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5508_: u8 = 0;
    let mut v___x_5509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5514_: u8 = 0;
    let mut v___x_5516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5518_: u8 = 0;
    let mut v_a_5519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5522_: u8 = 0;
    let mut v___x_5524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5526_: u8 = 0;
    let mut v___x_5527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5532_: u8 = 0;
    let mut v___x_5534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5536_: u8 = 0;
    let mut v_a_5537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5540_: u8 = 0;
    let mut v___x_5542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5544_: u8 = 0;
    let mut v___x_5545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5546_: u8 = 0;
    let mut v___x_5547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_5464_ = leanh::lean_ctor_get(v_a_5461_, 2);
                v_inheritedTraceOptions_5465_ = leanh::lean_ctor_get(v_a_5461_, 13);
                v_hasTrace_5466_ = leanh::lean_ctor_get_uint8(
                    v_options_5464_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v___x_5467_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__2;
                v___x_5468_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___closed__1_once), _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___closed__1);
                v___x_5469_ = leanh::lean_box(0);
                leanh::lean_inc_ref(v_type_5455_);
                v___x_5470_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8___redArg(v___x_5468_, v_type_5455_, v___x_5469_);
                if v_hasTrace_5466_ == 0 {
                    v___x_5471_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go(v_className_5454_, v_extraDeps_5456_, v___x_5467_, v___x_5470_, v_type_5455_, v_a_5457_, v_a_5458_, v_a_5459_, v_a_5460_, v_a_5461_, v_a_5462_);
                    return v___x_5471_;
                } else {
                    leanh::lean_inc_ref(v_type_5455_);
                    leanh::lean_inc(v_className_5454_);
                    v___f_5472_ = leanh::lean_alloc_closure(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___boxed as *mut core::ffi::c_void, 10, 2);
                    leanh::lean_closure_set(v___f_5472_, 0, v_className_5454_);
                    leanh::lean_closure_set(v___f_5472_, 1, v_type_5455_);
                    v___x_5473_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__2;
                    v___x_5474_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build___closed__0;
                    v___x_5475_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3_once), _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3);
                    v___x_5476_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_5465_,
                        v_options_5464_,
                        v___x_5475_,
                    );
                    if v___x_5476_ == 0 {
                        v___x_5545_ = l_Lean_trace_profiler;
                        v___x_5546_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__21(v_options_5464_, v___x_5545_);
                        if v___x_5546_ == 0 {
                            leanh::lean_dec_ref(v___f_5472_);
                            v___x_5547_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go(v_className_5454_, v_extraDeps_5456_, v___x_5467_, v___x_5470_, v_type_5455_, v_a_5457_, v_a_5458_, v_a_5459_, v_a_5460_, v_a_5461_, v_a_5462_);
                            return v___x_5547_;
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
                v___x_5481_ = lean_io_mono_nanos_now();
                v___x_5482_ = lean_float_of_nat(v___y_5478_);
                v___x_5483_ = leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___closed__2_once), _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___closed__2);
                v___x_5484_ = lean_float_div(v___x_5482_, v___x_5483_);
                v___x_5485_ = lean_float_of_nat(v___x_5481_);
                v___x_5486_ = lean_float_div(v___x_5485_, v___x_5483_);
                v___x_5487_ = leanh::lean_box_float(v___x_5484_);
                v___x_5488_ = leanh::lean_box_float(v___x_5486_);
                v___x_5489_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5489_, 0, v___x_5487_);
                leanh::lean_ctor_set(v___x_5489_, 1, v___x_5488_);
                v___x_5490_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5490_, 0, v_a_5480_);
                leanh::lean_ctor_set(v___x_5490_, 1, v___x_5489_);
                v___x_5491_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1(v___x_5473_, v_hasTrace_5466_, v___x_5474_, v_options_5464_, v___x_5476_, v___y_5479_, v___f_5472_, v___x_5490_, v_a_5457_, v_a_5458_, v_a_5459_, v_a_5460_, v_a_5461_, v_a_5462_);
                return v___x_5491_;
            }
            2 => {
                v___x_5496_ = lean_io_get_num_heartbeats();
                v___x_5497_ = lean_float_of_nat(v___y_5493_);
                v___x_5498_ = lean_float_of_nat(v___x_5496_);
                v___x_5499_ = leanh::lean_box_float(v___x_5497_);
                v___x_5500_ = leanh::lean_box_float(v___x_5498_);
                v___x_5501_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5501_, 0, v___x_5499_);
                leanh::lean_ctor_set(v___x_5501_, 1, v___x_5500_);
                v___x_5502_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5502_, 0, v_a_5495_);
                leanh::lean_ctor_set(v___x_5502_, 1, v___x_5501_);
                v___x_5503_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1(v___x_5473_, v_hasTrace_5466_, v___x_5474_, v_options_5464_, v___x_5476_, v___y_5494_, v___f_5472_, v___x_5502_, v_a_5457_, v_a_5458_, v_a_5459_, v_a_5460_, v_a_5461_, v_a_5462_);
                return v___x_5503_;
            }
            3 => {
                v___x_5505_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___redArg(v_a_5462_);
                v_a_5506_ = leanh::lean_ctor_get(v___x_5505_, 0);
                leanh::lean_inc(v_a_5506_);
                leanh::lean_dec_ref(v___x_5505_);
                v___x_5507_ = l_Lean_trace_profiler_useHeartbeats;
                v___x_5508_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__21(v_options_5464_, v___x_5507_);
                if v___x_5508_ == 0 {
                    v___x_5509_ = lean_io_mono_nanos_now();
                    v___x_5510_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go(v_className_5454_, v_extraDeps_5456_, v___x_5467_, v___x_5470_, v_type_5455_, v_a_5457_, v_a_5458_, v_a_5459_, v_a_5460_, v_a_5461_, v_a_5462_);
                    if leanh::lean_obj_tag(v___x_5510_) == 0 {
                        v_a_5511_ = leanh::lean_ctor_get(v___x_5510_, 0);
                        v_isSharedCheck_5518_ =
                            (!leanh::lean_is_exclusive(v___x_5510_)) as u8;
                        if v_isSharedCheck_5518_ == 0 {
                            v___x_5513_ = v___x_5510_;
                            v_isShared_5514_ = v_isSharedCheck_5518_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5511_);
                            leanh::lean_dec(v___x_5510_);
                            v___x_5513_ = leanh::lean_box(0);
                            v_isShared_5514_ = v_isSharedCheck_5518_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v_a_5519_ = leanh::lean_ctor_get(v___x_5510_, 0);
                        v_isSharedCheck_5526_ =
                            (!leanh::lean_is_exclusive(v___x_5510_)) as u8;
                        if v_isSharedCheck_5526_ == 0 {
                            v___x_5521_ = v___x_5510_;
                            v_isShared_5522_ = v_isSharedCheck_5526_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5519_);
                            leanh::lean_dec(v___x_5510_);
                            v___x_5521_ = leanh::lean_box(0);
                            v_isShared_5522_ = v_isSharedCheck_5526_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    v___x_5527_ = lean_io_get_num_heartbeats();
                    v___x_5528_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go(v_className_5454_, v_extraDeps_5456_, v___x_5467_, v___x_5470_, v_type_5455_, v_a_5457_, v_a_5458_, v_a_5459_, v_a_5460_, v_a_5461_, v_a_5462_);
                    if leanh::lean_obj_tag(v___x_5528_) == 0 {
                        v_a_5529_ = leanh::lean_ctor_get(v___x_5528_, 0);
                        v_isSharedCheck_5536_ =
                            (!leanh::lean_is_exclusive(v___x_5528_)) as u8;
                        if v_isSharedCheck_5536_ == 0 {
                            v___x_5531_ = v___x_5528_;
                            v_isShared_5532_ = v_isSharedCheck_5536_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5529_);
                            leanh::lean_dec(v___x_5528_);
                            v___x_5531_ = leanh::lean_box(0);
                            v_isShared_5532_ = v_isSharedCheck_5536_;
                            state = 8;
                            continue;
                        }
                    } else {
                        v_a_5537_ = leanh::lean_ctor_get(v___x_5528_, 0);
                        v_isSharedCheck_5544_ =
                            (!leanh::lean_is_exclusive(v___x_5528_)) as u8;
                        if v_isSharedCheck_5544_ == 0 {
                            v___x_5539_ = v___x_5528_;
                            v_isShared_5540_ = v_isSharedCheck_5544_;
                            state = 10;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5537_);
                            leanh::lean_dec(v___x_5528_);
                            v___x_5539_ = leanh::lean_box(0);
                            v_isShared_5540_ = v_isSharedCheck_5544_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            4 => {
                if v_isShared_5514_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5513_, 1);
                    v___x_5516_ = v___x_5513_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5517_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5517_, 0, v_a_5511_);
                    v___x_5516_ = v_reuseFailAlloc_5517_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___y_5478_ = v___x_5509_;
                v___y_5479_ = v_a_5506_;
                v_a_5480_ = v___x_5516_;
                state = 1;
                continue;
            }
            6 => {
                if v_isShared_5522_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5521_, 0);
                    v___x_5524_ = v___x_5521_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5525_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5525_, 0, v_a_5519_);
                    v___x_5524_ = v_reuseFailAlloc_5525_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_5478_ = v___x_5509_;
                v___y_5479_ = v_a_5506_;
                v_a_5480_ = v___x_5524_;
                state = 1;
                continue;
            }
            8 => {
                if v_isShared_5532_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5531_, 1);
                    v___x_5534_ = v___x_5531_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5535_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5535_, 0, v_a_5529_);
                    v___x_5534_ = v_reuseFailAlloc_5535_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___y_5493_ = v___x_5527_;
                v___y_5494_ = v_a_5506_;
                v_a_5495_ = v___x_5534_;
                state = 2;
                continue;
            }
            10 => {
                if v_isShared_5540_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5539_, 0);
                    v___x_5542_ = v___x_5539_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5543_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5543_, 0, v_a_5537_);
                    v___x_5542_ = v_reuseFailAlloc_5543_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___y_5493_ = v___x_5527_;
                v___y_5494_ = v_a_5506_;
                v_a_5495_ = v___x_5542_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___boxed(
    mut v_className_5548_: *mut leanh::LeanObject,
    mut v_type_5549_: *mut leanh::LeanObject,
    mut v_extraDeps_5550_: *mut leanh::LeanObject,
    mut v_a_5551_: *mut leanh::LeanObject,
    mut v_a_5552_: *mut leanh::LeanObject,
    mut v_a_5553_: *mut leanh::LeanObject,
    mut v_a_5554_: *mut leanh::LeanObject,
    mut v_a_5555_: *mut leanh::LeanObject,
    mut v_a_5556_: *mut leanh::LeanObject,
    mut v_a_5557_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5558_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5558_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation(
        v_className_5548_,
        v_type_5549_,
        v_extraDeps_5550_,
        v_a_5551_,
        v_a_5552_,
        v_a_5553_,
        v_a_5554_,
        v_a_5555_,
        v_a_5556_,
    );
    leanh::lean_dec(v_a_5556_);
    leanh::lean_dec_ref(v_a_5555_);
    leanh::lean_dec(v_a_5554_);
    leanh::lean_dec_ref(v_a_5553_);
    leanh::lean_dec(v_a_5552_);
    leanh::lean_dec_ref(v_a_5551_);
    return v_res_5558_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__3(
    mut v_00_u03b1_5559_: *mut leanh::LeanObject,
    mut v_x_5560_: *mut leanh::LeanObject,
    mut v___y_5561_: *mut leanh::LeanObject,
    mut v___y_5562_: *mut leanh::LeanObject,
    mut v___y_5563_: *mut leanh::LeanObject,
    mut v___y_5564_: *mut leanh::LeanObject,
    mut v___y_5565_: *mut leanh::LeanObject,
    mut v___y_5566_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5568_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5568_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__3___redArg(v_x_5560_);
    return v___x_5568_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__3___boxed(
    mut v_00_u03b1_5569_: *mut leanh::LeanObject,
    mut v_x_5570_: *mut leanh::LeanObject,
    mut v___y_5571_: *mut leanh::LeanObject,
    mut v___y_5572_: *mut leanh::LeanObject,
    mut v___y_5573_: *mut leanh::LeanObject,
    mut v___y_5574_: *mut leanh::LeanObject,
    mut v___y_5575_: *mut leanh::LeanObject,
    mut v___y_5576_: *mut leanh::LeanObject,
    mut v___y_5577_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5578_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5578_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__3(v_00_u03b1_5569_, v_x_5570_, v___y_5571_, v___y_5572_, v___y_5573_, v___y_5574_, v___y_5575_, v___y_5576_);
    leanh::lean_dec(v___y_5576_);
    leanh::lean_dec_ref(v___y_5575_);
    leanh::lean_dec(v___y_5574_);
    leanh::lean_dec_ref(v___y_5573_);
    leanh::lean_dec(v___y_5572_);
    leanh::lean_dec_ref(v___y_5571_);
    return v_res_5578_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__2(
    mut v_oldTraces_5579_: *mut leanh::LeanObject,
    mut v_data_5580_: *mut leanh::LeanObject,
    mut v_ref_5581_: *mut leanh::LeanObject,
    mut v_msg_5582_: *mut leanh::LeanObject,
    mut v___y_5583_: *mut leanh::LeanObject,
    mut v___y_5584_: *mut leanh::LeanObject,
    mut v___y_5585_: *mut leanh::LeanObject,
    mut v___y_5586_: *mut leanh::LeanObject,
    mut v___y_5587_: *mut leanh::LeanObject,
    mut v___y_5588_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5590_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5590_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__2___redArg(v_oldTraces_5579_, v_data_5580_, v_ref_5581_, v_msg_5582_, v___y_5585_, v___y_5586_, v___y_5587_, v___y_5588_);
    return v___x_5590_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__2___boxed(
    mut v_oldTraces_5591_: *mut leanh::LeanObject,
    mut v_data_5592_: *mut leanh::LeanObject,
    mut v_ref_5593_: *mut leanh::LeanObject,
    mut v_msg_5594_: *mut leanh::LeanObject,
    mut v___y_5595_: *mut leanh::LeanObject,
    mut v___y_5596_: *mut leanh::LeanObject,
    mut v___y_5597_: *mut leanh::LeanObject,
    mut v___y_5598_: *mut leanh::LeanObject,
    mut v___y_5599_: *mut leanh::LeanObject,
    mut v___y_5600_: *mut leanh::LeanObject,
    mut v___y_5601_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5602_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5602_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__2(v_oldTraces_5591_, v_data_5592_, v_ref_5593_, v_msg_5594_, v___y_5595_, v___y_5596_, v___y_5597_, v___y_5598_, v___y_5599_, v___y_5600_);
    leanh::lean_dec(v___y_5600_);
    leanh::lean_dec_ref(v___y_5599_);
    leanh::lean_dec(v___y_5598_);
    leanh::lean_dec_ref(v___y_5597_);
    leanh::lean_dec(v___y_5596_);
    leanh::lean_dec_ref(v___y_5595_);
    return v_res_5602_;
}
pub unsafe fn _init_l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_5603_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5603_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_5603_;
}
pub unsafe fn _init_l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_5604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5605_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5604_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__0_once), _init_l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__0);
    v___x_5605_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_5605_, 0, v___x_5604_);
    return v___x_5605_;
}
pub unsafe fn _init_l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_5606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5607_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5606_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__1_once), _init_l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__1);
    v___x_5607_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5607_, 0, v___x_5606_);
    leanh::lean_ctor_set(v___x_5607_, 1, v___x_5606_);
    return v___x_5607_;
}
pub unsafe fn _init_l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_5608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5609_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5608_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__1_once), _init_l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__1);
    v___x_5609_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
    leanh::lean_ctor_set(v___x_5609_, 0, v___x_5608_);
    leanh::lean_ctor_set(v___x_5609_, 1, v___x_5608_);
    leanh::lean_ctor_set(v___x_5609_, 2, v___x_5608_);
    leanh::lean_ctor_set(v___x_5609_, 3, v___x_5608_);
    leanh::lean_ctor_set(v___x_5609_, 4, v___x_5608_);
    leanh::lean_ctor_set(v___x_5609_, 5, v___x_5608_);
    return v___x_5609_;
}
pub unsafe fn l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg(
    mut v_env_5610_: *mut leanh::LeanObject,
    mut v___y_5611_: *mut leanh::LeanObject,
    mut v___y_5612_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5624_: u8 = 0;
    let mut v___x_5625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_5630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_5632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5636_: u8 = 0;
    let mut v___x_5637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5644_: u8 = 0;
    let mut v_unused_5645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5647_: u8 = 0;
    let mut v_unused_5648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5614_ = lean_st_ref_take(v___y_5612_);
                v_nextMacroScope_5615_ = leanh::lean_ctor_get(v___x_5614_, 1);
                v_ngen_5616_ = leanh::lean_ctor_get(v___x_5614_, 2);
                v_auxDeclNGen_5617_ = leanh::lean_ctor_get(v___x_5614_, 3);
                v_traceState_5618_ = leanh::lean_ctor_get(v___x_5614_, 4);
                v_messages_5619_ = leanh::lean_ctor_get(v___x_5614_, 6);
                v_infoState_5620_ = leanh::lean_ctor_get(v___x_5614_, 7);
                v_snapshotTasks_5621_ = leanh::lean_ctor_get(v___x_5614_, 8);
                v_isSharedCheck_5647_ = (!leanh::lean_is_exclusive(v___x_5614_)) as u8;
                if v_isSharedCheck_5647_ == 0 {
                    v_unused_5648_ = leanh::lean_ctor_get(v___x_5614_, 5);
                    leanh::lean_dec(v_unused_5648_);
                    v_unused_5649_ = leanh::lean_ctor_get(v___x_5614_, 0);
                    leanh::lean_dec(v_unused_5649_);
                    v___x_5623_ = v___x_5614_;
                    v_isShared_5624_ = v_isSharedCheck_5647_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_5621_);
                    leanh::lean_inc(v_infoState_5620_);
                    leanh::lean_inc(v_messages_5619_);
                    leanh::lean_inc(v_traceState_5618_);
                    leanh::lean_inc(v_auxDeclNGen_5617_);
                    leanh::lean_inc(v_ngen_5616_);
                    leanh::lean_inc(v_nextMacroScope_5615_);
                    leanh::lean_dec(v___x_5614_);
                    v___x_5623_ = leanh::lean_box(0);
                    v_isShared_5624_ = v_isSharedCheck_5647_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5625_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__2_once), _init_l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__2);
                if v_isShared_5624_ == 0 {
                    leanh::lean_ctor_set(v___x_5623_, 5, v___x_5625_);
                    leanh::lean_ctor_set(v___x_5623_, 0, v_env_5610_);
                    v___x_5627_ = v___x_5623_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5646_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5646_, 0, v_env_5610_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5646_, 1, v_nextMacroScope_5615_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5646_, 2, v_ngen_5616_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5646_, 3, v_auxDeclNGen_5617_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5646_, 4, v_traceState_5618_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5646_, 5, v___x_5625_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5646_, 6, v_messages_5619_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5646_, 7, v_infoState_5620_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5646_, 8, v_snapshotTasks_5621_);
                    v___x_5627_ = v_reuseFailAlloc_5646_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5628_ = lean_st_ref_set(v___y_5612_, v___x_5627_);
                v___x_5629_ = lean_st_ref_take(v___y_5611_);
                v_mctx_5630_ = leanh::lean_ctor_get(v___x_5629_, 0);
                v_zetaDeltaFVarIds_5631_ = leanh::lean_ctor_get(v___x_5629_, 2);
                v_postponed_5632_ = leanh::lean_ctor_get(v___x_5629_, 3);
                v_diag_5633_ = leanh::lean_ctor_get(v___x_5629_, 4);
                v_isSharedCheck_5644_ = (!leanh::lean_is_exclusive(v___x_5629_)) as u8;
                if v_isSharedCheck_5644_ == 0 {
                    v_unused_5645_ = leanh::lean_ctor_get(v___x_5629_, 1);
                    leanh::lean_dec(v_unused_5645_);
                    v___x_5635_ = v___x_5629_;
                    v_isShared_5636_ = v_isSharedCheck_5644_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_5633_);
                    leanh::lean_inc(v_postponed_5632_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_5631_);
                    leanh::lean_inc(v_mctx_5630_);
                    leanh::lean_dec(v___x_5629_);
                    v___x_5635_ = leanh::lean_box(0);
                    v_isShared_5636_ = v_isSharedCheck_5644_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5637_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__3_once), _init_l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__3);
                if v_isShared_5636_ == 0 {
                    leanh::lean_ctor_set(v___x_5635_, 1, v___x_5637_);
                    v___x_5639_ = v___x_5635_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5643_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5643_, 0, v_mctx_5630_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5643_, 1, v___x_5637_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_5643_,
                        2,
                        v_zetaDeltaFVarIds_5631_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_5643_, 3, v_postponed_5632_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5643_, 4, v_diag_5633_);
                    v___x_5639_ = v_reuseFailAlloc_5643_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5640_ = lean_st_ref_set(v___y_5611_, v___x_5639_);
                v___x_5641_ = leanh::lean_box(0);
                v___x_5642_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5642_, 0, v___x_5641_);
                return v___x_5642_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___boxed(
    mut v_env_5650_: *mut leanh::LeanObject,
    mut v___y_5651_: *mut leanh::LeanObject,
    mut v___y_5652_: *mut leanh::LeanObject,
    mut v___y_5653_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5654_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5654_ = l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg(
        v_env_5650_,
        v___y_5651_,
        v___y_5652_,
    );
    leanh::lean_dec(v___y_5652_);
    leanh::lean_dec(v___y_5651_);
    return v_res_5654_;
}
pub unsafe fn l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0(
    mut v_env_5655_: *mut leanh::LeanObject,
    mut v___y_5656_: *mut leanh::LeanObject,
    mut v___y_5657_: *mut leanh::LeanObject,
    mut v___y_5658_: *mut leanh::LeanObject,
    mut v___y_5659_: *mut leanh::LeanObject,
    mut v___y_5660_: *mut leanh::LeanObject,
    mut v___y_5661_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5663_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5663_ = l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg(
        v_env_5655_,
        v___y_5659_,
        v___y_5661_,
    );
    return v___x_5663_;
}
pub unsafe fn l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___boxed(
    mut v_env_5664_: *mut leanh::LeanObject,
    mut v___y_5665_: *mut leanh::LeanObject,
    mut v___y_5666_: *mut leanh::LeanObject,
    mut v___y_5667_: *mut leanh::LeanObject,
    mut v___y_5668_: *mut leanh::LeanObject,
    mut v___y_5669_: *mut leanh::LeanObject,
    mut v___y_5670_: *mut leanh::LeanObject,
    mut v___y_5671_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5672_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5672_ = l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0(
        v_env_5664_,
        v___y_5665_,
        v___y_5666_,
        v___y_5667_,
        v___y_5668_,
        v___y_5669_,
        v___y_5670_,
    );
    leanh::lean_dec(v___y_5670_);
    leanh::lean_dec_ref(v___y_5669_);
    leanh::lean_dec(v___y_5668_);
    leanh::lean_dec_ref(v___y_5667_);
    leanh::lean_dec(v___y_5666_);
    leanh::lean_dec_ref(v___y_5665_);
    return v_res_5672_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___lam__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_5674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5675_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5674_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___lam__0___closed__0;
    v___x_5675_ = l_Lean_stringToMessageData(v___x_5674_);
    return v___x_5675_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___lam__0(
    mut v_mkCmd_5676_: *mut leanh::LeanObject,
    mut v_a_5677_: *mut leanh::LeanObject,
    mut v___x_5678_: *mut leanh::LeanObject,
    mut v___y_5679_: *mut leanh::LeanObject,
    mut v___y_5680_: *mut leanh::LeanObject,
    mut v___y_5681_: *mut leanh::LeanObject,
    mut v___y_5682_: *mut leanh::LeanObject,
    mut v___y_5683_: *mut leanh::LeanObject,
    mut v___y_5684_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5699_: u8 = 0;
    let mut v___x_5701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5703_: u8 = 0;
    let mut v_unused_5704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5708_: u8 = 0;
    let mut v___x_5710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5712_: u8 = 0;
    let mut v___y_5714_: u8 = 0;
    let mut v_options_5715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_5716_: u8 = 0;
    let mut v_inheritedTraceOptions_5717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5720_: u8 = 0;
    let mut v___x_5721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5732_: u8 = 0;
    let mut v___x_5734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5736_: u8 = 0;
    let mut v___x_5737_: u8 = 0;
    let mut v___x_5738_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___y_5682_);
                leanh::lean_inc_ref(v___y_5681_);
                leanh::lean_inc(v___y_5680_);
                leanh::lean_inc_ref(v___y_5679_);
                leanh::lean_inc_ref(v_a_5677_);
                v___x_5686_ = leanh::lean_apply_5(
                    v_mkCmd_5676_,
                    v_a_5677_,
                    v___y_5679_,
                    v___y_5680_,
                    v___y_5681_,
                    v___y_5682_,
                );
                v___x_5687_ =
                    l_Lean_Core_withFreshMacroScope___redArg(v___x_5686_, v___y_5683_, v___y_5684_);
                if leanh::lean_obj_tag(v___x_5687_) == 0 {
                    leanh::lean_dec_ref(v___y_5679_);
                    leanh::lean_dec_ref(v___x_5678_);
                    leanh::lean_dec_ref(v_a_5677_);
                    return v___x_5687_;
                } else {
                    v_a_5688_ = leanh::lean_ctor_get(v___x_5687_, 0);
                    leanh::lean_inc(v_a_5688_);
                    v___x_5737_ = l_Lean_Exception_isInterrupt(v_a_5688_);
                    if v___x_5737_ == 0 {
                        leanh::lean_inc(v_a_5688_);
                        v___x_5738_ = l_Lean_Exception_isRuntime(v_a_5688_);
                        v___y_5714_ = v___x_5738_;
                        state = 6;
                        continue;
                    } else {
                        v___y_5714_ = v___x_5737_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_dec_ref(v___y_5690_);
                v___x_5696_ =
                    l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg(
                        v___x_5678_,
                        v___y_5693_,
                        v___y_5695_,
                    );
                if leanh::lean_obj_tag(v___x_5696_) == 0 {
                    v_isSharedCheck_5703_ = (!leanh::lean_is_exclusive(v___x_5696_)) as u8;
                    if v_isSharedCheck_5703_ == 0 {
                        v_unused_5704_ = leanh::lean_ctor_get(v___x_5696_, 0);
                        leanh::lean_dec(v_unused_5704_);
                        v___x_5698_ = v___x_5696_;
                        v_isShared_5699_ = v_isSharedCheck_5703_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_5696_);
                        v___x_5698_ = leanh::lean_box(0);
                        v_isShared_5699_ = v_isSharedCheck_5703_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_5688_);
                    v_a_5705_ = leanh::lean_ctor_get(v___x_5696_, 0);
                    v_isSharedCheck_5712_ = (!leanh::lean_is_exclusive(v___x_5696_)) as u8;
                    if v_isSharedCheck_5712_ == 0 {
                        v___x_5707_ = v___x_5696_;
                        v_isShared_5708_ = v_isSharedCheck_5712_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5705_);
                        leanh::lean_dec(v___x_5696_);
                        v___x_5707_ = leanh::lean_box(0);
                        v_isShared_5708_ = v_isSharedCheck_5712_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_5699_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5698_, 1);
                    leanh::lean_ctor_set(v___x_5698_, 0, v_a_5688_);
                    v___x_5701_ = v___x_5698_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5702_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5702_, 0, v_a_5688_);
                    v___x_5701_ = v_reuseFailAlloc_5702_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5701_;
            }
            4 => {
                if v_isShared_5708_ == 0 {
                    v___x_5710_ = v___x_5707_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5711_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5711_, 0, v_a_5705_);
                    v___x_5710_ = v_reuseFailAlloc_5711_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5710_;
            }
            6 => {
                if v___y_5714_ == 0 {
                    leanh::lean_dec_ref_known(v___x_5687_, 1);
                    v_options_5715_ = leanh::lean_ctor_get(v___y_5683_, 2);
                    v_hasTrace_5716_ = leanh::lean_ctor_get_uint8(
                        v_options_5715_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_5716_ == 0 {
                        leanh::lean_dec_ref(v_a_5677_);
                        v___y_5690_ = v___y_5679_;
                        v___y_5691_ = v___y_5680_;
                        v___y_5692_ = v___y_5681_;
                        v___y_5693_ = v___y_5682_;
                        v___y_5694_ = v___y_5683_;
                        v___y_5695_ = v___y_5684_;
                        state = 1;
                        continue;
                    } else {
                        v_inheritedTraceOptions_5717_ =
                            leanh::lean_ctor_get(v___y_5683_, 13);
                        v___x_5718_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__2;
                        v___x_5719_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3_once), _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3);
                        v___x_5720_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_5717_,
                            v_options_5715_,
                            v___x_5719_,
                        );
                        if v___x_5720_ == 0 {
                            leanh::lean_dec_ref(v_a_5677_);
                            v___y_5690_ = v___y_5679_;
                            v___y_5691_ = v___y_5680_;
                            v___y_5692_ = v___y_5681_;
                            v___y_5693_ = v___y_5682_;
                            v___y_5694_ = v___y_5683_;
                            v___y_5695_ = v___y_5684_;
                            state = 1;
                            continue;
                        } else {
                            v___x_5721_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___lam__0___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___lam__0___closed__1);
                            v___x_5722_ = l_Lean_MessageData_ofExpr(v_a_5677_);
                            v___x_5723_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_5723_, 0, v___x_5721_);
                            leanh::lean_ctor_set(v___x_5723_, 1, v___x_5722_);
                            v___x_5724_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__3_once), _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__3);
                            v___x_5725_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_5725_, 0, v___x_5723_);
                            leanh::lean_ctor_set(v___x_5725_, 1, v___x_5724_);
                            leanh::lean_inc(v_a_5688_);
                            v___x_5726_ = l_Lean_Exception_toMessageData(v_a_5688_);
                            v___x_5727_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_5727_, 0, v___x_5725_);
                            leanh::lean_ctor_set(v___x_5727_, 1, v___x_5726_);
                            v___x_5728_ = l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg(v___x_5718_, v___x_5727_, v___y_5681_, v___y_5682_, v___y_5683_, v___y_5684_);
                            if leanh::lean_obj_tag(v___x_5728_) == 0 {
                                leanh::lean_dec_ref_known(v___x_5728_, 1);
                                v___y_5690_ = v___y_5679_;
                                v___y_5691_ = v___y_5680_;
                                v___y_5692_ = v___y_5681_;
                                v___y_5693_ = v___y_5682_;
                                v___y_5694_ = v___y_5683_;
                                v___y_5695_ = v___y_5684_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec(v_a_5688_);
                                leanh::lean_dec_ref(v___y_5679_);
                                leanh::lean_dec_ref(v___x_5678_);
                                v_a_5729_ = leanh::lean_ctor_get(v___x_5728_, 0);
                                v_isSharedCheck_5736_ =
                                    (!leanh::lean_is_exclusive(v___x_5728_)) as u8;
                                if v_isSharedCheck_5736_ == 0 {
                                    v___x_5731_ = v___x_5728_;
                                    v_isShared_5732_ = v_isSharedCheck_5736_;
                                    state = 7;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_5729_);
                                    leanh::lean_dec(v___x_5728_);
                                    v___x_5731_ = leanh::lean_box(0);
                                    v_isShared_5732_ = v_isSharedCheck_5736_;
                                    state = 7;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_5688_);
                    leanh::lean_dec_ref(v___y_5679_);
                    leanh::lean_dec_ref(v___x_5678_);
                    leanh::lean_dec_ref(v_a_5677_);
                    return v___x_5687_;
                }
            }
            7 => {
                if v_isShared_5732_ == 0 {
                    v___x_5734_ = v___x_5731_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5735_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5735_, 0, v_a_5729_);
                    v___x_5734_ = v_reuseFailAlloc_5735_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5734_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___lam__0___boxed(
    mut v_mkCmd_5739_: *mut leanh::LeanObject,
    mut v_a_5740_: *mut leanh::LeanObject,
    mut v___x_5741_: *mut leanh::LeanObject,
    mut v___y_5742_: *mut leanh::LeanObject,
    mut v___y_5743_: *mut leanh::LeanObject,
    mut v___y_5744_: *mut leanh::LeanObject,
    mut v___y_5745_: *mut leanh::LeanObject,
    mut v___y_5746_: *mut leanh::LeanObject,
    mut v___y_5747_: *mut leanh::LeanObject,
    mut v___y_5748_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5749_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5749_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___lam__0(v_mkCmd_5739_, v_a_5740_, v___x_5741_, v___y_5742_, v___y_5743_, v___y_5744_, v___y_5745_, v___y_5746_, v___y_5747_);
    leanh::lean_dec(v___y_5747_);
    leanh::lean_dec_ref(v___y_5746_);
    leanh::lean_dec(v___y_5745_);
    leanh::lean_dec_ref(v___y_5744_);
    leanh::lean_dec(v___y_5743_);
    return v_res_5749_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_5750_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5750_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_5750_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_5751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5752_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5751_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__0);
    v___x_5752_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_5752_, 0, v___x_5751_);
    return v___x_5752_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_5753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5755_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5753_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__1);
    v___x_5754_ = leanh::lean_unsigned_to_nat(0);
    v___x_5755_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_5755_, 0, v___x_5754_);
    leanh::lean_ctor_set(v___x_5755_, 1, v___x_5754_);
    leanh::lean_ctor_set(v___x_5755_, 2, v___x_5754_);
    leanh::lean_ctor_set(v___x_5755_, 3, v___x_5754_);
    leanh::lean_ctor_set(v___x_5755_, 4, v___x_5753_);
    leanh::lean_ctor_set(v___x_5755_, 5, v___x_5753_);
    leanh::lean_ctor_set(v___x_5755_, 6, v___x_5753_);
    leanh::lean_ctor_set(v___x_5755_, 7, v___x_5753_);
    leanh::lean_ctor_set(v___x_5755_, 8, v___x_5753_);
    leanh::lean_ctor_set(v___x_5755_, 9, v___x_5753_);
    return v___x_5755_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_5756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5758_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5756_ = leanh::lean_unsigned_to_nat(32);
    v___x_5757_ = lean_mk_empty_array_with_capacity(v___x_5756_);
    v___x_5758_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_5758_, 0, v___x_5757_);
    return v___x_5758_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_5759_: usize = 0;
    let mut v___x_5760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5764_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5759_ = 5usize;
    v___x_5760_ = leanh::lean_unsigned_to_nat(0);
    v___x_5761_ = leanh::lean_unsigned_to_nat(32);
    v___x_5762_ = lean_mk_empty_array_with_capacity(v___x_5761_);
    v___x_5763_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__3);
    v___x_5764_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_5764_, 0, v___x_5763_);
    leanh::lean_ctor_set(v___x_5764_, 1, v___x_5762_);
    leanh::lean_ctor_set(v___x_5764_, 2, v___x_5760_);
    leanh::lean_ctor_set(v___x_5764_, 3, v___x_5760_);
    leanh::lean_ctor_set_usize(v___x_5764_, 4, v___x_5759_);
    return v___x_5764_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_5765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5768_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5765_ = leanh::lean_box(1);
    v___x_5766_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__4);
    v___x_5767_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__1);
    v___x_5768_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_5768_, 0, v___x_5767_);
    leanh::lean_ctor_set(v___x_5768_, 1, v___x_5766_);
    leanh::lean_ctor_set(v___x_5768_, 2, v___x_5765_);
    return v___x_5768_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg(
    mut v_msgData_5769_: *mut leanh::LeanObject,
    mut v___y_5770_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_5775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_5778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5783_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5772_ = lean_st_ref_get(v___y_5770_);
    v_env_5773_ = leanh::lean_ctor_get(v___x_5772_, 0);
    leanh::lean_inc_ref(v_env_5773_);
    leanh::lean_dec(v___x_5772_);
    v___x_5774_ = lean_st_ref_get(v___y_5770_);
    v_scopes_5775_ = leanh::lean_ctor_get(v___x_5774_, 2);
    leanh::lean_inc(v_scopes_5775_);
    leanh::lean_dec(v___x_5774_);
    v___x_5776_ = l_Lean_Elab_Command_instInhabitedScope_default;
    v___x_5777_ = l_List_head_x21___redArg(v___x_5776_, v_scopes_5775_);
    leanh::lean_dec(v_scopes_5775_);
    v_opts_5778_ = leanh::lean_ctor_get(v___x_5777_, 1);
    leanh::lean_inc_ref(v_opts_5778_);
    leanh::lean_dec(v___x_5777_);
    v___x_5779_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__2);
    v___x_5780_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__5);
    v___x_5781_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_5781_, 0, v_env_5773_);
    leanh::lean_ctor_set(v___x_5781_, 1, v___x_5779_);
    leanh::lean_ctor_set(v___x_5781_, 2, v___x_5780_);
    leanh::lean_ctor_set(v___x_5781_, 3, v_opts_5778_);
    v___x_5782_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5782_, 0, v___x_5781_);
    leanh::lean_ctor_set(v___x_5782_, 1, v_msgData_5769_);
    v___x_5783_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_5783_, 0, v___x_5782_);
    return v___x_5783_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___boxed(
    mut v_msgData_5784_: *mut leanh::LeanObject,
    mut v___y_5785_: *mut leanh::LeanObject,
    mut v___y_5786_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5787_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5787_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg(v_msgData_5784_, v___y_5785_);
    leanh::lean_dec(v___y_5785_);
    return v_res_5787_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1(
    mut v_cls_5788_: *mut leanh::LeanObject,
    mut v_msg_5789_: *mut leanh::LeanObject,
    mut v___y_5790_: *mut leanh::LeanObject,
    mut v___y_5791_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5799_: u8 = 0;
    let mut v___x_5800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_5804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_5805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_5807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5814_: u8 = 0;
    let mut v_tid_5815_: u64 = 0;
    let mut v_traces_5816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5819_: u8 = 0;
    let mut v___x_5820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5821_: f64 = 0.0;
    let mut v___x_5822_: u8 = 0;
    let mut v___x_5823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5840_: u8 = 0;
    let mut v_isSharedCheck_5841_: u8 = 0;
    let mut v_isSharedCheck_5842_: u8 = 0;
    let mut v_a_5843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5846_: u8 = 0;
    let mut v___x_5848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5850_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5793_ = l_Lean_Elab_Command_getRef___redArg(v___y_5790_);
                if leanh::lean_obj_tag(v___x_5793_) == 0 {
                    v_a_5794_ = leanh::lean_ctor_get(v___x_5793_, 0);
                    leanh::lean_inc(v_a_5794_);
                    leanh::lean_dec_ref_known(v___x_5793_, 1);
                    v___x_5795_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg(v_msg_5789_, v___y_5791_);
                    v_a_5796_ = leanh::lean_ctor_get(v___x_5795_, 0);
                    v_isSharedCheck_5842_ = (!leanh::lean_is_exclusive(v___x_5795_)) as u8;
                    if v_isSharedCheck_5842_ == 0 {
                        v___x_5798_ = v___x_5795_;
                        v_isShared_5799_ = v_isSharedCheck_5842_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5796_);
                        leanh::lean_dec(v___x_5795_);
                        v___x_5798_ = leanh::lean_box(0);
                        v_isShared_5799_ = v_isSharedCheck_5842_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_msg_5789_);
                    leanh::lean_dec(v_cls_5788_);
                    v_a_5843_ = leanh::lean_ctor_get(v___x_5793_, 0);
                    v_isSharedCheck_5850_ = (!leanh::lean_is_exclusive(v___x_5793_)) as u8;
                    if v_isSharedCheck_5850_ == 0 {
                        v___x_5845_ = v___x_5793_;
                        v_isShared_5846_ = v_isSharedCheck_5850_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5843_);
                        leanh::lean_dec(v___x_5793_);
                        v___x_5845_ = leanh::lean_box(0);
                        v_isShared_5846_ = v_isSharedCheck_5850_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5800_ = lean_st_ref_take(v___y_5791_);
                v_traceState_5801_ = leanh::lean_ctor_get(v___x_5800_, 9);
                v_env_5802_ = leanh::lean_ctor_get(v___x_5800_, 0);
                v_messages_5803_ = leanh::lean_ctor_get(v___x_5800_, 1);
                v_scopes_5804_ = leanh::lean_ctor_get(v___x_5800_, 2);
                v_usedQuotCtxts_5805_ = leanh::lean_ctor_get(v___x_5800_, 3);
                v_nextMacroScope_5806_ = leanh::lean_ctor_get(v___x_5800_, 4);
                v_maxRecDepth_5807_ = leanh::lean_ctor_get(v___x_5800_, 5);
                v_ngen_5808_ = leanh::lean_ctor_get(v___x_5800_, 6);
                v_auxDeclNGen_5809_ = leanh::lean_ctor_get(v___x_5800_, 7);
                v_infoState_5810_ = leanh::lean_ctor_get(v___x_5800_, 8);
                v_snapshotTasks_5811_ = leanh::lean_ctor_get(v___x_5800_, 10);
                v_isSharedCheck_5841_ = (!leanh::lean_is_exclusive(v___x_5800_)) as u8;
                if v_isSharedCheck_5841_ == 0 {
                    v___x_5813_ = v___x_5800_;
                    v_isShared_5814_ = v_isSharedCheck_5841_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_5811_);
                    leanh::lean_inc(v_traceState_5801_);
                    leanh::lean_inc(v_infoState_5810_);
                    leanh::lean_inc(v_auxDeclNGen_5809_);
                    leanh::lean_inc(v_ngen_5808_);
                    leanh::lean_inc(v_maxRecDepth_5807_);
                    leanh::lean_inc(v_nextMacroScope_5806_);
                    leanh::lean_inc(v_usedQuotCtxts_5805_);
                    leanh::lean_inc(v_scopes_5804_);
                    leanh::lean_inc(v_messages_5803_);
                    leanh::lean_inc(v_env_5802_);
                    leanh::lean_dec(v___x_5800_);
                    v___x_5813_ = leanh::lean_box(0);
                    v_isShared_5814_ = v_isSharedCheck_5841_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_5815_ = leanh::lean_ctor_get_uint64(
                    v_traceState_5801_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_traces_5816_ = leanh::lean_ctor_get(v_traceState_5801_, 0);
                v_isSharedCheck_5840_ =
                    (!leanh::lean_is_exclusive(v_traceState_5801_)) as u8;
                if v_isSharedCheck_5840_ == 0 {
                    v___x_5818_ = v_traceState_5801_;
                    v_isShared_5819_ = v_isSharedCheck_5840_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_traces_5816_);
                    leanh::lean_dec(v_traceState_5801_);
                    v___x_5818_ = leanh::lean_box(0);
                    v_isShared_5819_ = v_isSharedCheck_5840_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5820_ = leanh::lean_box(0);
                v___x_5821_ = leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg___closed__0_once), _init_l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg___closed__0);
                v___x_5822_ = 0;
                v___x_5823_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build___closed__0;
                v___x_5824_ = leanh::lean_alloc_ctor(0, 3, (17) as u32);
                leanh::lean_ctor_set(v___x_5824_, 0, v_cls_5788_);
                leanh::lean_ctor_set(v___x_5824_, 1, v___x_5820_);
                leanh::lean_ctor_set(v___x_5824_, 2, v___x_5823_);
                leanh::lean_ctor_set_float(
                    v___x_5824_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_5821_,
                );
                leanh::lean_ctor_set_float(
                    v___x_5824_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_5821_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_5824_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_5822_,
                );
                v___x_5825_ = l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg___closed__1;
                v___x_5826_ = leanh::lean_alloc_ctor(9, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_5826_, 0, v___x_5824_);
                leanh::lean_ctor_set(v___x_5826_, 1, v_a_5796_);
                leanh::lean_ctor_set(v___x_5826_, 2, v___x_5825_);
                v___x_5827_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5827_, 0, v_a_5794_);
                leanh::lean_ctor_set(v___x_5827_, 1, v___x_5826_);
                v___x_5828_ = l_Lean_PersistentArray_push___redArg(v_traces_5816_, v___x_5827_);
                if v_isShared_5819_ == 0 {
                    leanh::lean_ctor_set(v___x_5818_, 0, v___x_5828_);
                    v___x_5830_ = v___x_5818_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5839_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5839_, 0, v___x_5828_);
                    leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_5839_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_tid_5815_,
                    );
                    v___x_5830_ = v_reuseFailAlloc_5839_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_5814_ == 0 {
                    leanh::lean_ctor_set(v___x_5813_, 9, v___x_5830_);
                    v___x_5832_ = v___x_5813_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5838_ = leanh::lean_alloc_ctor(0, 11, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5838_, 0, v_env_5802_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5838_, 1, v_messages_5803_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5838_, 2, v_scopes_5804_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5838_, 3, v_usedQuotCtxts_5805_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5838_, 4, v_nextMacroScope_5806_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5838_, 5, v_maxRecDepth_5807_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5838_, 6, v_ngen_5808_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5838_, 7, v_auxDeclNGen_5809_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5838_, 8, v_infoState_5810_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5838_, 9, v___x_5830_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5838_, 10, v_snapshotTasks_5811_);
                    v___x_5832_ = v_reuseFailAlloc_5838_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5833_ = lean_st_ref_set(v___y_5791_, v___x_5832_);
                v___x_5834_ = leanh::lean_box(0);
                if v_isShared_5799_ == 0 {
                    leanh::lean_ctor_set(v___x_5798_, 0, v___x_5834_);
                    v___x_5836_ = v___x_5798_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5837_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5837_, 0, v___x_5834_);
                    v___x_5836_ = v_reuseFailAlloc_5837_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5836_;
            }
            7 => {
                if v_isShared_5846_ == 0 {
                    v___x_5848_ = v___x_5845_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5849_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5849_, 0, v_a_5843_);
                    v___x_5848_ = v_reuseFailAlloc_5849_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5848_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1___boxed(
    mut v_cls_5851_: *mut leanh::LeanObject,
    mut v_msg_5852_: *mut leanh::LeanObject,
    mut v___y_5853_: *mut leanh::LeanObject,
    mut v___y_5854_: *mut leanh::LeanObject,
    mut v___y_5855_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5856_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5856_ = l_Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1(
        v_cls_5851_,
        v_msg_5852_,
        v___y_5853_,
        v___y_5854_,
    );
    leanh::lean_dec(v___y_5854_);
    leanh::lean_dec_ref(v___y_5853_);
    return v_res_5856_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_5858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5859_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5858_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__0;
    v___x_5859_ = l_Lean_stringToMessageData(v___x_5858_);
    return v___x_5859_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_5861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5862_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5861_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__2;
    v___x_5862_ = l_Lean_stringToMessageData(v___x_5861_);
    return v___x_5862_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_5864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5865_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5864_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__4;
    v___x_5865_ = l_Lean_stringToMessageData(v___x_5864_);
    return v___x_5865_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2(
    mut v_mkCmd_5866_: *mut leanh::LeanObject,
    mut v___x_5867_: *mut leanh::LeanObject,
    mut v_className_5868_: *mut leanh::LeanObject,
    mut v_as_5869_: *mut leanh::LeanObject,
    mut v_sz_5870_: usize,
    mut v_i_5871_: usize,
    mut v_b_5872_: *mut leanh::LeanObject,
    mut v___y_5873_: *mut leanh::LeanObject,
    mut v___y_5874_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_5877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5878_: usize = 0;
    let mut v___x_5879_: usize = 0;
    let mut v___x_5881_: u8 = 0;
    let mut v___x_5882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_5891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_5894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_5895_: u8 = 0;
    let mut v___x_5896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5899_: u8 = 0;
    let mut v___x_5900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5901_: u8 = 0;
    let mut v___x_5902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5914_: u8 = 0;
    let mut v___x_5916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5918_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5881_ = lean_usize_dec_lt(v_i_5871_, v_sz_5870_);
                if v___x_5881_ == 0 {
                    leanh::lean_dec(v_className_5868_);
                    leanh::lean_dec_ref(v___x_5867_);
                    leanh::lean_dec_ref(v_mkCmd_5866_);
                    v___x_5882_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5882_, 0, v_b_5872_);
                    return v___x_5882_;
                } else {
                    v_a_5883_ = lean_array_uget_borrowed(v_as_5869_, v_i_5871_);
                    leanh::lean_inc_ref(v___x_5867_);
                    leanh::lean_inc(v_a_5883_);
                    leanh::lean_inc_ref(v_mkCmd_5866_);
                    v___f_5884_ = leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___lam__0___boxed as *mut core::ffi::c_void, 10, 3);
                    leanh::lean_closure_set(v___f_5884_, 0, v_mkCmd_5866_);
                    leanh::lean_closure_set(v___f_5884_, 1, v_a_5883_);
                    leanh::lean_closure_set(v___f_5884_, 2, v___x_5867_);
                    v___x_5885_ = l_Lean_Elab_Command_liftTermElabM___redArg(
                        v___f_5884_,
                        v___y_5873_,
                        v___y_5874_,
                    );
                    if leanh::lean_obj_tag(v___x_5885_) == 0 {
                        v_a_5886_ = leanh::lean_ctor_get(v___x_5885_, 0);
                        leanh::lean_inc(v_a_5886_);
                        leanh::lean_dec_ref_known(v___x_5885_, 1);
                        v___x_5887_ =
                            l_Lean_Elab_Command_elabCommand(v_a_5886_, v___y_5873_, v___y_5874_);
                        if leanh::lean_obj_tag(v___x_5887_) == 0 {
                            leanh::lean_dec_ref_known(v___x_5887_, 1);
                            v___x_5888_ = l_Lean_inheritedTraceOptions;
                            v___x_5889_ = lean_st_ref_get(v___x_5888_);
                            v___x_5890_ = lean_st_ref_get(v___y_5874_);
                            v_scopes_5891_ = leanh::lean_ctor_get(v___x_5890_, 2);
                            leanh::lean_inc(v_scopes_5891_);
                            leanh::lean_dec(v___x_5890_);
                            v___x_5892_ = l_Lean_Elab_Command_instInhabitedScope_default;
                            v___x_5893_ = l_List_head_x21___redArg(v___x_5892_, v_scopes_5891_);
                            leanh::lean_dec(v_scopes_5891_);
                            v_opts_5894_ = leanh::lean_ctor_get(v___x_5893_, 1);
                            leanh::lean_inc_ref(v_opts_5894_);
                            leanh::lean_dec(v___x_5893_);
                            v_hasTrace_5895_ = leanh::lean_ctor_get_uint8(
                                v_opts_5894_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            );
                            v___x_5896_ = leanh::lean_box(0);
                            if v_hasTrace_5895_ == 0 {
                                leanh::lean_dec_ref(v_opts_5894_);
                                leanh::lean_dec(v___x_5889_);
                                v_a_5877_ = v___x_5896_;
                                state = 1;
                                continue;
                            } else {
                                v___x_5897_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__2;
                                v___x_5898_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3_once), _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3);
                                v___x_5899_ =
                                    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                        v___x_5889_,
                                        v_opts_5894_,
                                        v___x_5898_,
                                    );
                                leanh::lean_dec_ref(v_opts_5894_);
                                leanh::lean_dec(v___x_5889_);
                                if v___x_5899_ == 0 {
                                    v_a_5877_ = v___x_5896_;
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_5900_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__1);
                                    v___x_5901_ = 0;
                                    leanh::lean_inc(v_className_5868_);
                                    v___x_5902_ = l_Lean_MessageData_ofConstName(
                                        v_className_5868_,
                                        v___x_5901_,
                                    );
                                    v___x_5903_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_5903_, 0, v___x_5900_);
                                    leanh::lean_ctor_set(v___x_5903_, 1, v___x_5902_);
                                    v___x_5904_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__3);
                                    v___x_5905_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_5905_, 0, v___x_5903_);
                                    leanh::lean_ctor_set(v___x_5905_, 1, v___x_5904_);
                                    leanh::lean_inc(v_a_5883_);
                                    v___x_5906_ = l_Lean_MessageData_ofExpr(v_a_5883_);
                                    v___x_5907_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_5907_, 0, v___x_5905_);
                                    leanh::lean_ctor_set(v___x_5907_, 1, v___x_5906_);
                                    v___x_5908_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__5), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__5_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__5);
                                    v___x_5909_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_5909_, 0, v___x_5907_);
                                    leanh::lean_ctor_set(v___x_5909_, 1, v___x_5908_);
                                    v___x_5910_ = l_Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1(v___x_5897_, v___x_5909_, v___y_5873_, v___y_5874_);
                                    if leanh::lean_obj_tag(v___x_5910_) == 0 {
                                        leanh::lean_dec_ref_known(v___x_5910_, 1);
                                        v_a_5877_ = v___x_5896_;
                                        state = 1;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v_className_5868_);
                                        leanh::lean_dec_ref(v___x_5867_);
                                        leanh::lean_dec_ref(v_mkCmd_5866_);
                                        return v___x_5910_;
                                    }
                                }
                            }
                        } else {
                            leanh::lean_dec(v_className_5868_);
                            leanh::lean_dec_ref(v___x_5867_);
                            leanh::lean_dec_ref(v_mkCmd_5866_);
                            return v___x_5887_;
                        }
                    } else {
                        leanh::lean_dec(v_className_5868_);
                        leanh::lean_dec_ref(v___x_5867_);
                        leanh::lean_dec_ref(v_mkCmd_5866_);
                        v_a_5911_ = leanh::lean_ctor_get(v___x_5885_, 0);
                        v_isSharedCheck_5918_ =
                            (!leanh::lean_is_exclusive(v___x_5885_)) as u8;
                        if v_isSharedCheck_5918_ == 0 {
                            v___x_5913_ = v___x_5885_;
                            v_isShared_5914_ = v_isSharedCheck_5918_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5911_);
                            leanh::lean_dec(v___x_5885_);
                            v___x_5913_ = leanh::lean_box(0);
                            v_isShared_5914_ = v_isSharedCheck_5918_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5878_ = 1usize;
                v___x_5879_ = lean_usize_add(v_i_5871_, v___x_5878_);
                v_i_5871_ = v___x_5879_;
                v_b_5872_ = v_a_5877_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_5914_ == 0 {
                    v___x_5916_ = v___x_5913_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5917_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5917_, 0, v_a_5911_);
                    v___x_5916_ = v_reuseFailAlloc_5917_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5916_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___boxed(
    mut v_mkCmd_5919_: *mut leanh::LeanObject,
    mut v___x_5920_: *mut leanh::LeanObject,
    mut v_className_5921_: *mut leanh::LeanObject,
    mut v_as_5922_: *mut leanh::LeanObject,
    mut v_sz_5923_: *mut leanh::LeanObject,
    mut v_i_5924_: *mut leanh::LeanObject,
    mut v_b_5925_: *mut leanh::LeanObject,
    mut v___y_5926_: *mut leanh::LeanObject,
    mut v___y_5927_: *mut leanh::LeanObject,
    mut v___y_5928_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5929_: usize = 0;
    let mut v_i_boxed_5930_: usize = 0;
    let mut v_res_5931_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5929_ = leanh::lean_unbox_usize(v_sz_5923_);
    leanh::lean_dec(v_sz_5923_);
    v_i_boxed_5930_ = leanh::lean_unbox_usize(v_i_5924_);
    leanh::lean_dec(v_i_5924_);
    v_res_5931_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2(v_mkCmd_5919_, v___x_5920_, v_className_5921_, v_as_5922_, v_sz_boxed_5929_, v_i_boxed_5930_, v_b_5925_, v___y_5926_, v___y_5927_);
    leanh::lean_dec(v___y_5927_);
    leanh::lean_dec_ref(v___y_5926_);
    leanh::lean_dec_ref(v_as_5922_);
    return v_res_5931_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_withClassInstDeps(
    mut v_className_5932_: *mut leanh::LeanObject,
    mut v_type_5933_: *mut leanh::LeanObject,
    mut v_extraDeps_5934_: *mut leanh::LeanObject,
    mut v_mkCmd_5935_: *mut leanh::LeanObject,
    mut v_a_5936_: *mut leanh::LeanObject,
    mut v_a_5937_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5945_: usize = 0;
    let mut v___x_5946_: usize = 0;
    let mut v___x_5947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5950_: u8 = 0;
    let mut v___x_5952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5954_: u8 = 0;
    let mut v_unused_5955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5959_: u8 = 0;
    let mut v___x_5961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5963_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_className_5932_);
                v___x_5939_ = leanh::lean_alloc_closure(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___boxed as *mut core::ffi::c_void, 10, 3);
                leanh::lean_closure_set(v___x_5939_, 0, v_className_5932_);
                leanh::lean_closure_set(v___x_5939_, 1, v_type_5933_);
                leanh::lean_closure_set(v___x_5939_, 2, v_extraDeps_5934_);
                v___x_5940_ =
                    l_Lean_Elab_Command_liftTermElabM___redArg(v___x_5939_, v_a_5936_, v_a_5937_);
                if leanh::lean_obj_tag(v___x_5940_) == 0 {
                    v_a_5941_ = leanh::lean_ctor_get(v___x_5940_, 0);
                    leanh::lean_inc(v_a_5941_);
                    leanh::lean_dec_ref_known(v___x_5940_, 1);
                    v___x_5942_ = lean_st_ref_get(v_a_5937_);
                    v_env_5943_ = leanh::lean_ctor_get(v___x_5942_, 0);
                    leanh::lean_inc_ref(v_env_5943_);
                    leanh::lean_dec(v___x_5942_);
                    v___x_5944_ = leanh::lean_box(0);
                    v_sz_5945_ = lean_array_size(v_a_5941_);
                    v___x_5946_ = 0usize;
                    v___x_5947_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2(v_mkCmd_5935_, v_env_5943_, v_className_5932_, v_a_5941_, v_sz_5945_, v___x_5946_, v___x_5944_, v_a_5936_, v_a_5937_);
                    leanh::lean_dec(v_a_5941_);
                    if leanh::lean_obj_tag(v___x_5947_) == 0 {
                        v_isSharedCheck_5954_ =
                            (!leanh::lean_is_exclusive(v___x_5947_)) as u8;
                        if v_isSharedCheck_5954_ == 0 {
                            v_unused_5955_ = leanh::lean_ctor_get(v___x_5947_, 0);
                            leanh::lean_dec(v_unused_5955_);
                            v___x_5949_ = v___x_5947_;
                            v_isShared_5950_ = v_isSharedCheck_5954_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_5947_);
                            v___x_5949_ = leanh::lean_box(0);
                            v_isShared_5950_ = v_isSharedCheck_5954_;
                            state = 1;
                            continue;
                        }
                    } else {
                        return v___x_5947_;
                    }
                } else {
                    leanh::lean_dec_ref(v_mkCmd_5935_);
                    leanh::lean_dec(v_className_5932_);
                    v_a_5956_ = leanh::lean_ctor_get(v___x_5940_, 0);
                    v_isSharedCheck_5963_ = (!leanh::lean_is_exclusive(v___x_5940_)) as u8;
                    if v_isSharedCheck_5963_ == 0 {
                        v___x_5958_ = v___x_5940_;
                        v_isShared_5959_ = v_isSharedCheck_5963_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5956_);
                        leanh::lean_dec(v___x_5940_);
                        v___x_5958_ = leanh::lean_box(0);
                        v_isShared_5959_ = v_isSharedCheck_5963_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5950_ == 0 {
                    leanh::lean_ctor_set(v___x_5949_, 0, v___x_5944_);
                    v___x_5952_ = v___x_5949_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5953_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5953_, 0, v___x_5944_);
                    v___x_5952_ = v_reuseFailAlloc_5953_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5952_;
            }
            3 => {
                if v_isShared_5959_ == 0 {
                    v___x_5961_ = v___x_5958_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5962_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5962_, 0, v_a_5956_);
                    v___x_5961_ = v_reuseFailAlloc_5962_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5961_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_withClassInstDeps___boxed(
    mut v_className_5964_: *mut leanh::LeanObject,
    mut v_type_5965_: *mut leanh::LeanObject,
    mut v_extraDeps_5966_: *mut leanh::LeanObject,
    mut v_mkCmd_5967_: *mut leanh::LeanObject,
    mut v_a_5968_: *mut leanh::LeanObject,
    mut v_a_5969_: *mut leanh::LeanObject,
    mut v_a_5970_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5971_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5971_ = l_Lean_Elab_ConfigEval_withClassInstDeps(
        v_className_5964_,
        v_type_5965_,
        v_extraDeps_5966_,
        v_mkCmd_5967_,
        v_a_5968_,
        v_a_5969_,
    );
    leanh::lean_dec(v_a_5969_);
    leanh::lean_dec_ref(v_a_5968_);
    return v_res_5971_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1(
    mut v_msgData_5972_: *mut leanh::LeanObject,
    mut v___y_5973_: *mut leanh::LeanObject,
    mut v___y_5974_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5976_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5976_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg(v_msgData_5972_, v___y_5974_);
    return v___x_5976_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___boxed(
    mut v_msgData_5977_: *mut leanh::LeanObject,
    mut v___y_5978_: *mut leanh::LeanObject,
    mut v___y_5979_: *mut leanh::LeanObject,
    mut v___y_5980_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5981_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5981_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1(v_msgData_5977_, v___y_5978_, v___y_5979_);
    leanh::lean_dec(v___y_5979_);
    leanh::lean_dec_ref(v___y_5978_);
    return v_res_5981_;
}
pub unsafe fn l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_6047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6048_: u8 = 0;
    let mut v___x_6049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6050_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6047_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__2;
    v___x_6048_ = 0;
    v___x_6049_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__25_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2_;
    v___x_6050_ = l_Lean_registerTraceClass(v___x_6047_, v___x_6048_, v___x_6049_);
    return v___x_6050_;
}
pub unsafe fn l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2____boxed(
    mut v_a_6051_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6052_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6052_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2_();
    return v_res_6052_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_ConfigEval_Util(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Command(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_ConfigEval_Util(
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
pub unsafe fn initialize_Lean_Elab_ConfigEval_Util(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Command(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_ConfigEval_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_ConfigEval_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_ConfigEval_Util(builtin);
}