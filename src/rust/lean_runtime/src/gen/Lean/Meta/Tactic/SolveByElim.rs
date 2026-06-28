// Lean compiler output
// Module: Lean.Meta.Tactic.SolveByElim
// Imports: Init.Data.Sum Lean.LabelAttribute Lean.Meta.Tactic.Backtrack Lean.Meta.Tactic.Constructor Lean.Meta.Tactic.Repeat Lean.Meta.Tactic.Symm Lean.Elab.Term
use crate::r#gen::Init::Data::Array::Basic::{
    l_Array_append___redArg, l_List_foldl___at___00Array_appendList_spec__0___redArg,
};
use crate::r#gen::Init::Data::List::Basic::{
    l_List_appendTR___redArg, l_List_filter___redArg, l_List_isEmpty___redArg,
    l_List_reverse___redArg,
};
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Data::Sum::{initialize_Init_Data_Sum, runtime_initialize_Init_Data_Sum};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_mkStr3, l_Lean_Name_num___override,
    l_Lean_Name_str___override, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getId,
    l_Lean_addMacroScope, l_Lean_replaceRef, l_String_toRawSubstring_x27,
};
use crate::r#gen::Lean::CoreM::l_Lean_Exception_isRuntime;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::PersistentArray::{
    l_Lean_PersistentArray_append___redArg, l_Lean_PersistentArray_push___redArg,
    l_Lean_PersistentArray_toArray___redArg,
};
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Elab::Term::TermElabM::{
    l_Lean_Elab_Term_TermElabM_run___redArg, l_Lean_Elab_Term_elabTerm,
};
use crate::r#gen::Lean::Elab::Term::{
    initialize_Lean_Elab_Term, runtime_initialize_Lean_Elab_Term,
};
use crate::r#gen::Lean::Exception::l_Lean_Exception_isInterrupt;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_hasMVar, l_Lean_Expr_mvar___override, l_Lean_instBEqMVarId_beq,
    l_Lean_instHashableMVarId_hash,
};
use crate::r#gen::Lean::LabelAttribute::{
    initialize_Lean_LabelAttribute, l_Lean_labelled, runtime_initialize_Lean_LabelAttribute,
};
use crate::r#gen::Lean::LocalContext::{
    l_Lean_LocalDecl_isImplementationDetail, l_Lean_LocalDecl_toExpr,
};
use crate::r#gen::Lean::Message::{l_Lean_MessageData_ofExpr, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp, l_Lean_Meta_Context_config,
    l_Lean_Meta_Context_configKey, l_Lean_Meta_SavedState_restore___redArg,
    l_Lean_Meta_TransparencyMode_toUInt64, l_Lean_Meta_mkConstWithFreshMVarLevels,
    l_Lean_Meta_saveState___redArg,
};
use crate::r#gen::Lean::Meta::Iterator::{
    l___private_Lean_Meta_Iterator_0__Lean_Meta_Iterator_filterMapM___next___boxed,
    l_Lean_Meta_Iterator_head___redArg, l_Lean_Meta_Iterator_ofList___redArg,
};
use crate::r#gen::Lean::Meta::SynthInstance::l_Lean_Meta_synthInstance;
use crate::r#gen::Lean::Meta::Tactic::Apply::{l_Lean_MVarId_apply, l_Lean_MVarId_exfalso};
use crate::r#gen::Lean::Meta::Tactic::Backtrack::{
    initialize_Lean_Meta_Tactic_Backtrack, l_Lean_Meta_Tactic_Backtrack_backtrack,
    runtime_initialize_Lean_Meta_Tactic_Backtrack,
};
use crate::r#gen::Lean::Meta::Tactic::Constructor::{
    initialize_Lean_Meta_Tactic_Constructor, l_Lean_MVarId_constructor,
    runtime_initialize_Lean_Meta_Tactic_Constructor,
};
use crate::r#gen::Lean::Meta::Tactic::Intro::l_Lean_Meta_intro1Core;
use crate::r#gen::Lean::Meta::Tactic::Repeat::{
    initialize_Lean_Meta_Tactic_Repeat, runtime_initialize_Lean_Meta_Tactic_Repeat,
};
use crate::r#gen::Lean::Meta::Tactic::Symm::{
    initialize_Lean_Meta_Tactic_Symm, l_Lean_Expr_applySymm,
    runtime_initialize_Lean_Meta_Tactic_Symm,
};
use crate::r#gen::Lean::Meta::Tactic::Util::{l_Lean_MVarId_getType, l_Lean_MVarId_inferInstance};
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Lean::Util::FindExpr::l_Lean_Expr_occurs;
use crate::r#gen::Lean::Util::Trace::{
    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go, l_Lean_TraceResult_toEmoji,
    l_Lean_registerTraceClass, l_Lean_trace_profiler, l_Lean_trace_profiler_threshold,
    l_Lean_trace_profiler_useHeartbeats,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::Float::{lean_float_decLt, lean_float_div, lean_float_sub};
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_lor, lean_uint64_shift_left, lean_uint64_shift_right, lean_uint64_to_usize,
    lean_usize_land, lean_usize_mul, lean_usize_shift_left, lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
    lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::IO::{
    lean_io_get_num_heartbeats, lean_io_mono_nanos_now,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Expr::lean_expr_eqv;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_5, lean_apply_6, lean_apply_7, lean_apply_8, lean_box, lean_box_float,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_get_uint64, lean_ctor_set,
    lean_ctor_set_float, lean_ctor_set_tag, lean_ctor_set_uint8, lean_ctor_set_uint64,
    lean_ctor_set_usize, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object,
    lean_float_once, lean_inc, lean_inc_n, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unbox,
    lean_unbox_float, lean_unbox_usize, lean_unsigned_to_nat, lean_usize_once,
};
pub static l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__0_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__0_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__0_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__1_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__1_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__1_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__2_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [115, 111, 108, 118, 101, 66, 121, 69, 108, 105, 109, 0]};
static mut l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__2_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__2_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__0_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value) as *mut LeanObject,142734480563613395 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__1_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value) as *mut LeanObject,15847151208953044930 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__2_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value) as *mut LeanObject,15933762081429107667 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__4_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__4_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__4_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__5_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__4_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__5_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__5_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__6_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__6_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__6_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__7_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__5_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__6_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value) as *mut LeanObject,10352885018404983386 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__7_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__7_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__8_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__7_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__0_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value) as *mut LeanObject,13556645696814629918 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__8_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__8_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__9_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__8_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__1_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value) as *mut LeanObject,18261494228143523011 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__9_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__9_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__10_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [83, 111, 108, 118, 101, 66, 121, 69, 108, 105, 109, 0]};
static mut l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__10_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__10_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__11_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__9_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__10_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value) as *mut LeanObject,16953199068887284896 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__11_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__11_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__12_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__11_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,15613865758377383129 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__12_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__12_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__13_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__12_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__6_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value) as *mut LeanObject,6374525547227858620 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__13_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__13_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__14_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__13_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__0_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value) as *mut LeanObject,9665627801066572736 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__14_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__14_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__15_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__14_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__10_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value) as *mut LeanObject,6100880789239980127 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__15_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__15_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__16_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__16_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__16_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__17_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__15_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__16_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value) as *mut LeanObject,16171311638899483518 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__17_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__17_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__18_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__18_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__18_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__19_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__17_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__18_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value) as *mut LeanObject,10952074911740446367 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__19_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__19_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__20_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__19_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__6_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value) as *mut LeanObject,3955255408667699282 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__20_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__20_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__21_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__20_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__0_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value) as *mut LeanObject,4081974627457573574 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__21_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__21_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__22_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__21_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__1_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value) as *mut LeanObject,16010851464576248411 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__22_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__22_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__23_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__22_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__10_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value) as *mut LeanObject,16141982932145577752 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__23_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__23_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__24_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__23_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value) as *mut LeanObject,((( 1979843508 as usize) << 1) | 1) as *mut LeanObject,14259435572816672137 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__24_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__24_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__25_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__25_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__25_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__26_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__24_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__25_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value) as *mut LeanObject,16374197204089067034 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__26_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__26_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__27_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__27_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__27_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__28_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__26_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__27_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value) as *mut LeanObject,954235401373109862 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__28_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__28_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__29_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__28_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject,4836708041685628071 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__29_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__29_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__0_value:
    LeanStringObject<18> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 18,
    m_capacity: 18,
    m_length: 17,
    m_data: [
        116, 114, 121, 105, 110, 103, 32, 116, 111, 32, 97, 112, 112, 108, 121, 58, 32, 0,
    ],
};
static mut l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__0_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__2: f64 = 0.0;
pub static l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__3_value: LeanStringObject<54> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [60, 101, 120, 99, 101, 112, 116, 105, 111, 110, 32, 116, 104, 114, 111, 119, 110, 32, 119, 104, 105, 108, 101, 32, 112, 114, 111, 100, 117, 99, 105, 110, 103, 32, 116, 114, 97, 99, 101, 32, 110, 111, 100, 101, 32, 109, 101, 115, 115, 97, 103, 101, 62, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__3_value) as *mut LeanObject;
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__5: f64 = 0.0;
pub static l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__0_value:
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
static mut l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__1_value:
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
            l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__0_value
        ) as *mut LeanObject,
        14231257465488249300 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2: f64 = 0.0;
pub static l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___closed__0_value:
    LeanStringObject<1> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 1,
    m_capacity: 1,
    m_length: 0,
    m_data: [0],
};
static mut l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___closed__0_value:
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
    m_fun: l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___closed__0_value
) as *mut LeanObject;
pub static mut l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___closed__0_value
)
    as *mut LeanObject;
pub static l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___closed__0_value: LeanClosureObject<
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
    m_fun: l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___closed__0_value:
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
    m_fun: l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___closed__0_value:
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
    m_fun: l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0___closed__0_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 0
            + 8) as u16,
        other: 0,
        tag: 0,
    },
    m_objs: [16777474 as *mut LeanObject],
};
static mut l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___closed__0_value:
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
    m_fun: l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___closed__0: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___closed__0_value
)
    as *mut LeanObject;
pub static l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___closed__0_value:
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
    m_fun: l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__0_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [102, 97, 105, 108, 101, 100, 0]};
static mut l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__0_value
) as *mut LeanObject;
static mut l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_SolveByElim_elabContextLemmas___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1___boxed
            as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_SolveByElim_elabContextLemmas___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_SolveByElim_elabContextLemmas___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_SolveByElim_elabContextLemmas___closed__1_value: LeanArrayObject<0> =
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
static mut l_Lean_Meta_SolveByElim_elabContextLemmas___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_SolveByElim_elabContextLemmas___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_SolveByElim_elabContextLemmas___closed__2_value: LeanCtorObject<10> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 8
                + 16) as u16,
            other: 8,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_SolveByElim_elabContextLemmas___closed__0_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_SolveByElim_elabContextLemmas___closed__1_value)
                as *mut LeanObject,
            16843009 as *mut LeanObject,
            65537 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_SolveByElim_elabContextLemmas___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_SolveByElim_elabContextLemmas___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Meta_SolveByElim_elabContextLemmas___closed__3_value: LeanCtorObject<7> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 7
                + 0) as u16,
            other: 7,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_SolveByElim_elabContextLemmas___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_SolveByElim_elabContextLemmas___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__0_value) as *mut LeanObject;
static mut l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__0_value: LeanStringObject<28> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 28, m_capacity: 28, m_length: 27, m_data: [96, 114, 101, 112, 101, 97, 116, 49, 39, 96, 32, 109, 97, 100, 101, 32, 110, 111, 32, 112, 114, 111, 103, 114, 101, 115, 115, 0]};
static mut l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__0_value) as *mut LeanObject;
static mut l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__0_value: LeanStringObject<37> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 37,
        m_capacity: 37,
        m_length: 32,
        m_data: [
            226, 143, 174, 239, 184, 143, 32, 115, 116, 97, 114, 116, 105, 110, 103, 32, 111, 118,
            101, 114, 32, 117, 115, 105, 110, 103, 32, 96, 101, 120, 102, 97, 108, 115, 111, 96, 0,
        ],
    };
static mut l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_SolveByElim_solveByElim___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Meta_SolveByElim_solveByElim___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_SolveByElim_solveByElim___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_SolveByElim_solveByElim___closed__0_value) as *mut LeanObject;
static mut l_Lean_Meta_SolveByElim_solveByElim___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_SolveByElim_solveByElim___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0___closed__0_value:
    LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__0_value: LeanStringObject<80> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 80,
        m_capacity: 80,
        m_length: 79,
        m_data: [
            73, 116, 32, 100, 111, 101, 115, 110, 39, 116, 32, 109, 97, 107, 101, 32, 115, 101,
            110, 115, 101, 32, 116, 111, 32, 114, 101, 109, 111, 118, 101, 32, 108, 111, 99, 97,
            108, 32, 104, 121, 112, 111, 116, 104, 101, 115, 101, 115, 32, 119, 104, 101, 110, 32,
            117, 115, 105, 110, 103, 32, 96, 111, 110, 108, 121, 96, 32, 119, 105, 116, 104, 111,
            117, 116, 32, 96, 42, 96, 46, 0,
        ],
    };
static mut l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__2_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [114, 102, 108, 0],
    };
static mut l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__4_value: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__2_value)
                as *mut LeanObject,
            17342663138809293389 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__5_value: LeanStringObject<8> =
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
        m_data: [116, 114, 105, 118, 105, 97, 108, 0],
    };
static mut l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__5_value)
        as *mut LeanObject;
static mut l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__7_value: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__5_value)
                as *mut LeanObject,
            1505373468667533072 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__8_value: LeanStringObject<9> =
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
        m_data: [99, 111, 110, 103, 114, 70, 117, 110, 0],
    };
static mut l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__8_value)
        as *mut LeanObject;
static mut l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__10_value: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__8_value)
                as *mut LeanObject,
            10988039791356833343 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__11_value: LeanStringObject<9> =
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
        m_data: [99, 111, 110, 103, 114, 65, 114, 103, 0],
    };
static mut l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__11_value)
        as *mut LeanObject;
static mut l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__13_value: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__11_value)
                as *mut LeanObject,
            2642306550782628284 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__13_value)
        as *mut LeanObject;
pub static l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__14_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__4_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__14_value)
        as *mut LeanObject;
pub static l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__15_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__14_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__15_value)
        as *mut LeanObject;
pub static l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__16_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__7_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__16_value)
        as *mut LeanObject;
pub static l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__17_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__16_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__17_value)
        as *mut LeanObject;
pub static l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__18_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__10_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__18_value)
        as *mut LeanObject;
pub static l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__19_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__18_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__19_value)
        as *mut LeanObject;
pub static l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__20_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__13_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__20_value)
        as *mut LeanObject;
pub static l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__21_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__20_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__21_value)
        as *mut LeanObject;
pub static l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__22_value: LeanArrayObject<0> =
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
static mut l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__22: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__22_value)
        as *mut LeanObject;
pub static l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__23_value: LeanStringObject<49> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 49,
        m_capacity: 49,
        m_length: 48,
        m_data: [
            73, 116, 32, 100, 111, 101, 115, 110, 39, 116, 32, 109, 97, 107, 101, 32, 115, 101,
            110, 115, 101, 32, 116, 111, 32, 117, 115, 101, 32, 96, 42, 96, 32, 119, 105, 116, 104,
            111, 117, 116, 32, 96, 111, 110, 108, 121, 96, 46, 0,
        ],
    };
static mut l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__23: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__23_value)
        as *mut LeanObject;
static mut l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24: *mut LeanObject =
    core::ptr::null_mut();
pub unsafe fn l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4189_: u8 = 0;
    let mut v___x_4190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4191_: *mut LeanObject = core::ptr::null_mut();
    v___x_4188_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_;
    v___x_4189_ = 0;
    v___x_4190_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__29_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_;
    v___x_4191_ = l_Lean_registerTraceClass(v___x_4188_, v___x_4189_, v___x_4190_);
    return v___x_4191_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2____boxed(
    mut v_a_4192_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4193_: *mut LeanObject = core::ptr::null_mut();
    v_res_4193_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_();
    return v_res_4193_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_4194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4196_: *mut LeanObject = core::ptr::null_mut();
    v___x_4194_ = lean_unsigned_to_nat(32);
    v___x_4195_ = lean_mk_empty_array_with_capacity(v___x_4194_);
    v___x_4196_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4196_, 0, v___x_4195_);
    return v___x_4196_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_4197_: usize = 0;
    let mut v___x_4198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4202_: *mut LeanObject = core::ptr::null_mut();
    v___x_4197_ = 5usize;
    v___x_4198_ = lean_unsigned_to_nat(0);
    v___x_4199_ = lean_unsigned_to_nat(32);
    v___x_4200_ = lean_mk_empty_array_with_capacity(v___x_4199_);
    v___x_4201_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___closed__0_once), _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___closed__0);
    v___x_4202_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_4202_, 0, v___x_4201_);
    lean_ctor_set(v___x_4202_, 1, v___x_4200_);
    lean_ctor_set(v___x_4202_, 2, v___x_4198_);
    lean_ctor_set(v___x_4202_, 3, v___x_4198_);
    lean_ctor_set_usize(v___x_4202_, 4, v___x_4197_);
    return v___x_4202_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg(
    mut v___y_4203_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_4206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traces_4207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_4209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_4212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_4214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_4215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_4216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4220_: u8 = 0;
    let mut v_tid_4221_: u64 = 0;
    let mut v___x_4223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4224_: u8 = 0;
    let mut v___x_4225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4234_: u8 = 0;
    let mut v_unused_4235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4236_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4205_ = lean_st_ref_get(v___y_4203_);
                v_traceState_4206_ = lean_ctor_get(v___x_4205_, 4);
                lean_inc_ref(v_traceState_4206_);
                lean_dec(v___x_4205_);
                v_traces_4207_ = lean_ctor_get(v_traceState_4206_, 0);
                lean_inc_ref(v_traces_4207_);
                lean_dec_ref(v_traceState_4206_);
                v___x_4208_ = lean_st_ref_take(v___y_4203_);
                v_traceState_4209_ = lean_ctor_get(v___x_4208_, 4);
                v_env_4210_ = lean_ctor_get(v___x_4208_, 0);
                v_nextMacroScope_4211_ = lean_ctor_get(v___x_4208_, 1);
                v_ngen_4212_ = lean_ctor_get(v___x_4208_, 2);
                v_auxDeclNGen_4213_ = lean_ctor_get(v___x_4208_, 3);
                v_cache_4214_ = lean_ctor_get(v___x_4208_, 5);
                v_messages_4215_ = lean_ctor_get(v___x_4208_, 6);
                v_infoState_4216_ = lean_ctor_get(v___x_4208_, 7);
                v_snapshotTasks_4217_ = lean_ctor_get(v___x_4208_, 8);
                v_isSharedCheck_4236_ = (!lean_is_exclusive(v___x_4208_)) as u8;
                if v_isSharedCheck_4236_ == 0 {
                    v___x_4219_ = v___x_4208_;
                    v_isShared_4220_ = v_isSharedCheck_4236_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_4217_);
                    lean_inc(v_infoState_4216_);
                    lean_inc(v_messages_4215_);
                    lean_inc(v_cache_4214_);
                    lean_inc(v_traceState_4209_);
                    lean_inc(v_auxDeclNGen_4213_);
                    lean_inc(v_ngen_4212_);
                    lean_inc(v_nextMacroScope_4211_);
                    lean_inc(v_env_4210_);
                    lean_dec(v___x_4208_);
                    v___x_4219_ = lean_box(0);
                    v_isShared_4220_ = v_isSharedCheck_4236_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_tid_4221_ = lean_ctor_get_uint64(
                    v_traceState_4209_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_4234_ = (!lean_is_exclusive(v_traceState_4209_)) as u8;
                if v_isSharedCheck_4234_ == 0 {
                    v_unused_4235_ = lean_ctor_get(v_traceState_4209_, 0);
                    lean_dec(v_unused_4235_);
                    v___x_4223_ = v_traceState_4209_;
                    v_isShared_4224_ = v_isSharedCheck_4234_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_traceState_4209_);
                    v___x_4223_ = lean_box(0);
                    v_isShared_4224_ = v_isSharedCheck_4234_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4225_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___closed__1_once), _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___closed__1);
                if v_isShared_4224_ == 0 {
                    lean_ctor_set(v___x_4223_, 0, v___x_4225_);
                    v___x_4227_ = v___x_4223_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4233_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4233_, 0, v___x_4225_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_4233_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_4221_,
                    );
                    v___x_4227_ = v_reuseFailAlloc_4233_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4220_ == 0 {
                    lean_ctor_set(v___x_4219_, 4, v___x_4227_);
                    v___x_4229_ = v___x_4219_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4232_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4232_, 0, v_env_4210_);
                    lean_ctor_set(v_reuseFailAlloc_4232_, 1, v_nextMacroScope_4211_);
                    lean_ctor_set(v_reuseFailAlloc_4232_, 2, v_ngen_4212_);
                    lean_ctor_set(v_reuseFailAlloc_4232_, 3, v_auxDeclNGen_4213_);
                    lean_ctor_set(v_reuseFailAlloc_4232_, 4, v___x_4227_);
                    lean_ctor_set(v_reuseFailAlloc_4232_, 5, v_cache_4214_);
                    lean_ctor_set(v_reuseFailAlloc_4232_, 6, v_messages_4215_);
                    lean_ctor_set(v_reuseFailAlloc_4232_, 7, v_infoState_4216_);
                    lean_ctor_set(v_reuseFailAlloc_4232_, 8, v_snapshotTasks_4217_);
                    v___x_4229_ = v_reuseFailAlloc_4232_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4230_ = lean_st_ref_set(v___y_4203_, v___x_4229_);
                v___x_4231_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4231_, 0, v_traces_4207_);
                return v___x_4231_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___boxed(
    mut v___y_4237_: *mut LeanObject,
    mut v___y_4238_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4239_: *mut LeanObject = core::ptr::null_mut();
    v_res_4239_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg(v___y_4237_);
    lean_dec(v___y_4237_);
    return v_res_4239_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0(
    mut v___y_4240_: *mut LeanObject,
    mut v___y_4241_: *mut LeanObject,
    mut v___y_4242_: *mut LeanObject,
    mut v___y_4243_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4245_: *mut LeanObject = core::ptr::null_mut();
    v___x_4245_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg(v___y_4243_);
    return v___x_4245_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___boxed(
    mut v___y_4246_: *mut LeanObject,
    mut v___y_4247_: *mut LeanObject,
    mut v___y_4248_: *mut LeanObject,
    mut v___y_4249_: *mut LeanObject,
    mut v___y_4250_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4251_: *mut LeanObject = core::ptr::null_mut();
    v_res_4251_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0(v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_);
    lean_dec(v___y_4249_);
    lean_dec_ref(v___y_4248_);
    lean_dec(v___y_4247_);
    lean_dec_ref(v___y_4246_);
    return v_res_4251_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(
    mut v_opts_4252_: *mut LeanObject,
    mut v_opt_4253_: *mut LeanObject,
) -> u8 {
    let mut v_name_4254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_4255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_4256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4257_: *mut LeanObject = core::ptr::null_mut();
    v_name_4254_ = lean_ctor_get(v_opt_4253_, 0);
    v_defValue_4255_ = lean_ctor_get(v_opt_4253_, 1);
    v_map_4256_ = lean_ctor_get(v_opts_4252_, 0);
    v___x_4257_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_4256_,
            v_name_4254_,
        );
    if lean_obj_tag(v___x_4257_) == 0 {
        let mut v___x_4258_: u8 = 0;
        v___x_4258_ = (lean_unbox(v_defValue_4255_) as u8);
        return v___x_4258_;
    } else {
        let mut v_val_4259_: *mut LeanObject = core::ptr::null_mut();
        v_val_4259_ = lean_ctor_get(v___x_4257_, 0);
        lean_inc(v_val_4259_);
        lean_dec_ref_known(v___x_4257_, 1);
        if lean_obj_tag(v_val_4259_) == 1 {
            let mut v_v_4260_: u8 = 0;
            v_v_4260_ = lean_ctor_get_uint8(v_val_4259_, 0 as u32);
            lean_dec_ref_known(v_val_4259_, 0);
            return v_v_4260_;
        } else {
            let mut v___x_4261_: u8 = 0;
            lean_dec(v_val_4259_);
            v___x_4261_ = (lean_unbox(v_defValue_4255_) as u8);
            return v___x_4261_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1___boxed(
    mut v_opts_4262_: *mut LeanObject,
    mut v_opt_4263_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4264_: u8 = 0;
    let mut v_r_4265_: *mut LeanObject = core::ptr::null_mut();
    v_res_4264_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(
        v_opts_4262_,
        v_opt_4263_,
    );
    lean_dec_ref(v_opt_4263_);
    lean_dec_ref(v_opts_4262_);
    v_r_4265_ = lean_box((v_res_4264_) as usize);
    return v_r_4265_;
}
pub unsafe fn l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg(
    mut v_x_4266_: *mut LeanObject,
    mut v___y_4267_: *mut LeanObject,
    mut v___y_4268_: *mut LeanObject,
    mut v___y_4269_: *mut LeanObject,
    mut v___y_4270_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4278_: u8 = 0;
    let mut v___x_4279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4283_: u8 = 0;
    let mut v_a_4284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4287_: u8 = 0;
    let mut v___y_4289_: u8 = 0;
    let mut v___x_4290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4293_: u8 = 0;
    let mut v___x_4294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4298_: u8 = 0;
    let mut v_unused_4299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4303_: u8 = 0;
    let mut v___x_4305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4307_: u8 = 0;
    let mut v___x_4309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4311_: u8 = 0;
    let mut v___x_4312_: u8 = 0;
    let mut v_isSharedCheck_4313_: u8 = 0;
    let mut v_a_4314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4317_: u8 = 0;
    let mut v___x_4319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4321_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4272_ = l_Lean_Meta_saveState___redArg(v___y_4268_, v___y_4270_);
                if lean_obj_tag(v___x_4272_) == 0 {
                    v_a_4273_ = lean_ctor_get(v___x_4272_, 0);
                    lean_inc(v_a_4273_);
                    lean_dec_ref_known(v___x_4272_, 1);
                    lean_inc(v___y_4270_);
                    lean_inc_ref(v___y_4269_);
                    lean_inc(v___y_4268_);
                    lean_inc_ref(v___y_4267_);
                    v___x_4274_ = lean_apply_5(
                        v_x_4266_,
                        v___y_4267_,
                        v___y_4268_,
                        v___y_4269_,
                        v___y_4270_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_4274_) == 0 {
                        lean_dec(v_a_4273_);
                        v_a_4275_ = lean_ctor_get(v___x_4274_, 0);
                        v_isSharedCheck_4283_ = (!lean_is_exclusive(v___x_4274_)) as u8;
                        if v_isSharedCheck_4283_ == 0 {
                            v___x_4277_ = v___x_4274_;
                            v_isShared_4278_ = v_isSharedCheck_4283_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_4275_);
                            lean_dec(v___x_4274_);
                            v___x_4277_ = lean_box(0);
                            v_isShared_4278_ = v_isSharedCheck_4283_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4284_ = lean_ctor_get(v___x_4274_, 0);
                        v_isSharedCheck_4313_ = (!lean_is_exclusive(v___x_4274_)) as u8;
                        if v_isSharedCheck_4313_ == 0 {
                            v___x_4286_ = v___x_4274_;
                            v_isShared_4287_ = v_isSharedCheck_4313_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_4284_);
                            lean_dec(v___x_4274_);
                            v___x_4286_ = lean_box(0);
                            v_isShared_4287_ = v_isSharedCheck_4313_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_x_4266_);
                    v_a_4314_ = lean_ctor_get(v___x_4272_, 0);
                    v_isSharedCheck_4321_ = (!lean_is_exclusive(v___x_4272_)) as u8;
                    if v_isSharedCheck_4321_ == 0 {
                        v___x_4316_ = v___x_4272_;
                        v_isShared_4317_ = v_isSharedCheck_4321_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_4314_);
                        lean_dec(v___x_4272_);
                        v___x_4316_ = lean_box(0);
                        v_isShared_4317_ = v_isSharedCheck_4321_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4279_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4279_, 0, v_a_4275_);
                if v_isShared_4278_ == 0 {
                    lean_ctor_set(v___x_4277_, 0, v___x_4279_);
                    v___x_4281_ = v___x_4277_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4282_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4282_, 0, v___x_4279_);
                    v___x_4281_ = v_reuseFailAlloc_4282_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4281_;
            }
            3 => {
                v___x_4311_ = l_Lean_Exception_isInterrupt(v_a_4284_);
                if v___x_4311_ == 0 {
                    lean_inc(v_a_4284_);
                    v___x_4312_ = l_Lean_Exception_isRuntime(v_a_4284_);
                    v___y_4289_ = v___x_4312_;
                    state = 4;
                    continue;
                } else {
                    v___y_4289_ = v___x_4311_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v___y_4289_ == 0 {
                    lean_del_object(v___x_4286_);
                    lean_dec(v_a_4284_);
                    v___x_4290_ = l_Lean_Meta_SavedState_restore___redArg(
                        v_a_4273_,
                        v___y_4268_,
                        v___y_4270_,
                    );
                    lean_dec(v_a_4273_);
                    if lean_obj_tag(v___x_4290_) == 0 {
                        v_isSharedCheck_4298_ = (!lean_is_exclusive(v___x_4290_)) as u8;
                        if v_isSharedCheck_4298_ == 0 {
                            v_unused_4299_ = lean_ctor_get(v___x_4290_, 0);
                            lean_dec(v_unused_4299_);
                            v___x_4292_ = v___x_4290_;
                            v_isShared_4293_ = v_isSharedCheck_4298_;
                            state = 5;
                            continue;
                        } else {
                            lean_dec(v___x_4290_);
                            v___x_4292_ = lean_box(0);
                            v_isShared_4293_ = v_isSharedCheck_4298_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v_a_4300_ = lean_ctor_get(v___x_4290_, 0);
                        v_isSharedCheck_4307_ = (!lean_is_exclusive(v___x_4290_)) as u8;
                        if v_isSharedCheck_4307_ == 0 {
                            v___x_4302_ = v___x_4290_;
                            v_isShared_4303_ = v_isSharedCheck_4307_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_4300_);
                            lean_dec(v___x_4290_);
                            v___x_4302_ = lean_box(0);
                            v_isShared_4303_ = v_isSharedCheck_4307_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_4273_);
                    if v_isShared_4287_ == 0 {
                        v___x_4309_ = v___x_4286_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_4310_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4310_, 0, v_a_4284_);
                        v___x_4309_ = v_reuseFailAlloc_4310_;
                        state = 9;
                        continue;
                    }
                }
            }
            5 => {
                v___x_4294_ = lean_box(0);
                if v_isShared_4293_ == 0 {
                    lean_ctor_set(v___x_4292_, 0, v___x_4294_);
                    v___x_4296_ = v___x_4292_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4297_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4297_, 0, v___x_4294_);
                    v___x_4296_ = v_reuseFailAlloc_4297_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4296_;
            }
            7 => {
                if v_isShared_4303_ == 0 {
                    v___x_4305_ = v___x_4302_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4306_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4306_, 0, v_a_4300_);
                    v___x_4305_ = v_reuseFailAlloc_4306_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4305_;
            }
            9 => {
                return v___x_4309_;
            }
            10 => {
                if v_isShared_4317_ == 0 {
                    v___x_4319_ = v___x_4316_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4320_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4320_, 0, v_a_4314_);
                    v___x_4319_ = v_reuseFailAlloc_4320_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4319_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg___boxed(
    mut v_x_4322_: *mut LeanObject,
    mut v___y_4323_: *mut LeanObject,
    mut v___y_4324_: *mut LeanObject,
    mut v___y_4325_: *mut LeanObject,
    mut v___y_4326_: *mut LeanObject,
    mut v___y_4327_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4328_: *mut LeanObject = core::ptr::null_mut();
    v_res_4328_ = l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg(
        v_x_4322_,
        v___y_4323_,
        v___y_4324_,
        v___y_4325_,
        v___y_4326_,
    );
    lean_dec(v___y_4326_);
    lean_dec_ref(v___y_4325_);
    lean_dec(v___y_4324_);
    lean_dec_ref(v___y_4323_);
    return v_res_4328_;
}
pub unsafe fn l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6(
    mut v_00_u03b1_4329_: *mut LeanObject,
    mut v_x_4330_: *mut LeanObject,
    mut v___y_4331_: *mut LeanObject,
    mut v___y_4332_: *mut LeanObject,
    mut v___y_4333_: *mut LeanObject,
    mut v___y_4334_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4336_: *mut LeanObject = core::ptr::null_mut();
    v___x_4336_ = l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg(
        v_x_4330_,
        v___y_4331_,
        v___y_4332_,
        v___y_4333_,
        v___y_4334_,
    );
    return v___x_4336_;
}
pub unsafe fn l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___boxed(
    mut v_00_u03b1_4337_: *mut LeanObject,
    mut v_x_4338_: *mut LeanObject,
    mut v___y_4339_: *mut LeanObject,
    mut v___y_4340_: *mut LeanObject,
    mut v___y_4341_: *mut LeanObject,
    mut v___y_4342_: *mut LeanObject,
    mut v___y_4343_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4344_: *mut LeanObject = core::ptr::null_mut();
    v_res_4344_ = l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6(
        v_00_u03b1_4337_,
        v_x_4338_,
        v___y_4339_,
        v___y_4340_,
        v___y_4341_,
        v___y_4342_,
    );
    lean_dec(v___y_4342_);
    lean_dec_ref(v___y_4341_);
    lean_dec(v___y_4340_);
    lean_dec_ref(v___y_4339_);
    return v_res_4344_;
}
pub unsafe fn _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__1()
-> *mut LeanObject {
    let mut v___x_4346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4347_: *mut LeanObject = core::ptr::null_mut();
    v___x_4346_ = l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__0;
    v___x_4347_ = l_Lean_stringToMessageData(v___x_4346_);
    return v___x_4347_;
}
pub unsafe fn l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0(
    mut v_e_4348_: *mut LeanObject,
    mut v_x_4349_: *mut LeanObject,
    mut v___y_4350_: *mut LeanObject,
    mut v___y_4351_: *mut LeanObject,
    mut v___y_4352_: *mut LeanObject,
    mut v___y_4353_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4358_: *mut LeanObject = core::ptr::null_mut();
    v___x_4355_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__1_once
        ),
        _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__1,
    );
    v___x_4356_ = l_Lean_MessageData_ofExpr(v_e_4348_);
    v___x_4357_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_4357_, 0, v___x_4355_);
    lean_ctor_set(v___x_4357_, 1, v___x_4356_);
    v___x_4358_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4358_, 0, v___x_4357_);
    return v___x_4358_;
}
pub unsafe fn l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___boxed(
    mut v_e_4359_: *mut LeanObject,
    mut v_x_4360_: *mut LeanObject,
    mut v___y_4361_: *mut LeanObject,
    mut v___y_4362_: *mut LeanObject,
    mut v___y_4363_: *mut LeanObject,
    mut v___y_4364_: *mut LeanObject,
    mut v___y_4365_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4366_: *mut LeanObject = core::ptr::null_mut();
    v_res_4366_ = l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0(
        v_e_4359_,
        v_x_4360_,
        v___y_4361_,
        v___y_4362_,
        v___y_4363_,
        v___y_4364_,
    );
    lean_dec(v___y_4364_);
    lean_dec_ref(v___y_4363_);
    lean_dec(v___y_4362_);
    lean_dec_ref(v___y_4361_);
    lean_dec_ref(v_x_4360_);
    return v_res_4366_;
}
pub unsafe fn l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(
    mut v___x_4367_: u8,
    mut v___x_4368_: u8,
    mut v_x_4369_: *mut LeanObject,
    mut v_x_4370_: *mut LeanObject,
    mut v___y_4371_: *mut LeanObject,
    mut v___y_4372_: *mut LeanObject,
    mut v___y_4373_: *mut LeanObject,
    mut v___y_4374_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4381_: u8 = 0;
    let mut v_a_4383_: u8 = 0;
    let mut v___x_4386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4393_: u8 = 0;
    let mut v___y_4395_: u8 = 0;
    let mut v___x_4397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4399_: u8 = 0;
    let mut v___x_4400_: u8 = 0;
    let mut v_isSharedCheck_4401_: u8 = 0;
    let mut v_isSharedCheck_4402_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4369_) == 0 {
                    v___x_4376_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4376_, 0, v_x_4370_);
                    return v___x_4376_;
                } else {
                    v_head_4377_ = lean_ctor_get(v_x_4369_, 0);
                    v_tail_4378_ = lean_ctor_get(v_x_4369_, 1);
                    v_isSharedCheck_4402_ = (!lean_is_exclusive(v_x_4369_)) as u8;
                    if v_isSharedCheck_4402_ == 0 {
                        v___x_4380_ = v_x_4369_;
                        v_isShared_4381_ = v_isSharedCheck_4402_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_4378_);
                        lean_inc(v_head_4377_);
                        lean_dec(v_x_4369_);
                        v___x_4380_ = lean_box(0);
                        v_isShared_4381_ = v_isSharedCheck_4402_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_head_4377_);
                v___x_4389_ = l_Lean_MVarId_inferInstance(
                    v_head_4377_,
                    v___y_4371_,
                    v___y_4372_,
                    v___y_4373_,
                    v___y_4374_,
                );
                if lean_obj_tag(v___x_4389_) == 0 {
                    lean_dec_ref_known(v___x_4389_, 1);
                    v_a_4383_ = v___x_4367_;
                    state = 2;
                    continue;
                } else {
                    v_a_4390_ = lean_ctor_get(v___x_4389_, 0);
                    v_isSharedCheck_4401_ = (!lean_is_exclusive(v___x_4389_)) as u8;
                    if v_isSharedCheck_4401_ == 0 {
                        v___x_4392_ = v___x_4389_;
                        v_isShared_4393_ = v_isSharedCheck_4401_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_4390_);
                        lean_dec(v___x_4389_);
                        v___x_4392_ = lean_box(0);
                        v_isShared_4393_ = v_isSharedCheck_4401_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_a_4383_ == 0 {
                    lean_del_object(v___x_4380_);
                    lean_dec(v_head_4377_);
                    v_x_4369_ = v_tail_4378_;
                    state = 0;
                    continue;
                } else {
                    if v_isShared_4381_ == 0 {
                        lean_ctor_set(v___x_4380_, 1, v_x_4370_);
                        v___x_4386_ = v___x_4380_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4388_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4388_, 0, v_head_4377_);
                        lean_ctor_set(v_reuseFailAlloc_4388_, 1, v_x_4370_);
                        v___x_4386_ = v_reuseFailAlloc_4388_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v_x_4369_ = v_tail_4378_;
                v_x_4370_ = v___x_4386_;
                state = 0;
                continue;
            }
            4 => {
                v___x_4399_ = l_Lean_Exception_isInterrupt(v_a_4390_);
                if v___x_4399_ == 0 {
                    lean_inc(v_a_4390_);
                    v___x_4400_ = l_Lean_Exception_isRuntime(v_a_4390_);
                    v___y_4395_ = v___x_4400_;
                    state = 5;
                    continue;
                } else {
                    v___y_4395_ = v___x_4399_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v___y_4395_ == 0 {
                    lean_del_object(v___x_4392_);
                    lean_dec(v_a_4390_);
                    v_a_4383_ = v___x_4368_;
                    state = 2;
                    continue;
                } else {
                    lean_del_object(v___x_4380_);
                    lean_dec(v_tail_4378_);
                    lean_dec(v_head_4377_);
                    lean_dec(v_x_4370_);
                    if v_isShared_4393_ == 0 {
                        v___x_4397_ = v___x_4392_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_4398_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4398_, 0, v_a_4390_);
                        v___x_4397_ = v_reuseFailAlloc_4398_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_4397_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3___boxed(
    mut v___x_4403_: *mut LeanObject,
    mut v___x_4404_: *mut LeanObject,
    mut v_x_4405_: *mut LeanObject,
    mut v_x_4406_: *mut LeanObject,
    mut v___y_4407_: *mut LeanObject,
    mut v___y_4408_: *mut LeanObject,
    mut v___y_4409_: *mut LeanObject,
    mut v___y_4410_: *mut LeanObject,
    mut v___y_4411_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_14186__boxed_4412_: u8 = 0;
    let mut v___x_14187__boxed_4413_: u8 = 0;
    let mut v_res_4414_: *mut LeanObject = core::ptr::null_mut();
    v___x_14186__boxed_4412_ = (lean_unbox(v___x_4403_) as u8);
    v___x_14187__boxed_4413_ = (lean_unbox(v___x_4404_) as u8);
    v_res_4414_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(
        v___x_14186__boxed_4412_,
        v___x_14187__boxed_4413_,
        v_x_4405_,
        v_x_4406_,
        v___y_4407_,
        v___y_4408_,
        v___y_4409_,
        v___y_4410_,
    );
    lean_dec(v___y_4410_);
    lean_dec_ref(v___y_4409_);
    lean_dec(v___y_4408_);
    lean_dec_ref(v___y_4407_);
    return v_res_4414_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4___redArg(
    mut v_x_4415_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_4417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4420_: u8 = 0;
    let mut v___x_4422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4424_: u8 = 0;
    let mut v_a_4425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4428_: u8 = 0;
    let mut v___x_4430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4432_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4415_) == 0 {
                    v_a_4417_ = lean_ctor_get(v_x_4415_, 0);
                    v_isSharedCheck_4424_ = (!lean_is_exclusive(v_x_4415_)) as u8;
                    if v_isSharedCheck_4424_ == 0 {
                        v___x_4419_ = v_x_4415_;
                        v_isShared_4420_ = v_isSharedCheck_4424_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4417_);
                        lean_dec(v_x_4415_);
                        v___x_4419_ = lean_box(0);
                        v_isShared_4420_ = v_isSharedCheck_4424_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4425_ = lean_ctor_get(v_x_4415_, 0);
                    v_isSharedCheck_4432_ = (!lean_is_exclusive(v_x_4415_)) as u8;
                    if v_isSharedCheck_4432_ == 0 {
                        v___x_4427_ = v_x_4415_;
                        v_isShared_4428_ = v_isSharedCheck_4432_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4425_);
                        lean_dec(v_x_4415_);
                        v___x_4427_ = lean_box(0);
                        v_isShared_4428_ = v_isSharedCheck_4432_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4420_ == 0 {
                    lean_ctor_set_tag(v___x_4419_, 1);
                    v___x_4422_ = v___x_4419_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4423_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4423_, 0, v_a_4417_);
                    v___x_4422_ = v_reuseFailAlloc_4423_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4422_;
            }
            3 => {
                if v_isShared_4428_ == 0 {
                    lean_ctor_set_tag(v___x_4427_, 0);
                    v___x_4430_ = v___x_4427_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4431_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4431_, 0, v_a_4425_);
                    v___x_4430_ = v_reuseFailAlloc_4431_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4430_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4___redArg___boxed(
    mut v_x_4433_: *mut LeanObject,
    mut v___y_4434_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4435_: *mut LeanObject = core::ptr::null_mut();
    v_res_4435_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4___redArg(v_x_4433_);
    return v_res_4435_;
}
pub unsafe fn l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2(
    mut v_e_4436_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_e_4436_) == 0 {
        let mut v___x_4437_: u8 = 0;
        v___x_4437_ = 2;
        return v___x_4437_;
    } else {
        let mut v___x_4438_: u8 = 0;
        v___x_4438_ = 0;
        return v___x_4438_;
    }
}
pub unsafe fn l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2___boxed(
    mut v_e_4439_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4440_: u8 = 0;
    let mut v_r_4441_: *mut LeanObject = core::ptr::null_mut();
    v_res_4440_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2(v_e_4439_);
    lean_dec_ref(v_e_4439_);
    v_r_4441_ = lean_box((v_res_4440_) as usize);
    return v_r_4441_;
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5(
    mut v_opts_4442_: *mut LeanObject,
    mut v_opt_4443_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_4444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_4445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_4446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4447_: *mut LeanObject = core::ptr::null_mut();
    v_name_4444_ = lean_ctor_get(v_opt_4443_, 0);
    v_defValue_4445_ = lean_ctor_get(v_opt_4443_, 1);
    v_map_4446_ = lean_ctor_get(v_opts_4442_, 0);
    v___x_4447_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_4446_,
            v_name_4444_,
        );
    if lean_obj_tag(v___x_4447_) == 0 {
        lean_inc(v_defValue_4445_);
        return v_defValue_4445_;
    } else {
        let mut v_val_4448_: *mut LeanObject = core::ptr::null_mut();
        v_val_4448_ = lean_ctor_get(v___x_4447_, 0);
        lean_inc(v_val_4448_);
        lean_dec_ref_known(v___x_4447_, 1);
        if lean_obj_tag(v_val_4448_) == 3 {
            let mut v_v_4449_: *mut LeanObject = core::ptr::null_mut();
            v_v_4449_ = lean_ctor_get(v_val_4448_, 0);
            lean_inc(v_v_4449_);
            lean_dec_ref_known(v_val_4448_, 1);
            return v_v_4449_;
        } else {
            lean_dec(v_val_4448_);
            lean_inc(v_defValue_4445_);
            return v_defValue_4445_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5___boxed(
    mut v_opts_4450_: *mut LeanObject,
    mut v_opt_4451_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4452_: *mut LeanObject = core::ptr::null_mut();
    v_res_4452_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5(v_opts_4450_, v_opt_4451_);
    lean_dec_ref(v_opt_4451_);
    lean_dec_ref(v_opts_4450_);
    return v_res_4452_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3_spec__5(
    mut v_sz_4453_: usize,
    mut v_i_4454_: usize,
    mut v_bs_4455_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4456_: u8 = 0;
    let mut v_v_4457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msg_4458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4461_: usize = 0;
    let mut v___x_4462_: usize = 0;
    let mut v___x_4463_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4456_ = lean_usize_dec_lt(v_i_4454_, v_sz_4453_);
                if v___x_4456_ == 0 {
                    return v_bs_4455_;
                } else {
                    v_v_4457_ = lean_array_uget_borrowed(v_bs_4455_, v_i_4454_);
                    v_msg_4458_ = lean_ctor_get(v_v_4457_, 1);
                    lean_inc_ref(v_msg_4458_);
                    v___x_4459_ = lean_unsigned_to_nat(0);
                    v_bs_x27_4460_ = lean_array_uset(v_bs_4455_, v_i_4454_, v___x_4459_);
                    v___x_4461_ = 1usize;
                    v___x_4462_ = lean_usize_add(v_i_4454_, v___x_4461_);
                    v___x_4463_ = lean_array_uset(v_bs_x27_4460_, v_i_4454_, v_msg_4458_);
                    v_i_4454_ = v___x_4462_;
                    v_bs_4455_ = v___x_4463_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3_spec__5___boxed(
    mut v_sz_4465_: *mut LeanObject,
    mut v_i_4466_: *mut LeanObject,
    mut v_bs_4467_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4468_: usize = 0;
    let mut v_i_boxed_4469_: usize = 0;
    let mut v_res_4470_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4468_ = lean_unbox_usize(v_sz_4465_);
    lean_dec(v_sz_4465_);
    v_i_boxed_4469_ = lean_unbox_usize(v_i_4466_);
    lean_dec(v_i_4466_);
    v_res_4470_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3_spec__5(v_sz_boxed_4468_, v_i_boxed_4469_, v_bs_4467_);
    return v_res_4470_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3_spec__6(
    mut v_msgData_4471_: *mut LeanObject,
    mut v___y_4472_: *mut LeanObject,
    mut v___y_4473_: *mut LeanObject,
    mut v___y_4474_: *mut LeanObject,
    mut v___y_4475_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_4480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_4481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4485_: *mut LeanObject = core::ptr::null_mut();
    v___x_4477_ = lean_st_ref_get(v___y_4475_);
    v_env_4478_ = lean_ctor_get(v___x_4477_, 0);
    lean_inc_ref(v_env_4478_);
    lean_dec(v___x_4477_);
    v___x_4479_ = lean_st_ref_get(v___y_4473_);
    v_mctx_4480_ = lean_ctor_get(v___x_4479_, 0);
    lean_inc_ref(v_mctx_4480_);
    lean_dec(v___x_4479_);
    v_lctx_4481_ = lean_ctor_get(v___y_4472_, 2);
    v_options_4482_ = lean_ctor_get(v___y_4474_, 2);
    lean_inc_ref(v_options_4482_);
    lean_inc_ref(v_lctx_4481_);
    v___x_4483_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_4483_, 0, v_env_4478_);
    lean_ctor_set(v___x_4483_, 1, v_mctx_4480_);
    lean_ctor_set(v___x_4483_, 2, v_lctx_4481_);
    lean_ctor_set(v___x_4483_, 3, v_options_4482_);
    v___x_4484_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_4484_, 0, v___x_4483_);
    lean_ctor_set(v___x_4484_, 1, v_msgData_4471_);
    v___x_4485_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4485_, 0, v___x_4484_);
    return v___x_4485_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3_spec__6___boxed(
    mut v_msgData_4486_: *mut LeanObject,
    mut v___y_4487_: *mut LeanObject,
    mut v___y_4488_: *mut LeanObject,
    mut v___y_4489_: *mut LeanObject,
    mut v___y_4490_: *mut LeanObject,
    mut v___y_4491_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4492_: *mut LeanObject = core::ptr::null_mut();
    v_res_4492_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3_spec__6(v_msgData_4486_, v___y_4487_, v___y_4488_, v___y_4489_, v___y_4490_);
    lean_dec(v___y_4490_);
    lean_dec_ref(v___y_4489_);
    lean_dec(v___y_4488_);
    lean_dec_ref(v___y_4487_);
    return v_res_4492_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3(
    mut v_oldTraces_4493_: *mut LeanObject,
    mut v_data_4494_: *mut LeanObject,
    mut v_ref_4495_: *mut LeanObject,
    mut v_msg_4496_: *mut LeanObject,
    mut v___y_4497_: *mut LeanObject,
    mut v___y_4498_: *mut LeanObject,
    mut v___y_4499_: *mut LeanObject,
    mut v___y_4500_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_4502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_4506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_4510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_4511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_4514_: u8 = 0;
    let mut v_cancelTk_x3f_4515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4516_: u8 = 0;
    let mut v_inheritedTraceOptions_4517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_4519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traces_4520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_4524_: usize = 0;
    let mut v___x_4525_: usize = 0;
    let mut v___x_4526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msg_4527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4532_: u8 = 0;
    let mut v___x_4533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_4534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_4537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_4539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_4540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_4541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4545_: u8 = 0;
    let mut v_tid_4546_: u64 = 0;
    let mut v___x_4548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4549_: u8 = 0;
    let mut v___x_4550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4563_: u8 = 0;
    let mut v_unused_4564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4565_: u8 = 0;
    let mut v_isSharedCheck_4566_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_4502_ = lean_ctor_get(v___y_4499_, 0);
                v_fileMap_4503_ = lean_ctor_get(v___y_4499_, 1);
                v_options_4504_ = lean_ctor_get(v___y_4499_, 2);
                v_currRecDepth_4505_ = lean_ctor_get(v___y_4499_, 3);
                v_maxRecDepth_4506_ = lean_ctor_get(v___y_4499_, 4);
                v_ref_4507_ = lean_ctor_get(v___y_4499_, 5);
                v_currNamespace_4508_ = lean_ctor_get(v___y_4499_, 6);
                v_openDecls_4509_ = lean_ctor_get(v___y_4499_, 7);
                v_initHeartbeats_4510_ = lean_ctor_get(v___y_4499_, 8);
                v_maxHeartbeats_4511_ = lean_ctor_get(v___y_4499_, 9);
                v_quotContext_4512_ = lean_ctor_get(v___y_4499_, 10);
                v_currMacroScope_4513_ = lean_ctor_get(v___y_4499_, 11);
                v_diag_4514_ = lean_ctor_get_uint8(
                    v___y_4499_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_4515_ = lean_ctor_get(v___y_4499_, 12);
                v_suppressElabErrors_4516_ = lean_ctor_get_uint8(
                    v___y_4499_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_4517_ = lean_ctor_get(v___y_4499_, 13);
                v___x_4518_ = lean_st_ref_get(v___y_4500_);
                v_traceState_4519_ = lean_ctor_get(v___x_4518_, 4);
                lean_inc_ref(v_traceState_4519_);
                lean_dec(v___x_4518_);
                v_traces_4520_ = lean_ctor_get(v_traceState_4519_, 0);
                lean_inc_ref(v_traces_4520_);
                lean_dec_ref(v_traceState_4519_);
                v_ref_4521_ = l_Lean_replaceRef(v_ref_4495_, v_ref_4507_);
                lean_inc_ref(v_inheritedTraceOptions_4517_);
                lean_inc(v_cancelTk_x3f_4515_);
                lean_inc(v_currMacroScope_4513_);
                lean_inc(v_quotContext_4512_);
                lean_inc(v_maxHeartbeats_4511_);
                lean_inc(v_initHeartbeats_4510_);
                lean_inc(v_openDecls_4509_);
                lean_inc(v_currNamespace_4508_);
                lean_inc(v_maxRecDepth_4506_);
                lean_inc(v_currRecDepth_4505_);
                lean_inc_ref(v_options_4504_);
                lean_inc_ref(v_fileMap_4503_);
                lean_inc_ref(v_fileName_4502_);
                v___x_4522_ = lean_alloc_ctor(0, 14, (2) as u32);
                lean_ctor_set(v___x_4522_, 0, v_fileName_4502_);
                lean_ctor_set(v___x_4522_, 1, v_fileMap_4503_);
                lean_ctor_set(v___x_4522_, 2, v_options_4504_);
                lean_ctor_set(v___x_4522_, 3, v_currRecDepth_4505_);
                lean_ctor_set(v___x_4522_, 4, v_maxRecDepth_4506_);
                lean_ctor_set(v___x_4522_, 5, v_ref_4521_);
                lean_ctor_set(v___x_4522_, 6, v_currNamespace_4508_);
                lean_ctor_set(v___x_4522_, 7, v_openDecls_4509_);
                lean_ctor_set(v___x_4522_, 8, v_initHeartbeats_4510_);
                lean_ctor_set(v___x_4522_, 9, v_maxHeartbeats_4511_);
                lean_ctor_set(v___x_4522_, 10, v_quotContext_4512_);
                lean_ctor_set(v___x_4522_, 11, v_currMacroScope_4513_);
                lean_ctor_set(v___x_4522_, 12, v_cancelTk_x3f_4515_);
                lean_ctor_set(v___x_4522_, 13, v_inheritedTraceOptions_4517_);
                lean_ctor_set_uint8(
                    v___x_4522_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    v_diag_4514_,
                );
                lean_ctor_set_uint8(
                    v___x_4522_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_4516_,
                );
                v___x_4523_ = l_Lean_PersistentArray_toArray___redArg(v_traces_4520_);
                lean_dec_ref(v_traces_4520_);
                v_sz_4524_ = lean_array_size(v___x_4523_);
                v___x_4525_ = 0usize;
                v___x_4526_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3_spec__5(v_sz_4524_, v___x_4525_, v___x_4523_);
                v_msg_4527_ = lean_alloc_ctor(9, 3, (0) as u32);
                lean_ctor_set(v_msg_4527_, 0, v_data_4494_);
                lean_ctor_set(v_msg_4527_, 1, v_msg_4496_);
                lean_ctor_set(v_msg_4527_, 2, v___x_4526_);
                v___x_4528_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3_spec__6(v_msg_4527_, v___y_4497_, v___y_4498_, v___x_4522_, v___y_4500_);
                lean_dec_ref_known(v___x_4522_, 14);
                v_a_4529_ = lean_ctor_get(v___x_4528_, 0);
                v_isSharedCheck_4566_ = (!lean_is_exclusive(v___x_4528_)) as u8;
                if v_isSharedCheck_4566_ == 0 {
                    v___x_4531_ = v___x_4528_;
                    v_isShared_4532_ = v_isSharedCheck_4566_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_4529_);
                    lean_dec(v___x_4528_);
                    v___x_4531_ = lean_box(0);
                    v_isShared_4532_ = v_isSharedCheck_4566_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4533_ = lean_st_ref_take(v___y_4500_);
                v_traceState_4534_ = lean_ctor_get(v___x_4533_, 4);
                v_env_4535_ = lean_ctor_get(v___x_4533_, 0);
                v_nextMacroScope_4536_ = lean_ctor_get(v___x_4533_, 1);
                v_ngen_4537_ = lean_ctor_get(v___x_4533_, 2);
                v_auxDeclNGen_4538_ = lean_ctor_get(v___x_4533_, 3);
                v_cache_4539_ = lean_ctor_get(v___x_4533_, 5);
                v_messages_4540_ = lean_ctor_get(v___x_4533_, 6);
                v_infoState_4541_ = lean_ctor_get(v___x_4533_, 7);
                v_snapshotTasks_4542_ = lean_ctor_get(v___x_4533_, 8);
                v_isSharedCheck_4565_ = (!lean_is_exclusive(v___x_4533_)) as u8;
                if v_isSharedCheck_4565_ == 0 {
                    v___x_4544_ = v___x_4533_;
                    v_isShared_4545_ = v_isSharedCheck_4565_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_4542_);
                    lean_inc(v_infoState_4541_);
                    lean_inc(v_messages_4540_);
                    lean_inc(v_cache_4539_);
                    lean_inc(v_traceState_4534_);
                    lean_inc(v_auxDeclNGen_4538_);
                    lean_inc(v_ngen_4537_);
                    lean_inc(v_nextMacroScope_4536_);
                    lean_inc(v_env_4535_);
                    lean_dec(v___x_4533_);
                    v___x_4544_ = lean_box(0);
                    v_isShared_4545_ = v_isSharedCheck_4565_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_4546_ = lean_ctor_get_uint64(
                    v_traceState_4534_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_4563_ = (!lean_is_exclusive(v_traceState_4534_)) as u8;
                if v_isSharedCheck_4563_ == 0 {
                    v_unused_4564_ = lean_ctor_get(v_traceState_4534_, 0);
                    lean_dec(v_unused_4564_);
                    v___x_4548_ = v_traceState_4534_;
                    v_isShared_4549_ = v_isSharedCheck_4563_;
                    state = 3;
                    continue;
                } else {
                    lean_dec(v_traceState_4534_);
                    v___x_4548_ = lean_box(0);
                    v_isShared_4549_ = v_isSharedCheck_4563_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4550_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4550_, 0, v_ref_4495_);
                lean_ctor_set(v___x_4550_, 1, v_a_4529_);
                v___x_4551_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_4493_, v___x_4550_);
                if v_isShared_4549_ == 0 {
                    lean_ctor_set(v___x_4548_, 0, v___x_4551_);
                    v___x_4553_ = v___x_4548_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4562_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4562_, 0, v___x_4551_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_4562_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_4546_,
                    );
                    v___x_4553_ = v_reuseFailAlloc_4562_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4545_ == 0 {
                    lean_ctor_set(v___x_4544_, 4, v___x_4553_);
                    v___x_4555_ = v___x_4544_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4561_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4561_, 0, v_env_4535_);
                    lean_ctor_set(v_reuseFailAlloc_4561_, 1, v_nextMacroScope_4536_);
                    lean_ctor_set(v_reuseFailAlloc_4561_, 2, v_ngen_4537_);
                    lean_ctor_set(v_reuseFailAlloc_4561_, 3, v_auxDeclNGen_4538_);
                    lean_ctor_set(v_reuseFailAlloc_4561_, 4, v___x_4553_);
                    lean_ctor_set(v_reuseFailAlloc_4561_, 5, v_cache_4539_);
                    lean_ctor_set(v_reuseFailAlloc_4561_, 6, v_messages_4540_);
                    lean_ctor_set(v_reuseFailAlloc_4561_, 7, v_infoState_4541_);
                    lean_ctor_set(v_reuseFailAlloc_4561_, 8, v_snapshotTasks_4542_);
                    v___x_4555_ = v_reuseFailAlloc_4561_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4556_ = lean_st_ref_set(v___y_4500_, v___x_4555_);
                v___x_4557_ = lean_box(0);
                if v_isShared_4532_ == 0 {
                    lean_ctor_set(v___x_4531_, 0, v___x_4557_);
                    v___x_4559_ = v___x_4531_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4560_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4560_, 0, v___x_4557_);
                    v___x_4559_ = v_reuseFailAlloc_4560_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4559_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___boxed(
    mut v_oldTraces_4567_: *mut LeanObject,
    mut v_data_4568_: *mut LeanObject,
    mut v_ref_4569_: *mut LeanObject,
    mut v_msg_4570_: *mut LeanObject,
    mut v___y_4571_: *mut LeanObject,
    mut v___y_4572_: *mut LeanObject,
    mut v___y_4573_: *mut LeanObject,
    mut v___y_4574_: *mut LeanObject,
    mut v___y_4575_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4576_: *mut LeanObject = core::ptr::null_mut();
    v_res_4576_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3(v_oldTraces_4567_, v_data_4568_, v_ref_4569_, v_msg_4570_, v___y_4571_, v___y_4572_, v___y_4573_, v___y_4574_);
    lean_dec(v___y_4574_);
    lean_dec_ref(v___y_4573_);
    lean_dec(v___y_4572_);
    lean_dec_ref(v___y_4571_);
    return v_res_4576_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__1()
-> *mut LeanObject {
    let mut v___x_4578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4579_: *mut LeanObject = core::ptr::null_mut();
    v___x_4578_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__0;
    v___x_4579_ = l_Lean_stringToMessageData(v___x_4578_);
    return v___x_4579_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__2()
-> f64 {
    let mut v___x_4580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4581_: f64 = 0.0;
    v___x_4580_ = lean_unsigned_to_nat(0);
    v___x_4581_ = lean_float_of_nat(v___x_4580_);
    return v___x_4581_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__4()
-> *mut LeanObject {
    let mut v___x_4583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4584_: *mut LeanObject = core::ptr::null_mut();
    v___x_4583_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__3;
    v___x_4584_ = l_Lean_stringToMessageData(v___x_4583_);
    return v___x_4584_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__5()
-> f64 {
    let mut v___x_4585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4586_: f64 = 0.0;
    v___x_4585_ = lean_unsigned_to_nat(1000);
    v___x_4586_ = lean_float_of_nat(v___x_4585_);
    return v___x_4586_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(
    mut v_cls_4587_: *mut LeanObject,
    mut v_collapsed_4588_: u8,
    mut v_tag_4589_: *mut LeanObject,
    mut v_opts_4590_: *mut LeanObject,
    mut v_clsEnabled_4591_: u8,
    mut v_oldTraces_4592_: *mut LeanObject,
    mut v_msg_4593_: *mut LeanObject,
    mut v_resStartStop_4594_: *mut LeanObject,
    mut v___y_4595_: *mut LeanObject,
    mut v___y_4596_: *mut LeanObject,
    mut v___y_4597_: *mut LeanObject,
    mut v___y_4598_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_4600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4604_: u8 = 0;
    let mut v___y_4606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_4608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4614_: u8 = 0;
    let mut v___x_4616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4618_: u8 = 0;
    let mut v_fst_4619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4623_: u8 = 0;
    let mut v___x_4624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4625_: u8 = 0;
    let mut v___y_4627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_result_4629_: u8 = 0;
    let mut v___x_4630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_m_4636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4639_: f64 = 0.0;
    let mut v_data_4640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_4641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4642_: f64 = 0.0;
    let mut v___x_4643_: f64 = 0.0;
    let mut v_reuseFailAlloc_4644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4652_: u8 = 0;
    let mut v___x_4653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_4654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_4657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_4659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_4660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_4661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4665_: u8 = 0;
    let mut v_tid_4666_: u64 = 0;
    let mut v_traces_4667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4670_: u8 = 0;
    let mut v___x_4671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4680_: u8 = 0;
    let mut v_isSharedCheck_4681_: u8 = 0;
    let mut v___y_4683_: f64 = 0.0;
    let mut v___x_4684_: f64 = 0.0;
    let mut v___x_4685_: f64 = 0.0;
    let mut v___x_4686_: f64 = 0.0;
    let mut v___x_4687_: u8 = 0;
    let mut v___x_4688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4689_: u8 = 0;
    let mut v___x_4690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4692_: f64 = 0.0;
    let mut v___x_4693_: f64 = 0.0;
    let mut v___x_4694_: f64 = 0.0;
    let mut v___x_4695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4697_: f64 = 0.0;
    let mut v_isSharedCheck_4698_: u8 = 0;
    let mut v_isSharedCheck_4699_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_4600_ = lean_ctor_get(v_resStartStop_4594_, 0);
                v_snd_4601_ = lean_ctor_get(v_resStartStop_4594_, 1);
                v_isSharedCheck_4699_ = (!lean_is_exclusive(v_resStartStop_4594_)) as u8;
                if v_isSharedCheck_4699_ == 0 {
                    v___x_4603_ = v_resStartStop_4594_;
                    v_isShared_4604_ = v_isSharedCheck_4699_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_4601_);
                    lean_inc(v_fst_4600_);
                    lean_dec(v_resStartStop_4594_);
                    v___x_4603_ = lean_box(0);
                    v_isShared_4604_ = v_isSharedCheck_4699_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_4619_ = lean_ctor_get(v_snd_4601_, 0);
                v_snd_4620_ = lean_ctor_get(v_snd_4601_, 1);
                v_isSharedCheck_4698_ = (!lean_is_exclusive(v_snd_4601_)) as u8;
                if v_isSharedCheck_4698_ == 0 {
                    v___x_4622_ = v_snd_4601_;
                    v_isShared_4623_ = v_isSharedCheck_4698_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_snd_4620_);
                    lean_inc(v_fst_4619_);
                    lean_dec(v_snd_4601_);
                    v___x_4622_ = lean_box(0);
                    v_isShared_4623_ = v_isSharedCheck_4698_;
                    state = 5;
                    continue;
                }
            }
            2 => {
                lean_inc(v___y_4607_);
                v___x_4609_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3(v_oldTraces_4592_, v_data_4608_, v___y_4607_, v___y_4606_, v___y_4595_, v___y_4596_, v___y_4597_, v___y_4598_);
                if lean_obj_tag(v___x_4609_) == 0 {
                    lean_dec_ref_known(v___x_4609_, 1);
                    v___x_4610_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4___redArg(v_fst_4600_);
                    return v___x_4610_;
                } else {
                    lean_dec(v_fst_4600_);
                    v_a_4611_ = lean_ctor_get(v___x_4609_, 0);
                    v_isSharedCheck_4618_ = (!lean_is_exclusive(v___x_4609_)) as u8;
                    if v_isSharedCheck_4618_ == 0 {
                        v___x_4613_ = v___x_4609_;
                        v_isShared_4614_ = v_isSharedCheck_4618_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4611_);
                        lean_dec(v___x_4609_);
                        v___x_4613_ = lean_box(0);
                        v_isShared_4614_ = v_isSharedCheck_4618_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_4614_ == 0 {
                    v___x_4616_ = v___x_4613_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4617_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4617_, 0, v_a_4611_);
                    v___x_4616_ = v_reuseFailAlloc_4617_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4616_;
            }
            5 => {
                v___x_4624_ = l_Lean_trace_profiler;
                v___x_4625_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(
                    v_opts_4590_,
                    v___x_4624_,
                );
                if v___x_4625_ == 0 {
                    v___y_4652_ = v___x_4625_;
                    state = 10;
                    continue;
                } else {
                    v___x_4688_ = l_Lean_trace_profiler_useHeartbeats;
                    v___x_4689_ =
                        l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(
                            v_opts_4590_,
                            v___x_4688_,
                        );
                    if v___x_4689_ == 0 {
                        v___x_4690_ = l_Lean_trace_profiler_threshold;
                        v___x_4691_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5(v_opts_4590_, v___x_4690_);
                        v___x_4692_ = lean_float_of_nat(v___x_4691_);
                        v___x_4693_ = lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__5_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__5);
                        v___x_4694_ = lean_float_div(v___x_4692_, v___x_4693_);
                        v___y_4683_ = v___x_4694_;
                        state = 15;
                        continue;
                    } else {
                        v___x_4695_ = l_Lean_trace_profiler_threshold;
                        v___x_4696_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5(v_opts_4590_, v___x_4695_);
                        v___x_4697_ = lean_float_of_nat(v___x_4696_);
                        v___y_4683_ = v___x_4697_;
                        state = 15;
                        continue;
                    }
                }
            }
            6 => {
                v_result_4629_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2(v_fst_4600_);
                v___x_4630_ = l_Lean_TraceResult_toEmoji(v_result_4629_);
                v___x_4631_ = l_Lean_stringToMessageData(v___x_4630_);
                v___x_4632_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__1_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__1);
                if v_isShared_4623_ == 0 {
                    lean_ctor_set_tag(v___x_4622_, 7);
                    lean_ctor_set(v___x_4622_, 1, v___x_4632_);
                    lean_ctor_set(v___x_4622_, 0, v___x_4631_);
                    v___x_4634_ = v___x_4622_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4645_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4645_, 0, v___x_4631_);
                    lean_ctor_set(v_reuseFailAlloc_4645_, 1, v___x_4632_);
                    v___x_4634_ = v_reuseFailAlloc_4645_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_4604_ == 0 {
                    lean_ctor_set_tag(v___x_4603_, 7);
                    lean_ctor_set(v___x_4603_, 1, v_a_4628_);
                    lean_ctor_set(v___x_4603_, 0, v___x_4634_);
                    v_m_4636_ = v___x_4603_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4644_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4644_, 0, v___x_4634_);
                    lean_ctor_set(v_reuseFailAlloc_4644_, 1, v_a_4628_);
                    v_m_4636_ = v_reuseFailAlloc_4644_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_4637_ = lean_box((v_result_4629_) as usize);
                v___x_4638_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4638_, 0, v___x_4637_);
                v___x_4639_ = lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__2_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__2);
                lean_inc_ref(v_tag_4589_);
                lean_inc_ref(v___x_4638_);
                lean_inc(v_cls_4587_);
                v_data_4640_ = lean_alloc_ctor(0, 3, (17) as u32);
                lean_ctor_set(v_data_4640_, 0, v_cls_4587_);
                lean_ctor_set(v_data_4640_, 1, v___x_4638_);
                lean_ctor_set(v_data_4640_, 2, v_tag_4589_);
                lean_ctor_set_float(
                    v_data_4640_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_4639_,
                );
                lean_ctor_set_float(
                    v_data_4640_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    v___x_4639_,
                );
                lean_ctor_set_uint8(
                    v_data_4640_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                    v_collapsed_4588_,
                );
                if v___x_4625_ == 0 {
                    lean_dec_ref_known(v___x_4638_, 1);
                    lean_dec(v_snd_4620_);
                    lean_dec(v_fst_4619_);
                    lean_dec_ref(v_tag_4589_);
                    lean_dec(v_cls_4587_);
                    v___y_4606_ = v_m_4636_;
                    v___y_4607_ = v___y_4627_;
                    v_data_4608_ = v_data_4640_;
                    state = 2;
                    continue;
                } else {
                    lean_dec_ref_known(v_data_4640_, 3);
                    v_data_4641_ = lean_alloc_ctor(0, 3, (17) as u32);
                    lean_ctor_set(v_data_4641_, 0, v_cls_4587_);
                    lean_ctor_set(v_data_4641_, 1, v___x_4638_);
                    lean_ctor_set(v_data_4641_, 2, v_tag_4589_);
                    v___x_4642_ = lean_unbox_float(v_fst_4619_);
                    lean_dec(v_fst_4619_);
                    lean_ctor_set_float(
                        v_data_4641_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v___x_4642_,
                    );
                    v___x_4643_ = lean_unbox_float(v_snd_4620_);
                    lean_dec(v_snd_4620_);
                    lean_ctor_set_float(
                        v_data_4641_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                        v___x_4643_,
                    );
                    lean_ctor_set_uint8(
                        v_data_4641_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                        v_collapsed_4588_,
                    );
                    v___y_4606_ = v_m_4636_;
                    v___y_4607_ = v___y_4627_;
                    v_data_4608_ = v_data_4641_;
                    state = 2;
                    continue;
                }
            }
            9 => {
                v_ref_4647_ = lean_ctor_get(v___y_4597_, 5);
                lean_inc(v___y_4598_);
                lean_inc_ref(v___y_4597_);
                lean_inc(v___y_4596_);
                lean_inc_ref(v___y_4595_);
                lean_inc(v_fst_4600_);
                v___x_4648_ = lean_apply_6(
                    v_msg_4593_,
                    v_fst_4600_,
                    v___y_4595_,
                    v___y_4596_,
                    v___y_4597_,
                    v___y_4598_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_4648_) == 0 {
                    v_a_4649_ = lean_ctor_get(v___x_4648_, 0);
                    lean_inc(v_a_4649_);
                    lean_dec_ref_known(v___x_4648_, 1);
                    v___y_4627_ = v_ref_4647_;
                    v_a_4628_ = v_a_4649_;
                    state = 6;
                    continue;
                } else {
                    lean_dec_ref_known(v___x_4648_, 1);
                    v___x_4650_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__4_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__4);
                    v___y_4627_ = v_ref_4647_;
                    v_a_4628_ = v___x_4650_;
                    state = 6;
                    continue;
                }
            }
            10 => {
                if v_clsEnabled_4591_ == 0 {
                    if v___y_4652_ == 0 {
                        lean_del_object(v___x_4622_);
                        lean_dec(v_snd_4620_);
                        lean_dec(v_fst_4619_);
                        lean_del_object(v___x_4603_);
                        lean_dec_ref(v_msg_4593_);
                        lean_dec_ref(v_tag_4589_);
                        lean_dec(v_cls_4587_);
                        v___x_4653_ = lean_st_ref_take(v___y_4598_);
                        v_traceState_4654_ = lean_ctor_get(v___x_4653_, 4);
                        v_env_4655_ = lean_ctor_get(v___x_4653_, 0);
                        v_nextMacroScope_4656_ = lean_ctor_get(v___x_4653_, 1);
                        v_ngen_4657_ = lean_ctor_get(v___x_4653_, 2);
                        v_auxDeclNGen_4658_ = lean_ctor_get(v___x_4653_, 3);
                        v_cache_4659_ = lean_ctor_get(v___x_4653_, 5);
                        v_messages_4660_ = lean_ctor_get(v___x_4653_, 6);
                        v_infoState_4661_ = lean_ctor_get(v___x_4653_, 7);
                        v_snapshotTasks_4662_ = lean_ctor_get(v___x_4653_, 8);
                        v_isSharedCheck_4681_ = (!lean_is_exclusive(v___x_4653_)) as u8;
                        if v_isSharedCheck_4681_ == 0 {
                            v___x_4664_ = v___x_4653_;
                            v_isShared_4665_ = v_isSharedCheck_4681_;
                            state = 11;
                            continue;
                        } else {
                            lean_inc(v_snapshotTasks_4662_);
                            lean_inc(v_infoState_4661_);
                            lean_inc(v_messages_4660_);
                            lean_inc(v_cache_4659_);
                            lean_inc(v_traceState_4654_);
                            lean_inc(v_auxDeclNGen_4658_);
                            lean_inc(v_ngen_4657_);
                            lean_inc(v_nextMacroScope_4656_);
                            lean_inc(v_env_4655_);
                            lean_dec(v___x_4653_);
                            v___x_4664_ = lean_box(0);
                            v_isShared_4665_ = v_isSharedCheck_4681_;
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
                v_tid_4666_ = lean_ctor_get_uint64(
                    v_traceState_4654_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_traces_4667_ = lean_ctor_get(v_traceState_4654_, 0);
                v_isSharedCheck_4680_ = (!lean_is_exclusive(v_traceState_4654_)) as u8;
                if v_isSharedCheck_4680_ == 0 {
                    v___x_4669_ = v_traceState_4654_;
                    v_isShared_4670_ = v_isSharedCheck_4680_;
                    state = 12;
                    continue;
                } else {
                    lean_inc(v_traces_4667_);
                    lean_dec(v_traceState_4654_);
                    v___x_4669_ = lean_box(0);
                    v_isShared_4670_ = v_isSharedCheck_4680_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_4671_ =
                    l_Lean_PersistentArray_append___redArg(v_oldTraces_4592_, v_traces_4667_);
                lean_dec_ref(v_traces_4667_);
                if v_isShared_4670_ == 0 {
                    lean_ctor_set(v___x_4669_, 0, v___x_4671_);
                    v___x_4673_ = v___x_4669_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4679_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4679_, 0, v___x_4671_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_4679_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_4666_,
                    );
                    v___x_4673_ = v_reuseFailAlloc_4679_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_4665_ == 0 {
                    lean_ctor_set(v___x_4664_, 4, v___x_4673_);
                    v___x_4675_ = v___x_4664_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4678_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4678_, 0, v_env_4655_);
                    lean_ctor_set(v_reuseFailAlloc_4678_, 1, v_nextMacroScope_4656_);
                    lean_ctor_set(v_reuseFailAlloc_4678_, 2, v_ngen_4657_);
                    lean_ctor_set(v_reuseFailAlloc_4678_, 3, v_auxDeclNGen_4658_);
                    lean_ctor_set(v_reuseFailAlloc_4678_, 4, v___x_4673_);
                    lean_ctor_set(v_reuseFailAlloc_4678_, 5, v_cache_4659_);
                    lean_ctor_set(v_reuseFailAlloc_4678_, 6, v_messages_4660_);
                    lean_ctor_set(v_reuseFailAlloc_4678_, 7, v_infoState_4661_);
                    lean_ctor_set(v_reuseFailAlloc_4678_, 8, v_snapshotTasks_4662_);
                    v___x_4675_ = v_reuseFailAlloc_4678_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_4676_ = lean_st_ref_set(v___y_4598_, v___x_4675_);
                v___x_4677_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4___redArg(v_fst_4600_);
                return v___x_4677_;
            }
            15 => {
                v___x_4684_ = lean_unbox_float(v_snd_4620_);
                v___x_4685_ = lean_unbox_float(v_fst_4619_);
                v___x_4686_ = lean_float_sub(v___x_4684_, v___x_4685_);
                v___x_4687_ = lean_float_decLt(v___y_4683_, v___x_4686_);
                v___y_4652_ = v___x_4687_;
                state = 10;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___boxed(
    mut v_cls_4700_: *mut LeanObject,
    mut v_collapsed_4701_: *mut LeanObject,
    mut v_tag_4702_: *mut LeanObject,
    mut v_opts_4703_: *mut LeanObject,
    mut v_clsEnabled_4704_: *mut LeanObject,
    mut v_oldTraces_4705_: *mut LeanObject,
    mut v_msg_4706_: *mut LeanObject,
    mut v_resStartStop_4707_: *mut LeanObject,
    mut v___y_4708_: *mut LeanObject,
    mut v___y_4709_: *mut LeanObject,
    mut v___y_4710_: *mut LeanObject,
    mut v___y_4711_: *mut LeanObject,
    mut v___y_4712_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_collapsed_boxed_4713_: u8 = 0;
    let mut v_clsEnabled_boxed_4714_: u8 = 0;
    let mut v_res_4715_: *mut LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_4713_ = (lean_unbox(v_collapsed_4701_) as u8);
    v_clsEnabled_boxed_4714_ = (lean_unbox(v_clsEnabled_4704_) as u8);
    v_res_4715_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v_cls_4700_, v_collapsed_boxed_4713_, v_tag_4702_, v_opts_4703_, v_clsEnabled_boxed_4714_, v_oldTraces_4705_, v_msg_4706_, v_resStartStop_4707_, v___y_4708_, v___y_4709_, v___y_4710_, v___y_4711_);
    lean_dec(v___y_4711_);
    lean_dec_ref(v___y_4710_);
    lean_dec(v___y_4709_);
    lean_dec_ref(v___y_4708_);
    lean_dec_ref(v_opts_4703_);
    return v_res_4715_;
}
pub unsafe fn l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__4(
    mut v___x_4716_: u8,
    mut v_x_4717_: *mut LeanObject,
    mut v_x_4718_: *mut LeanObject,
    mut v___y_4719_: *mut LeanObject,
    mut v___y_4720_: *mut LeanObject,
    mut v___y_4721_: *mut LeanObject,
    mut v___y_4722_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4729_: u8 = 0;
    let mut v___x_4730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4735_: u8 = 0;
    let mut v___y_4737_: u8 = 0;
    let mut v___x_4740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4746_: u8 = 0;
    let mut v___x_4747_: u8 = 0;
    let mut v_isSharedCheck_4748_: u8 = 0;
    let mut v_isSharedCheck_4749_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4717_) == 0 {
                    v___x_4724_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4724_, 0, v_x_4718_);
                    return v___x_4724_;
                } else {
                    v_head_4725_ = lean_ctor_get(v_x_4717_, 0);
                    v_tail_4726_ = lean_ctor_get(v_x_4717_, 1);
                    v_isSharedCheck_4749_ = (!lean_is_exclusive(v_x_4717_)) as u8;
                    if v_isSharedCheck_4749_ == 0 {
                        v___x_4728_ = v_x_4717_;
                        v_isShared_4729_ = v_isSharedCheck_4749_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_4726_);
                        lean_inc(v_head_4725_);
                        lean_dec(v_x_4717_);
                        v___x_4728_ = lean_box(0);
                        v_isShared_4729_ = v_isSharedCheck_4749_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_head_4725_);
                v___x_4730_ = l_Lean_MVarId_inferInstance(
                    v_head_4725_,
                    v___y_4719_,
                    v___y_4720_,
                    v___y_4721_,
                    v___y_4722_,
                );
                if lean_obj_tag(v___x_4730_) == 0 {
                    lean_dec_ref_known(v___x_4730_, 1);
                    lean_del_object(v___x_4728_);
                    lean_dec(v_head_4725_);
                    v_x_4717_ = v_tail_4726_;
                    state = 0;
                    continue;
                } else {
                    v_a_4732_ = lean_ctor_get(v___x_4730_, 0);
                    v_isSharedCheck_4748_ = (!lean_is_exclusive(v___x_4730_)) as u8;
                    if v_isSharedCheck_4748_ == 0 {
                        v___x_4734_ = v___x_4730_;
                        v_isShared_4735_ = v_isSharedCheck_4748_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_4732_);
                        lean_dec(v___x_4730_);
                        v___x_4734_ = lean_box(0);
                        v_isShared_4735_ = v_isSharedCheck_4748_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4746_ = l_Lean_Exception_isInterrupt(v_a_4732_);
                if v___x_4746_ == 0 {
                    lean_inc(v_a_4732_);
                    v___x_4747_ = l_Lean_Exception_isRuntime(v_a_4732_);
                    v___y_4737_ = v___x_4747_;
                    state = 3;
                    continue;
                } else {
                    v___y_4737_ = v___x_4746_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v___y_4737_ == 0 {
                    lean_del_object(v___x_4734_);
                    lean_dec(v_a_4732_);
                    if v___x_4716_ == 0 {
                        lean_del_object(v___x_4728_);
                        lean_dec(v_head_4725_);
                        v_x_4717_ = v_tail_4726_;
                        state = 0;
                        continue;
                    } else {
                        if v_isShared_4729_ == 0 {
                            lean_ctor_set(v___x_4728_, 1, v_x_4718_);
                            v___x_4740_ = v___x_4728_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_4742_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4742_, 0, v_head_4725_);
                            lean_ctor_set(v_reuseFailAlloc_4742_, 1, v_x_4718_);
                            v___x_4740_ = v_reuseFailAlloc_4742_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_4728_);
                    lean_dec(v_tail_4726_);
                    lean_dec(v_head_4725_);
                    lean_dec(v_x_4718_);
                    if v_isShared_4735_ == 0 {
                        v___x_4744_ = v___x_4734_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4745_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4745_, 0, v_a_4732_);
                        v___x_4744_ = v_reuseFailAlloc_4745_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                v_x_4717_ = v_tail_4726_;
                v_x_4718_ = v___x_4740_;
                state = 0;
                continue;
            }
            5 => {
                return v___x_4744_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__4___boxed(
    mut v___x_4750_: *mut LeanObject,
    mut v_x_4751_: *mut LeanObject,
    mut v_x_4752_: *mut LeanObject,
    mut v___y_4753_: *mut LeanObject,
    mut v___y_4754_: *mut LeanObject,
    mut v___y_4755_: *mut LeanObject,
    mut v___y_4756_: *mut LeanObject,
    mut v___y_4757_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_14652__boxed_4758_: u8 = 0;
    let mut v_res_4759_: *mut LeanObject = core::ptr::null_mut();
    v___x_14652__boxed_4758_ = (lean_unbox(v___x_4750_) as u8);
    v_res_4759_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__4(
        v___x_14652__boxed_4758_,
        v_x_4751_,
        v_x_4752_,
        v___y_4753_,
        v___y_4754_,
        v___y_4755_,
        v___y_4756_,
    );
    lean_dec(v___y_4756_);
    lean_dec_ref(v___y_4755_);
    lean_dec(v___y_4754_);
    lean_dec_ref(v___y_4753_);
    return v_res_4759_;
}
pub unsafe fn l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5(
    mut v___x_4760_: u8,
    mut v_x_4761_: *mut LeanObject,
    mut v_x_4762_: *mut LeanObject,
    mut v___y_4763_: *mut LeanObject,
    mut v___y_4764_: *mut LeanObject,
    mut v___y_4765_: *mut LeanObject,
    mut v___y_4766_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4773_: u8 = 0;
    let mut v___x_4776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4784_: u8 = 0;
    let mut v___y_4786_: u8 = 0;
    let mut v___x_4788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4790_: u8 = 0;
    let mut v___x_4791_: u8 = 0;
    let mut v_isSharedCheck_4792_: u8 = 0;
    let mut v_isSharedCheck_4793_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4761_) == 0 {
                    v___x_4768_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4768_, 0, v_x_4762_);
                    return v___x_4768_;
                } else {
                    v_head_4769_ = lean_ctor_get(v_x_4761_, 0);
                    v_tail_4770_ = lean_ctor_get(v_x_4761_, 1);
                    v_isSharedCheck_4793_ = (!lean_is_exclusive(v_x_4761_)) as u8;
                    if v_isSharedCheck_4793_ == 0 {
                        v___x_4772_ = v_x_4761_;
                        v_isShared_4773_ = v_isSharedCheck_4793_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_4770_);
                        lean_inc(v_head_4769_);
                        lean_dec(v_x_4761_);
                        v___x_4772_ = lean_box(0);
                        v_isShared_4773_ = v_isSharedCheck_4793_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_head_4769_);
                v___x_4779_ = l_Lean_MVarId_inferInstance(
                    v_head_4769_,
                    v___y_4763_,
                    v___y_4764_,
                    v___y_4765_,
                    v___y_4766_,
                );
                if lean_obj_tag(v___x_4779_) == 0 {
                    lean_dec_ref_known(v___x_4779_, 1);
                    if v___x_4760_ == 0 {
                        lean_del_object(v___x_4772_);
                        lean_dec(v_head_4769_);
                        v_x_4761_ = v_tail_4770_;
                        state = 0;
                        continue;
                    } else {
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_4781_ = lean_ctor_get(v___x_4779_, 0);
                    v_isSharedCheck_4792_ = (!lean_is_exclusive(v___x_4779_)) as u8;
                    if v_isSharedCheck_4792_ == 0 {
                        v___x_4783_ = v___x_4779_;
                        v_isShared_4784_ = v_isSharedCheck_4792_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_4781_);
                        lean_dec(v___x_4779_);
                        v___x_4783_ = lean_box(0);
                        v_isShared_4784_ = v_isSharedCheck_4792_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_4773_ == 0 {
                    lean_ctor_set(v___x_4772_, 1, v_x_4762_);
                    v___x_4776_ = v___x_4772_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4778_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4778_, 0, v_head_4769_);
                    lean_ctor_set(v_reuseFailAlloc_4778_, 1, v_x_4762_);
                    v___x_4776_ = v_reuseFailAlloc_4778_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_x_4761_ = v_tail_4770_;
                v_x_4762_ = v___x_4776_;
                state = 0;
                continue;
            }
            4 => {
                v___x_4790_ = l_Lean_Exception_isInterrupt(v_a_4781_);
                if v___x_4790_ == 0 {
                    lean_inc(v_a_4781_);
                    v___x_4791_ = l_Lean_Exception_isRuntime(v_a_4781_);
                    v___y_4786_ = v___x_4791_;
                    state = 5;
                    continue;
                } else {
                    v___y_4786_ = v___x_4790_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v___y_4786_ == 0 {
                    lean_del_object(v___x_4783_);
                    lean_dec(v_a_4781_);
                    state = 2;
                    continue;
                } else {
                    lean_del_object(v___x_4772_);
                    lean_dec(v_tail_4770_);
                    lean_dec(v_head_4769_);
                    lean_dec(v_x_4762_);
                    if v_isShared_4784_ == 0 {
                        v___x_4788_ = v___x_4783_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_4789_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4789_, 0, v_a_4781_);
                        v___x_4788_ = v_reuseFailAlloc_4789_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_4788_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5___boxed(
    mut v___x_4794_: *mut LeanObject,
    mut v_x_4795_: *mut LeanObject,
    mut v_x_4796_: *mut LeanObject,
    mut v___y_4797_: *mut LeanObject,
    mut v___y_4798_: *mut LeanObject,
    mut v___y_4799_: *mut LeanObject,
    mut v___y_4800_: *mut LeanObject,
    mut v___y_4801_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_14729__boxed_4802_: u8 = 0;
    let mut v_res_4803_: *mut LeanObject = core::ptr::null_mut();
    v___x_14729__boxed_4802_ = (lean_unbox(v___x_4794_) as u8);
    v_res_4803_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5(
        v___x_14729__boxed_4802_,
        v_x_4795_,
        v_x_4796_,
        v___y_4797_,
        v___y_4798_,
        v___y_4799_,
        v___y_4800_,
    );
    lean_dec(v___y_4800_);
    lean_dec_ref(v___y_4799_);
    lean_dec(v___y_4798_);
    lean_dec_ref(v___y_4797_);
    return v_res_4803_;
}
pub unsafe fn _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2() -> f64 {
    let mut v___x_4807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4808_: f64 = 0.0;
    v___x_4807_ = lean_unsigned_to_nat(1000000000);
    v___x_4808_ = lean_float_of_nat(v___x_4807_);
    return v___x_4808_;
}
pub unsafe fn l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1(
    mut v_transparency_4809_: u8,
    mut v_g_4810_: *mut LeanObject,
    mut v_e_4811_: *mut LeanObject,
    mut v_cfg_4812_: *mut LeanObject,
    mut v___x_4813_: *mut LeanObject,
    mut v___x_4814_: *mut LeanObject,
    mut v___x_4815_: u8,
    mut v___x_4816_: *mut LeanObject,
    mut v___f_4817_: *mut LeanObject,
    mut v___y_4818_: *mut LeanObject,
    mut v___y_4819_: *mut LeanObject,
    mut v___y_4820_: *mut LeanObject,
    mut v___y_4821_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_options_4823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_4824_: u8 = 0;
    let mut v___x_4825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_foApprox_4826_: u8 = 0;
    let mut v_ctxApprox_4827_: u8 = 0;
    let mut v_quasiPatternApprox_4828_: u8 = 0;
    let mut v_constApprox_4829_: u8 = 0;
    let mut v_isDefEqStuckEx_4830_: u8 = 0;
    let mut v_unificationHints_4831_: u8 = 0;
    let mut v_proofIrrelevance_4832_: u8 = 0;
    let mut v_assignSyntheticOpaque_4833_: u8 = 0;
    let mut v_offsetCnstrs_4834_: u8 = 0;
    let mut v_etaStruct_4835_: u8 = 0;
    let mut v_univApprox_4836_: u8 = 0;
    let mut v_iota_4837_: u8 = 0;
    let mut v_beta_4838_: u8 = 0;
    let mut v_proj_4839_: u8 = 0;
    let mut v_zeta_4840_: u8 = 0;
    let mut v_zetaDelta_4841_: u8 = 0;
    let mut v_zetaUnused_4842_: u8 = 0;
    let mut v_zetaHave_4843_: u8 = 0;
    let mut v___x_4845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4846_: u8 = 0;
    let mut v_trackZetaDelta_4847_: u8 = 0;
    let mut v_zetaDeltaSet_4848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_4849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_localInstances_4850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_4851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_4852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_4853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_univApprox_4854_: u8 = 0;
    let mut v_inTypeClassResolution_4855_: u8 = 0;
    let mut v_cacheInferType_4856_: u8 = 0;
    let mut v_config_4858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4859_: u64 = 0;
    let mut v___x_4860_: u64 = 0;
    let mut v___x_4861_: u64 = 0;
    let mut v___x_4862_: u64 = 0;
    let mut v___x_4863_: u64 = 0;
    let mut v_key_4864_: u64 = 0;
    let mut v___x_4865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4874_: u8 = 0;
    let mut v___x_4875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4879_: u8 = 0;
    let mut v_reuseFailAlloc_4880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4881_: u8 = 0;
    let mut v_inheritedTraceOptions_4882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4885_: u8 = 0;
    let mut v___y_4887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4891_: f64 = 0.0;
    let mut v___x_4892_: f64 = 0.0;
    let mut v___x_4893_: f64 = 0.0;
    let mut v___x_4894_: f64 = 0.0;
    let mut v___x_4895_: f64 = 0.0;
    let mut v___x_4896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4914_: u8 = 0;
    let mut v___x_4916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4918_: u8 = 0;
    let mut v___y_4920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4924_: f64 = 0.0;
    let mut v___x_4925_: f64 = 0.0;
    let mut v___x_4926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4944_: u8 = 0;
    let mut v___x_4946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4948_: u8 = 0;
    let mut v___x_4950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4953_: u8 = 0;
    let mut v___x_4954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_foApprox_4956_: u8 = 0;
    let mut v_ctxApprox_4957_: u8 = 0;
    let mut v_quasiPatternApprox_4958_: u8 = 0;
    let mut v_constApprox_4959_: u8 = 0;
    let mut v_isDefEqStuckEx_4960_: u8 = 0;
    let mut v_unificationHints_4961_: u8 = 0;
    let mut v_proofIrrelevance_4962_: u8 = 0;
    let mut v_assignSyntheticOpaque_4963_: u8 = 0;
    let mut v_offsetCnstrs_4964_: u8 = 0;
    let mut v_etaStruct_4965_: u8 = 0;
    let mut v_univApprox_4966_: u8 = 0;
    let mut v_iota_4967_: u8 = 0;
    let mut v_beta_4968_: u8 = 0;
    let mut v_proj_4969_: u8 = 0;
    let mut v_zeta_4970_: u8 = 0;
    let mut v_zetaDelta_4971_: u8 = 0;
    let mut v_zetaUnused_4972_: u8 = 0;
    let mut v_zetaHave_4973_: u8 = 0;
    let mut v___x_4975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4976_: u8 = 0;
    let mut v_trackZetaDelta_4977_: u8 = 0;
    let mut v_zetaDeltaSet_4978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_4979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_localInstances_4980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_4981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_4982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_4983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_univApprox_4984_: u8 = 0;
    let mut v_inTypeClassResolution_4985_: u8 = 0;
    let mut v_cacheInferType_4986_: u8 = 0;
    let mut v_config_4988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4989_: u64 = 0;
    let mut v___x_4990_: u64 = 0;
    let mut v___x_4991_: u64 = 0;
    let mut v___x_4992_: u64 = 0;
    let mut v___x_4993_: u64 = 0;
    let mut v_key_4994_: u64 = 0;
    let mut v___x_4995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5004_: u8 = 0;
    let mut v___x_5005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_foApprox_5007_: u8 = 0;
    let mut v_ctxApprox_5008_: u8 = 0;
    let mut v_quasiPatternApprox_5009_: u8 = 0;
    let mut v_constApprox_5010_: u8 = 0;
    let mut v_isDefEqStuckEx_5011_: u8 = 0;
    let mut v_unificationHints_5012_: u8 = 0;
    let mut v_proofIrrelevance_5013_: u8 = 0;
    let mut v_assignSyntheticOpaque_5014_: u8 = 0;
    let mut v_offsetCnstrs_5015_: u8 = 0;
    let mut v_etaStruct_5016_: u8 = 0;
    let mut v_univApprox_5017_: u8 = 0;
    let mut v_iota_5018_: u8 = 0;
    let mut v_beta_5019_: u8 = 0;
    let mut v_proj_5020_: u8 = 0;
    let mut v_zeta_5021_: u8 = 0;
    let mut v_zetaDelta_5022_: u8 = 0;
    let mut v_zetaUnused_5023_: u8 = 0;
    let mut v_zetaHave_5024_: u8 = 0;
    let mut v___x_5026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5027_: u8 = 0;
    let mut v_trackZetaDelta_5028_: u8 = 0;
    let mut v_zetaDeltaSet_5029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_5030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_localInstances_5031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_5032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_5033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_5034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_univApprox_5035_: u8 = 0;
    let mut v_inTypeClassResolution_5036_: u8 = 0;
    let mut v_cacheInferType_5037_: u8 = 0;
    let mut v_config_5039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5040_: u64 = 0;
    let mut v___x_5041_: u64 = 0;
    let mut v___x_5042_: u64 = 0;
    let mut v___x_5043_: u64 = 0;
    let mut v___x_5044_: u64 = 0;
    let mut v_key_5045_: u64 = 0;
    let mut v___x_5046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5055_: u8 = 0;
    let mut v___x_5056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5057_: u8 = 0;
    let mut v___x_5058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_foApprox_5059_: u8 = 0;
    let mut v_ctxApprox_5060_: u8 = 0;
    let mut v_quasiPatternApprox_5061_: u8 = 0;
    let mut v_constApprox_5062_: u8 = 0;
    let mut v_isDefEqStuckEx_5063_: u8 = 0;
    let mut v_unificationHints_5064_: u8 = 0;
    let mut v_proofIrrelevance_5065_: u8 = 0;
    let mut v_assignSyntheticOpaque_5066_: u8 = 0;
    let mut v_offsetCnstrs_5067_: u8 = 0;
    let mut v_etaStruct_5068_: u8 = 0;
    let mut v_univApprox_5069_: u8 = 0;
    let mut v_iota_5070_: u8 = 0;
    let mut v_beta_5071_: u8 = 0;
    let mut v_proj_5072_: u8 = 0;
    let mut v_zeta_5073_: u8 = 0;
    let mut v_zetaDelta_5074_: u8 = 0;
    let mut v_zetaUnused_5075_: u8 = 0;
    let mut v_zetaHave_5076_: u8 = 0;
    let mut v___x_5078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5079_: u8 = 0;
    let mut v_trackZetaDelta_5080_: u8 = 0;
    let mut v_zetaDeltaSet_5081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_5082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_localInstances_5083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_5084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_5085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_5086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_univApprox_5087_: u8 = 0;
    let mut v_inTypeClassResolution_5088_: u8 = 0;
    let mut v_cacheInferType_5089_: u8 = 0;
    let mut v_config_5091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5092_: u64 = 0;
    let mut v___x_5093_: u64 = 0;
    let mut v___x_5094_: u64 = 0;
    let mut v___x_5095_: u64 = 0;
    let mut v___x_5096_: u64 = 0;
    let mut v_key_5097_: u64 = 0;
    let mut v___x_5098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5107_: u8 = 0;
    let mut v___x_5108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5112_: u8 = 0;
    let mut v_reuseFailAlloc_5113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5114_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_4823_ = lean_ctor_get(v___y_4820_, 2);
                v_hasTrace_4824_ = lean_ctor_get_uint8(
                    v_options_4823_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                if v_hasTrace_4824_ == 0 {
                    lean_dec_ref(v___f_4817_);
                    lean_dec_ref(v___x_4816_);
                    lean_dec(v___x_4814_);
                    v___x_4825_ = l_Lean_Meta_Context_config(v___y_4818_);
                    v_foApprox_4826_ = lean_ctor_get_uint8(v___x_4825_, 0 as u32);
                    v_ctxApprox_4827_ = lean_ctor_get_uint8(v___x_4825_, 1 as u32);
                    v_quasiPatternApprox_4828_ = lean_ctor_get_uint8(v___x_4825_, 2 as u32);
                    v_constApprox_4829_ = lean_ctor_get_uint8(v___x_4825_, 3 as u32);
                    v_isDefEqStuckEx_4830_ = lean_ctor_get_uint8(v___x_4825_, 4 as u32);
                    v_unificationHints_4831_ = lean_ctor_get_uint8(v___x_4825_, 5 as u32);
                    v_proofIrrelevance_4832_ = lean_ctor_get_uint8(v___x_4825_, 6 as u32);
                    v_assignSyntheticOpaque_4833_ = lean_ctor_get_uint8(v___x_4825_, 7 as u32);
                    v_offsetCnstrs_4834_ = lean_ctor_get_uint8(v___x_4825_, 8 as u32);
                    v_etaStruct_4835_ = lean_ctor_get_uint8(v___x_4825_, 10 as u32);
                    v_univApprox_4836_ = lean_ctor_get_uint8(v___x_4825_, 11 as u32);
                    v_iota_4837_ = lean_ctor_get_uint8(v___x_4825_, 12 as u32);
                    v_beta_4838_ = lean_ctor_get_uint8(v___x_4825_, 13 as u32);
                    v_proj_4839_ = lean_ctor_get_uint8(v___x_4825_, 14 as u32);
                    v_zeta_4840_ = lean_ctor_get_uint8(v___x_4825_, 15 as u32);
                    v_zetaDelta_4841_ = lean_ctor_get_uint8(v___x_4825_, 16 as u32);
                    v_zetaUnused_4842_ = lean_ctor_get_uint8(v___x_4825_, 17 as u32);
                    v_zetaHave_4843_ = lean_ctor_get_uint8(v___x_4825_, 18 as u32);
                    v_isSharedCheck_4881_ = (!lean_is_exclusive(v___x_4825_)) as u8;
                    if v_isSharedCheck_4881_ == 0 {
                        v___x_4845_ = v___x_4825_;
                        v_isShared_4846_ = v_isSharedCheck_4881_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_4825_);
                        v___x_4845_ = lean_box(0);
                        v_isShared_4846_ = v_isSharedCheck_4881_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_inheritedTraceOptions_4882_ = lean_ctor_get(v___y_4820_, 13);
                    v___x_4883_ =
                        l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__1;
                    lean_inc(v___x_4814_);
                    v___x_4884_ = l_Lean_Name_append(v___x_4883_, v___x_4814_);
                    v___x_4885_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_4882_,
                        v_options_4823_,
                        v___x_4884_,
                    );
                    lean_dec(v___x_4884_);
                    if v___x_4885_ == 0 {
                        v___x_5056_ = l_Lean_trace_profiler;
                        v___x_5057_ =
                            l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(
                                v_options_4823_,
                                v___x_5056_,
                            );
                        if v___x_5057_ == 0 {
                            lean_dec_ref(v___f_4817_);
                            lean_dec_ref(v___x_4816_);
                            lean_dec(v___x_4814_);
                            v___x_5058_ = l_Lean_Meta_Context_config(v___y_4818_);
                            v_foApprox_5059_ = lean_ctor_get_uint8(v___x_5058_, 0 as u32);
                            v_ctxApprox_5060_ = lean_ctor_get_uint8(v___x_5058_, 1 as u32);
                            v_quasiPatternApprox_5061_ = lean_ctor_get_uint8(v___x_5058_, 2 as u32);
                            v_constApprox_5062_ = lean_ctor_get_uint8(v___x_5058_, 3 as u32);
                            v_isDefEqStuckEx_5063_ = lean_ctor_get_uint8(v___x_5058_, 4 as u32);
                            v_unificationHints_5064_ = lean_ctor_get_uint8(v___x_5058_, 5 as u32);
                            v_proofIrrelevance_5065_ = lean_ctor_get_uint8(v___x_5058_, 6 as u32);
                            v_assignSyntheticOpaque_5066_ =
                                lean_ctor_get_uint8(v___x_5058_, 7 as u32);
                            v_offsetCnstrs_5067_ = lean_ctor_get_uint8(v___x_5058_, 8 as u32);
                            v_etaStruct_5068_ = lean_ctor_get_uint8(v___x_5058_, 10 as u32);
                            v_univApprox_5069_ = lean_ctor_get_uint8(v___x_5058_, 11 as u32);
                            v_iota_5070_ = lean_ctor_get_uint8(v___x_5058_, 12 as u32);
                            v_beta_5071_ = lean_ctor_get_uint8(v___x_5058_, 13 as u32);
                            v_proj_5072_ = lean_ctor_get_uint8(v___x_5058_, 14 as u32);
                            v_zeta_5073_ = lean_ctor_get_uint8(v___x_5058_, 15 as u32);
                            v_zetaDelta_5074_ = lean_ctor_get_uint8(v___x_5058_, 16 as u32);
                            v_zetaUnused_5075_ = lean_ctor_get_uint8(v___x_5058_, 17 as u32);
                            v_zetaHave_5076_ = lean_ctor_get_uint8(v___x_5058_, 18 as u32);
                            v_isSharedCheck_5114_ = (!lean_is_exclusive(v___x_5058_)) as u8;
                            if v_isSharedCheck_5114_ == 0 {
                                v___x_5078_ = v___x_5058_;
                                v_isShared_5079_ = v_isSharedCheck_5114_;
                                state = 20;
                                continue;
                            } else {
                                lean_dec(v___x_5058_);
                                v___x_5078_ = lean_box(0);
                                v_isShared_5079_ = v_isSharedCheck_5114_;
                                state = 20;
                                continue;
                            }
                        } else {
                            state = 15;
                            continue;
                        }
                    } else {
                        state = 15;
                        continue;
                    }
                }
            }
            1 => {
                v_trackZetaDelta_4847_ = lean_ctor_get_uint8(
                    v___y_4818_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_4848_ = lean_ctor_get(v___y_4818_, 1);
                v_lctx_4849_ = lean_ctor_get(v___y_4818_, 2);
                v_localInstances_4850_ = lean_ctor_get(v___y_4818_, 3);
                v_defEqCtx_x3f_4851_ = lean_ctor_get(v___y_4818_, 4);
                v_synthPendingDepth_4852_ = lean_ctor_get(v___y_4818_, 5);
                v_canUnfold_x3f_4853_ = lean_ctor_get(v___y_4818_, 6);
                v_univApprox_4854_ = lean_ctor_get_uint8(
                    v___y_4818_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_4855_ = lean_ctor_get_uint8(
                    v___y_4818_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_4856_ = lean_ctor_get_uint8(
                    v___y_4818_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                );
                if v_isShared_4846_ == 0 {
                    v_config_4858_ = v___x_4845_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4880_ = lean_alloc_ctor(0, 0, (19) as u32);
                    lean_ctor_set_uint8(v_reuseFailAlloc_4880_, 0 as u32, v_foApprox_4826_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_4880_, 1 as u32, v_ctxApprox_4827_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4880_,
                        2 as u32,
                        v_quasiPatternApprox_4828_,
                    );
                    lean_ctor_set_uint8(v_reuseFailAlloc_4880_, 3 as u32, v_constApprox_4829_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_4880_, 4 as u32, v_isDefEqStuckEx_4830_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_4880_, 5 as u32, v_unificationHints_4831_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_4880_, 6 as u32, v_proofIrrelevance_4832_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4880_,
                        7 as u32,
                        v_assignSyntheticOpaque_4833_,
                    );
                    lean_ctor_set_uint8(v_reuseFailAlloc_4880_, 8 as u32, v_offsetCnstrs_4834_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_4880_, 10 as u32, v_etaStruct_4835_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_4880_, 11 as u32, v_univApprox_4836_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_4880_, 12 as u32, v_iota_4837_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_4880_, 13 as u32, v_beta_4838_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_4880_, 14 as u32, v_proj_4839_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_4880_, 15 as u32, v_zeta_4840_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_4880_, 16 as u32, v_zetaDelta_4841_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_4880_, 17 as u32, v_zetaUnused_4842_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_4880_, 18 as u32, v_zetaHave_4843_);
                    v_config_4858_ = v_reuseFailAlloc_4880_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_ctor_set_uint8(v_config_4858_, 9 as u32, v_transparency_4809_);
                v___x_4859_ = l_Lean_Meta_Context_configKey(v___y_4818_);
                v___x_4860_ = 3u64;
                v___x_4861_ = lean_uint64_shift_right(v___x_4859_, v___x_4860_);
                v___x_4862_ = lean_uint64_shift_left(v___x_4861_, v___x_4860_);
                v___x_4863_ = l_Lean_Meta_TransparencyMode_toUInt64(v_transparency_4809_);
                v_key_4864_ = lean_uint64_lor(v___x_4862_, v___x_4863_);
                v___x_4865_ = lean_alloc_ctor(0, 1, (8) as u32);
                lean_ctor_set(v___x_4865_, 0, v_config_4858_);
                lean_ctor_set_uint64(
                    v___x_4865_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v_key_4864_,
                );
                lean_inc(v_canUnfold_x3f_4853_);
                lean_inc(v_synthPendingDepth_4852_);
                lean_inc(v_defEqCtx_x3f_4851_);
                lean_inc_ref(v_localInstances_4850_);
                lean_inc_ref(v_lctx_4849_);
                lean_inc(v_zetaDeltaSet_4848_);
                v___x_4866_ = lean_alloc_ctor(0, 7, (4) as u32);
                lean_ctor_set(v___x_4866_, 0, v___x_4865_);
                lean_ctor_set(v___x_4866_, 1, v_zetaDeltaSet_4848_);
                lean_ctor_set(v___x_4866_, 2, v_lctx_4849_);
                lean_ctor_set(v___x_4866_, 3, v_localInstances_4850_);
                lean_ctor_set(v___x_4866_, 4, v_defEqCtx_x3f_4851_);
                lean_ctor_set(v___x_4866_, 5, v_synthPendingDepth_4852_);
                lean_ctor_set(v___x_4866_, 6, v_canUnfold_x3f_4853_);
                lean_ctor_set_uint8(
                    v___x_4866_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                    v_trackZetaDelta_4847_,
                );
                lean_ctor_set_uint8(
                    v___x_4866_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                    v_univApprox_4854_,
                );
                lean_ctor_set_uint8(
                    v___x_4866_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_4855_,
                );
                lean_ctor_set_uint8(
                    v___x_4866_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_4856_,
                );
                v___x_4867_ = l_Lean_MVarId_apply(
                    v_g_4810_,
                    v_e_4811_,
                    v_cfg_4812_,
                    v___x_4813_,
                    v___x_4866_,
                    v___y_4819_,
                    v___y_4820_,
                    v___y_4821_,
                );
                lean_dec_ref_known(v___x_4866_, 7);
                if lean_obj_tag(v___x_4867_) == 0 {
                    v_a_4868_ = lean_ctor_get(v___x_4867_, 0);
                    lean_inc(v_a_4868_);
                    lean_dec_ref_known(v___x_4867_, 1);
                    v___x_4869_ = lean_box(0);
                    v___x_4870_ =
                        l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5(
                            v_hasTrace_4824_,
                            v_a_4868_,
                            v___x_4869_,
                            v___y_4818_,
                            v___y_4819_,
                            v___y_4820_,
                            v___y_4821_,
                        );
                    if lean_obj_tag(v___x_4870_) == 0 {
                        v_a_4871_ = lean_ctor_get(v___x_4870_, 0);
                        v_isSharedCheck_4879_ = (!lean_is_exclusive(v___x_4870_)) as u8;
                        if v_isSharedCheck_4879_ == 0 {
                            v___x_4873_ = v___x_4870_;
                            v_isShared_4874_ = v_isSharedCheck_4879_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_4871_);
                            lean_dec(v___x_4870_);
                            v___x_4873_ = lean_box(0);
                            v_isShared_4874_ = v_isSharedCheck_4879_;
                            state = 3;
                            continue;
                        }
                    } else {
                        return v___x_4870_;
                    }
                } else {
                    return v___x_4867_;
                }
            }
            3 => {
                v___x_4875_ = l_List_reverse___redArg(v_a_4871_);
                if v_isShared_4874_ == 0 {
                    lean_ctor_set(v___x_4873_, 0, v___x_4875_);
                    v___x_4877_ = v___x_4873_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4878_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4878_, 0, v___x_4875_);
                    v___x_4877_ = v_reuseFailAlloc_4878_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4877_;
            }
            5 => {
                v___x_4890_ = lean_io_mono_nanos_now();
                v___x_4891_ = lean_float_of_nat(v___y_4888_);
                v___x_4892_ = lean_float_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2_once
                    ),
                    _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2,
                );
                v___x_4893_ = lean_float_div(v___x_4891_, v___x_4892_);
                v___x_4894_ = lean_float_of_nat(v___x_4890_);
                v___x_4895_ = lean_float_div(v___x_4894_, v___x_4892_);
                v___x_4896_ = lean_box_float(v___x_4893_);
                v___x_4897_ = lean_box_float(v___x_4895_);
                v___x_4898_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4898_, 0, v___x_4896_);
                lean_ctor_set(v___x_4898_, 1, v___x_4897_);
                v___x_4899_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4899_, 0, v_a_4889_);
                lean_ctor_set(v___x_4899_, 1, v___x_4898_);
                v___x_4900_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___x_4814_, v___x_4815_, v___x_4816_, v_options_4823_, v___x_4885_, v___y_4887_, v___f_4817_, v___x_4899_, v___y_4818_, v___y_4819_, v___y_4820_, v___y_4821_);
                return v___x_4900_;
            }
            6 => {
                v___x_4905_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4905_, 0, v_a_4904_);
                v___y_4887_ = v___y_4902_;
                v___y_4888_ = v___y_4903_;
                v_a_4889_ = v___x_4905_;
                state = 5;
                continue;
            }
            7 => {
                if lean_obj_tag(v___y_4909_) == 0 {
                    v_a_4910_ = lean_ctor_get(v___y_4909_, 0);
                    lean_inc(v_a_4910_);
                    lean_dec_ref_known(v___y_4909_, 1);
                    v___y_4902_ = v___y_4907_;
                    v___y_4903_ = v___y_4908_;
                    v_a_4904_ = v_a_4910_;
                    state = 6;
                    continue;
                } else {
                    v_a_4911_ = lean_ctor_get(v___y_4909_, 0);
                    v_isSharedCheck_4918_ = (!lean_is_exclusive(v___y_4909_)) as u8;
                    if v_isSharedCheck_4918_ == 0 {
                        v___x_4913_ = v___y_4909_;
                        v_isShared_4914_ = v_isSharedCheck_4918_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_4911_);
                        lean_dec(v___y_4909_);
                        v___x_4913_ = lean_box(0);
                        v_isShared_4914_ = v_isSharedCheck_4918_;
                        state = 8;
                        continue;
                    }
                }
            }
            8 => {
                if v_isShared_4914_ == 0 {
                    lean_ctor_set_tag(v___x_4913_, 0);
                    v___x_4916_ = v___x_4913_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4917_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4917_, 0, v_a_4911_);
                    v___x_4916_ = v_reuseFailAlloc_4917_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___y_4887_ = v___y_4907_;
                v___y_4888_ = v___y_4908_;
                v_a_4889_ = v___x_4916_;
                state = 5;
                continue;
            }
            10 => {
                v___x_4923_ = lean_io_get_num_heartbeats();
                v___x_4924_ = lean_float_of_nat(v___y_4921_);
                v___x_4925_ = lean_float_of_nat(v___x_4923_);
                v___x_4926_ = lean_box_float(v___x_4924_);
                v___x_4927_ = lean_box_float(v___x_4925_);
                v___x_4928_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4928_, 0, v___x_4926_);
                lean_ctor_set(v___x_4928_, 1, v___x_4927_);
                v___x_4929_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4929_, 0, v_a_4922_);
                lean_ctor_set(v___x_4929_, 1, v___x_4928_);
                v___x_4930_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___x_4814_, v___x_4815_, v___x_4816_, v_options_4823_, v___x_4885_, v___y_4920_, v___f_4817_, v___x_4929_, v___y_4818_, v___y_4819_, v___y_4820_, v___y_4821_);
                return v___x_4930_;
            }
            11 => {
                v___x_4935_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4935_, 0, v_a_4934_);
                v___y_4920_ = v___y_4933_;
                v___y_4921_ = v___y_4932_;
                v_a_4922_ = v___x_4935_;
                state = 10;
                continue;
            }
            12 => {
                if lean_obj_tag(v___y_4939_) == 0 {
                    v_a_4940_ = lean_ctor_get(v___y_4939_, 0);
                    lean_inc(v_a_4940_);
                    lean_dec_ref_known(v___y_4939_, 1);
                    v___y_4932_ = v___y_4938_;
                    v___y_4933_ = v___y_4937_;
                    v_a_4934_ = v_a_4940_;
                    state = 11;
                    continue;
                } else {
                    v_a_4941_ = lean_ctor_get(v___y_4939_, 0);
                    v_isSharedCheck_4948_ = (!lean_is_exclusive(v___y_4939_)) as u8;
                    if v_isSharedCheck_4948_ == 0 {
                        v___x_4943_ = v___y_4939_;
                        v_isShared_4944_ = v_isSharedCheck_4948_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_a_4941_);
                        lean_dec(v___y_4939_);
                        v___x_4943_ = lean_box(0);
                        v_isShared_4944_ = v_isSharedCheck_4948_;
                        state = 13;
                        continue;
                    }
                }
            }
            13 => {
                if v_isShared_4944_ == 0 {
                    lean_ctor_set_tag(v___x_4943_, 0);
                    v___x_4946_ = v___x_4943_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4947_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4947_, 0, v_a_4941_);
                    v___x_4946_ = v_reuseFailAlloc_4947_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___y_4920_ = v___y_4937_;
                v___y_4921_ = v___y_4938_;
                v_a_4922_ = v___x_4946_;
                state = 10;
                continue;
            }
            15 => {
                v___x_4950_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg(v___y_4821_);
                v_a_4951_ = lean_ctor_get(v___x_4950_, 0);
                lean_inc(v_a_4951_);
                lean_dec_ref(v___x_4950_);
                v___x_4952_ = l_Lean_trace_profiler_useHeartbeats;
                v___x_4953_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(
                    v_options_4823_,
                    v___x_4952_,
                );
                if v___x_4953_ == 0 {
                    v___x_4954_ = lean_io_mono_nanos_now();
                    v___x_4955_ = l_Lean_Meta_Context_config(v___y_4818_);
                    v_foApprox_4956_ = lean_ctor_get_uint8(v___x_4955_, 0 as u32);
                    v_ctxApprox_4957_ = lean_ctor_get_uint8(v___x_4955_, 1 as u32);
                    v_quasiPatternApprox_4958_ = lean_ctor_get_uint8(v___x_4955_, 2 as u32);
                    v_constApprox_4959_ = lean_ctor_get_uint8(v___x_4955_, 3 as u32);
                    v_isDefEqStuckEx_4960_ = lean_ctor_get_uint8(v___x_4955_, 4 as u32);
                    v_unificationHints_4961_ = lean_ctor_get_uint8(v___x_4955_, 5 as u32);
                    v_proofIrrelevance_4962_ = lean_ctor_get_uint8(v___x_4955_, 6 as u32);
                    v_assignSyntheticOpaque_4963_ = lean_ctor_get_uint8(v___x_4955_, 7 as u32);
                    v_offsetCnstrs_4964_ = lean_ctor_get_uint8(v___x_4955_, 8 as u32);
                    v_etaStruct_4965_ = lean_ctor_get_uint8(v___x_4955_, 10 as u32);
                    v_univApprox_4966_ = lean_ctor_get_uint8(v___x_4955_, 11 as u32);
                    v_iota_4967_ = lean_ctor_get_uint8(v___x_4955_, 12 as u32);
                    v_beta_4968_ = lean_ctor_get_uint8(v___x_4955_, 13 as u32);
                    v_proj_4969_ = lean_ctor_get_uint8(v___x_4955_, 14 as u32);
                    v_zeta_4970_ = lean_ctor_get_uint8(v___x_4955_, 15 as u32);
                    v_zetaDelta_4971_ = lean_ctor_get_uint8(v___x_4955_, 16 as u32);
                    v_zetaUnused_4972_ = lean_ctor_get_uint8(v___x_4955_, 17 as u32);
                    v_zetaHave_4973_ = lean_ctor_get_uint8(v___x_4955_, 18 as u32);
                    v_isSharedCheck_5004_ = (!lean_is_exclusive(v___x_4955_)) as u8;
                    if v_isSharedCheck_5004_ == 0 {
                        v___x_4975_ = v___x_4955_;
                        v_isShared_4976_ = v_isSharedCheck_5004_;
                        state = 16;
                        continue;
                    } else {
                        lean_dec(v___x_4955_);
                        v___x_4975_ = lean_box(0);
                        v_isShared_4976_ = v_isSharedCheck_5004_;
                        state = 16;
                        continue;
                    }
                } else {
                    v___x_5005_ = lean_io_get_num_heartbeats();
                    v___x_5006_ = l_Lean_Meta_Context_config(v___y_4818_);
                    v_foApprox_5007_ = lean_ctor_get_uint8(v___x_5006_, 0 as u32);
                    v_ctxApprox_5008_ = lean_ctor_get_uint8(v___x_5006_, 1 as u32);
                    v_quasiPatternApprox_5009_ = lean_ctor_get_uint8(v___x_5006_, 2 as u32);
                    v_constApprox_5010_ = lean_ctor_get_uint8(v___x_5006_, 3 as u32);
                    v_isDefEqStuckEx_5011_ = lean_ctor_get_uint8(v___x_5006_, 4 as u32);
                    v_unificationHints_5012_ = lean_ctor_get_uint8(v___x_5006_, 5 as u32);
                    v_proofIrrelevance_5013_ = lean_ctor_get_uint8(v___x_5006_, 6 as u32);
                    v_assignSyntheticOpaque_5014_ = lean_ctor_get_uint8(v___x_5006_, 7 as u32);
                    v_offsetCnstrs_5015_ = lean_ctor_get_uint8(v___x_5006_, 8 as u32);
                    v_etaStruct_5016_ = lean_ctor_get_uint8(v___x_5006_, 10 as u32);
                    v_univApprox_5017_ = lean_ctor_get_uint8(v___x_5006_, 11 as u32);
                    v_iota_5018_ = lean_ctor_get_uint8(v___x_5006_, 12 as u32);
                    v_beta_5019_ = lean_ctor_get_uint8(v___x_5006_, 13 as u32);
                    v_proj_5020_ = lean_ctor_get_uint8(v___x_5006_, 14 as u32);
                    v_zeta_5021_ = lean_ctor_get_uint8(v___x_5006_, 15 as u32);
                    v_zetaDelta_5022_ = lean_ctor_get_uint8(v___x_5006_, 16 as u32);
                    v_zetaUnused_5023_ = lean_ctor_get_uint8(v___x_5006_, 17 as u32);
                    v_zetaHave_5024_ = lean_ctor_get_uint8(v___x_5006_, 18 as u32);
                    v_isSharedCheck_5055_ = (!lean_is_exclusive(v___x_5006_)) as u8;
                    if v_isSharedCheck_5055_ == 0 {
                        v___x_5026_ = v___x_5006_;
                        v_isShared_5027_ = v_isSharedCheck_5055_;
                        state = 18;
                        continue;
                    } else {
                        lean_dec(v___x_5006_);
                        v___x_5026_ = lean_box(0);
                        v_isShared_5027_ = v_isSharedCheck_5055_;
                        state = 18;
                        continue;
                    }
                }
            }
            16 => {
                v_trackZetaDelta_4977_ = lean_ctor_get_uint8(
                    v___y_4818_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_4978_ = lean_ctor_get(v___y_4818_, 1);
                v_lctx_4979_ = lean_ctor_get(v___y_4818_, 2);
                v_localInstances_4980_ = lean_ctor_get(v___y_4818_, 3);
                v_defEqCtx_x3f_4981_ = lean_ctor_get(v___y_4818_, 4);
                v_synthPendingDepth_4982_ = lean_ctor_get(v___y_4818_, 5);
                v_canUnfold_x3f_4983_ = lean_ctor_get(v___y_4818_, 6);
                v_univApprox_4984_ = lean_ctor_get_uint8(
                    v___y_4818_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_4985_ = lean_ctor_get_uint8(
                    v___y_4818_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_4986_ = lean_ctor_get_uint8(
                    v___y_4818_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                );
                if v_isShared_4976_ == 0 {
                    v_config_4988_ = v___x_4975_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_5003_ = lean_alloc_ctor(0, 0, (19) as u32);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5003_, 0 as u32, v_foApprox_4956_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5003_, 1 as u32, v_ctxApprox_4957_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5003_,
                        2 as u32,
                        v_quasiPatternApprox_4958_,
                    );
                    lean_ctor_set_uint8(v_reuseFailAlloc_5003_, 3 as u32, v_constApprox_4959_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5003_, 4 as u32, v_isDefEqStuckEx_4960_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5003_, 5 as u32, v_unificationHints_4961_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5003_, 6 as u32, v_proofIrrelevance_4962_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5003_,
                        7 as u32,
                        v_assignSyntheticOpaque_4963_,
                    );
                    lean_ctor_set_uint8(v_reuseFailAlloc_5003_, 8 as u32, v_offsetCnstrs_4964_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5003_, 10 as u32, v_etaStruct_4965_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5003_, 11 as u32, v_univApprox_4966_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5003_, 12 as u32, v_iota_4967_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5003_, 13 as u32, v_beta_4968_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5003_, 14 as u32, v_proj_4969_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5003_, 15 as u32, v_zeta_4970_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5003_, 16 as u32, v_zetaDelta_4971_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5003_, 17 as u32, v_zetaUnused_4972_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5003_, 18 as u32, v_zetaHave_4973_);
                    v_config_4988_ = v_reuseFailAlloc_5003_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                lean_ctor_set_uint8(v_config_4988_, 9 as u32, v_transparency_4809_);
                v___x_4989_ = l_Lean_Meta_Context_configKey(v___y_4818_);
                v___x_4990_ = 3u64;
                v___x_4991_ = lean_uint64_shift_right(v___x_4989_, v___x_4990_);
                v___x_4992_ = lean_uint64_shift_left(v___x_4991_, v___x_4990_);
                v___x_4993_ = l_Lean_Meta_TransparencyMode_toUInt64(v_transparency_4809_);
                v_key_4994_ = lean_uint64_lor(v___x_4992_, v___x_4993_);
                v___x_4995_ = lean_alloc_ctor(0, 1, (8) as u32);
                lean_ctor_set(v___x_4995_, 0, v_config_4988_);
                lean_ctor_set_uint64(
                    v___x_4995_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v_key_4994_,
                );
                lean_inc(v_canUnfold_x3f_4983_);
                lean_inc(v_synthPendingDepth_4982_);
                lean_inc(v_defEqCtx_x3f_4981_);
                lean_inc_ref(v_localInstances_4980_);
                lean_inc_ref(v_lctx_4979_);
                lean_inc(v_zetaDeltaSet_4978_);
                v___x_4996_ = lean_alloc_ctor(0, 7, (4) as u32);
                lean_ctor_set(v___x_4996_, 0, v___x_4995_);
                lean_ctor_set(v___x_4996_, 1, v_zetaDeltaSet_4978_);
                lean_ctor_set(v___x_4996_, 2, v_lctx_4979_);
                lean_ctor_set(v___x_4996_, 3, v_localInstances_4980_);
                lean_ctor_set(v___x_4996_, 4, v_defEqCtx_x3f_4981_);
                lean_ctor_set(v___x_4996_, 5, v_synthPendingDepth_4982_);
                lean_ctor_set(v___x_4996_, 6, v_canUnfold_x3f_4983_);
                lean_ctor_set_uint8(
                    v___x_4996_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                    v_trackZetaDelta_4977_,
                );
                lean_ctor_set_uint8(
                    v___x_4996_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                    v_univApprox_4984_,
                );
                lean_ctor_set_uint8(
                    v___x_4996_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_4985_,
                );
                lean_ctor_set_uint8(
                    v___x_4996_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_4986_,
                );
                v___x_4997_ = l_Lean_MVarId_apply(
                    v_g_4810_,
                    v_e_4811_,
                    v_cfg_4812_,
                    v___x_4813_,
                    v___x_4996_,
                    v___y_4819_,
                    v___y_4820_,
                    v___y_4821_,
                );
                lean_dec_ref_known(v___x_4996_, 7);
                if lean_obj_tag(v___x_4997_) == 0 {
                    v_a_4998_ = lean_ctor_get(v___x_4997_, 0);
                    lean_inc(v_a_4998_);
                    lean_dec_ref_known(v___x_4997_, 1);
                    v___x_4999_ = lean_box(0);
                    v___x_5000_ =
                        l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(
                            v___x_4953_,
                            v_hasTrace_4824_,
                            v_a_4998_,
                            v___x_4999_,
                            v___y_4818_,
                            v___y_4819_,
                            v___y_4820_,
                            v___y_4821_,
                        );
                    if lean_obj_tag(v___x_5000_) == 0 {
                        v_a_5001_ = lean_ctor_get(v___x_5000_, 0);
                        lean_inc(v_a_5001_);
                        lean_dec_ref_known(v___x_5000_, 1);
                        v___x_5002_ = l_List_reverse___redArg(v_a_5001_);
                        v___y_4902_ = v_a_4951_;
                        v___y_4903_ = v___x_4954_;
                        v_a_4904_ = v___x_5002_;
                        state = 6;
                        continue;
                    } else {
                        v___y_4907_ = v_a_4951_;
                        v___y_4908_ = v___x_4954_;
                        v___y_4909_ = v___x_5000_;
                        state = 7;
                        continue;
                    }
                } else {
                    v___y_4907_ = v_a_4951_;
                    v___y_4908_ = v___x_4954_;
                    v___y_4909_ = v___x_4997_;
                    state = 7;
                    continue;
                }
            }
            18 => {
                v_trackZetaDelta_5028_ = lean_ctor_get_uint8(
                    v___y_4818_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_5029_ = lean_ctor_get(v___y_4818_, 1);
                v_lctx_5030_ = lean_ctor_get(v___y_4818_, 2);
                v_localInstances_5031_ = lean_ctor_get(v___y_4818_, 3);
                v_defEqCtx_x3f_5032_ = lean_ctor_get(v___y_4818_, 4);
                v_synthPendingDepth_5033_ = lean_ctor_get(v___y_4818_, 5);
                v_canUnfold_x3f_5034_ = lean_ctor_get(v___y_4818_, 6);
                v_univApprox_5035_ = lean_ctor_get_uint8(
                    v___y_4818_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_5036_ = lean_ctor_get_uint8(
                    v___y_4818_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_5037_ = lean_ctor_get_uint8(
                    v___y_4818_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                );
                if v_isShared_5027_ == 0 {
                    v_config_5039_ = v___x_5026_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_5054_ = lean_alloc_ctor(0, 0, (19) as u32);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5054_, 0 as u32, v_foApprox_5007_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5054_, 1 as u32, v_ctxApprox_5008_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5054_,
                        2 as u32,
                        v_quasiPatternApprox_5009_,
                    );
                    lean_ctor_set_uint8(v_reuseFailAlloc_5054_, 3 as u32, v_constApprox_5010_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5054_, 4 as u32, v_isDefEqStuckEx_5011_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5054_, 5 as u32, v_unificationHints_5012_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5054_, 6 as u32, v_proofIrrelevance_5013_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5054_,
                        7 as u32,
                        v_assignSyntheticOpaque_5014_,
                    );
                    lean_ctor_set_uint8(v_reuseFailAlloc_5054_, 8 as u32, v_offsetCnstrs_5015_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5054_, 10 as u32, v_etaStruct_5016_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5054_, 11 as u32, v_univApprox_5017_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5054_, 12 as u32, v_iota_5018_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5054_, 13 as u32, v_beta_5019_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5054_, 14 as u32, v_proj_5020_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5054_, 15 as u32, v_zeta_5021_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5054_, 16 as u32, v_zetaDelta_5022_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5054_, 17 as u32, v_zetaUnused_5023_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5054_, 18 as u32, v_zetaHave_5024_);
                    v_config_5039_ = v_reuseFailAlloc_5054_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                lean_ctor_set_uint8(v_config_5039_, 9 as u32, v_transparency_4809_);
                v___x_5040_ = l_Lean_Meta_Context_configKey(v___y_4818_);
                v___x_5041_ = 3u64;
                v___x_5042_ = lean_uint64_shift_right(v___x_5040_, v___x_5041_);
                v___x_5043_ = lean_uint64_shift_left(v___x_5042_, v___x_5041_);
                v___x_5044_ = l_Lean_Meta_TransparencyMode_toUInt64(v_transparency_4809_);
                v_key_5045_ = lean_uint64_lor(v___x_5043_, v___x_5044_);
                v___x_5046_ = lean_alloc_ctor(0, 1, (8) as u32);
                lean_ctor_set(v___x_5046_, 0, v_config_5039_);
                lean_ctor_set_uint64(
                    v___x_5046_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v_key_5045_,
                );
                lean_inc(v_canUnfold_x3f_5034_);
                lean_inc(v_synthPendingDepth_5033_);
                lean_inc(v_defEqCtx_x3f_5032_);
                lean_inc_ref(v_localInstances_5031_);
                lean_inc_ref(v_lctx_5030_);
                lean_inc(v_zetaDeltaSet_5029_);
                v___x_5047_ = lean_alloc_ctor(0, 7, (4) as u32);
                lean_ctor_set(v___x_5047_, 0, v___x_5046_);
                lean_ctor_set(v___x_5047_, 1, v_zetaDeltaSet_5029_);
                lean_ctor_set(v___x_5047_, 2, v_lctx_5030_);
                lean_ctor_set(v___x_5047_, 3, v_localInstances_5031_);
                lean_ctor_set(v___x_5047_, 4, v_defEqCtx_x3f_5032_);
                lean_ctor_set(v___x_5047_, 5, v_synthPendingDepth_5033_);
                lean_ctor_set(v___x_5047_, 6, v_canUnfold_x3f_5034_);
                lean_ctor_set_uint8(
                    v___x_5047_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                    v_trackZetaDelta_5028_,
                );
                lean_ctor_set_uint8(
                    v___x_5047_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                    v_univApprox_5035_,
                );
                lean_ctor_set_uint8(
                    v___x_5047_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_5036_,
                );
                lean_ctor_set_uint8(
                    v___x_5047_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_5037_,
                );
                v___x_5048_ = l_Lean_MVarId_apply(
                    v_g_4810_,
                    v_e_4811_,
                    v_cfg_4812_,
                    v___x_4813_,
                    v___x_5047_,
                    v___y_4819_,
                    v___y_4820_,
                    v___y_4821_,
                );
                lean_dec_ref_known(v___x_5047_, 7);
                if lean_obj_tag(v___x_5048_) == 0 {
                    v_a_5049_ = lean_ctor_get(v___x_5048_, 0);
                    lean_inc(v_a_5049_);
                    lean_dec_ref_known(v___x_5048_, 1);
                    v___x_5050_ = lean_box(0);
                    v___x_5051_ =
                        l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__4(
                            v___x_4953_,
                            v_a_5049_,
                            v___x_5050_,
                            v___y_4818_,
                            v___y_4819_,
                            v___y_4820_,
                            v___y_4821_,
                        );
                    if lean_obj_tag(v___x_5051_) == 0 {
                        v_a_5052_ = lean_ctor_get(v___x_5051_, 0);
                        lean_inc(v_a_5052_);
                        lean_dec_ref_known(v___x_5051_, 1);
                        v___x_5053_ = l_List_reverse___redArg(v_a_5052_);
                        v___y_4932_ = v___x_5005_;
                        v___y_4933_ = v_a_4951_;
                        v_a_4934_ = v___x_5053_;
                        state = 11;
                        continue;
                    } else {
                        v___y_4937_ = v_a_4951_;
                        v___y_4938_ = v___x_5005_;
                        v___y_4939_ = v___x_5051_;
                        state = 12;
                        continue;
                    }
                } else {
                    v___y_4937_ = v_a_4951_;
                    v___y_4938_ = v___x_5005_;
                    v___y_4939_ = v___x_5048_;
                    state = 12;
                    continue;
                }
            }
            20 => {
                v_trackZetaDelta_5080_ = lean_ctor_get_uint8(
                    v___y_4818_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_5081_ = lean_ctor_get(v___y_4818_, 1);
                v_lctx_5082_ = lean_ctor_get(v___y_4818_, 2);
                v_localInstances_5083_ = lean_ctor_get(v___y_4818_, 3);
                v_defEqCtx_x3f_5084_ = lean_ctor_get(v___y_4818_, 4);
                v_synthPendingDepth_5085_ = lean_ctor_get(v___y_4818_, 5);
                v_canUnfold_x3f_5086_ = lean_ctor_get(v___y_4818_, 6);
                v_univApprox_5087_ = lean_ctor_get_uint8(
                    v___y_4818_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_5088_ = lean_ctor_get_uint8(
                    v___y_4818_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_5089_ = lean_ctor_get_uint8(
                    v___y_4818_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                );
                if v_isShared_5079_ == 0 {
                    v_config_5091_ = v___x_5078_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_5113_ = lean_alloc_ctor(0, 0, (19) as u32);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5113_, 0 as u32, v_foApprox_5059_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5113_, 1 as u32, v_ctxApprox_5060_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5113_,
                        2 as u32,
                        v_quasiPatternApprox_5061_,
                    );
                    lean_ctor_set_uint8(v_reuseFailAlloc_5113_, 3 as u32, v_constApprox_5062_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5113_, 4 as u32, v_isDefEqStuckEx_5063_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5113_, 5 as u32, v_unificationHints_5064_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5113_, 6 as u32, v_proofIrrelevance_5065_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5113_,
                        7 as u32,
                        v_assignSyntheticOpaque_5066_,
                    );
                    lean_ctor_set_uint8(v_reuseFailAlloc_5113_, 8 as u32, v_offsetCnstrs_5067_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5113_, 10 as u32, v_etaStruct_5068_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5113_, 11 as u32, v_univApprox_5069_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5113_, 12 as u32, v_iota_5070_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5113_, 13 as u32, v_beta_5071_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5113_, 14 as u32, v_proj_5072_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5113_, 15 as u32, v_zeta_5073_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5113_, 16 as u32, v_zetaDelta_5074_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5113_, 17 as u32, v_zetaUnused_5075_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5113_, 18 as u32, v_zetaHave_5076_);
                    v_config_5091_ = v_reuseFailAlloc_5113_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                lean_ctor_set_uint8(v_config_5091_, 9 as u32, v_transparency_4809_);
                v___x_5092_ = l_Lean_Meta_Context_configKey(v___y_4818_);
                v___x_5093_ = 3u64;
                v___x_5094_ = lean_uint64_shift_right(v___x_5092_, v___x_5093_);
                v___x_5095_ = lean_uint64_shift_left(v___x_5094_, v___x_5093_);
                v___x_5096_ = l_Lean_Meta_TransparencyMode_toUInt64(v_transparency_4809_);
                v_key_5097_ = lean_uint64_lor(v___x_5095_, v___x_5096_);
                v___x_5098_ = lean_alloc_ctor(0, 1, (8) as u32);
                lean_ctor_set(v___x_5098_, 0, v_config_5091_);
                lean_ctor_set_uint64(
                    v___x_5098_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v_key_5097_,
                );
                lean_inc(v_canUnfold_x3f_5086_);
                lean_inc(v_synthPendingDepth_5085_);
                lean_inc(v_defEqCtx_x3f_5084_);
                lean_inc_ref(v_localInstances_5083_);
                lean_inc_ref(v_lctx_5082_);
                lean_inc(v_zetaDeltaSet_5081_);
                v___x_5099_ = lean_alloc_ctor(0, 7, (4) as u32);
                lean_ctor_set(v___x_5099_, 0, v___x_5098_);
                lean_ctor_set(v___x_5099_, 1, v_zetaDeltaSet_5081_);
                lean_ctor_set(v___x_5099_, 2, v_lctx_5082_);
                lean_ctor_set(v___x_5099_, 3, v_localInstances_5083_);
                lean_ctor_set(v___x_5099_, 4, v_defEqCtx_x3f_5084_);
                lean_ctor_set(v___x_5099_, 5, v_synthPendingDepth_5085_);
                lean_ctor_set(v___x_5099_, 6, v_canUnfold_x3f_5086_);
                lean_ctor_set_uint8(
                    v___x_5099_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                    v_trackZetaDelta_5080_,
                );
                lean_ctor_set_uint8(
                    v___x_5099_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                    v_univApprox_5087_,
                );
                lean_ctor_set_uint8(
                    v___x_5099_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_5088_,
                );
                lean_ctor_set_uint8(
                    v___x_5099_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_5089_,
                );
                v___x_5100_ = l_Lean_MVarId_apply(
                    v_g_4810_,
                    v_e_4811_,
                    v_cfg_4812_,
                    v___x_4813_,
                    v___x_5099_,
                    v___y_4819_,
                    v___y_4820_,
                    v___y_4821_,
                );
                lean_dec_ref_known(v___x_5099_, 7);
                if lean_obj_tag(v___x_5100_) == 0 {
                    v_a_5101_ = lean_ctor_get(v___x_5100_, 0);
                    lean_inc(v_a_5101_);
                    lean_dec_ref_known(v___x_5100_, 1);
                    v___x_5102_ = lean_box(0);
                    v___x_5103_ =
                        l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(
                            v___x_5057_,
                            v_hasTrace_4824_,
                            v_a_5101_,
                            v___x_5102_,
                            v___y_4818_,
                            v___y_4819_,
                            v___y_4820_,
                            v___y_4821_,
                        );
                    if lean_obj_tag(v___x_5103_) == 0 {
                        v_a_5104_ = lean_ctor_get(v___x_5103_, 0);
                        v_isSharedCheck_5112_ = (!lean_is_exclusive(v___x_5103_)) as u8;
                        if v_isSharedCheck_5112_ == 0 {
                            v___x_5106_ = v___x_5103_;
                            v_isShared_5107_ = v_isSharedCheck_5112_;
                            state = 22;
                            continue;
                        } else {
                            lean_inc(v_a_5104_);
                            lean_dec(v___x_5103_);
                            v___x_5106_ = lean_box(0);
                            v_isShared_5107_ = v_isSharedCheck_5112_;
                            state = 22;
                            continue;
                        }
                    } else {
                        return v___x_5103_;
                    }
                } else {
                    return v___x_5100_;
                }
            }
            22 => {
                v___x_5108_ = l_List_reverse___redArg(v_a_5104_);
                if v_isShared_5107_ == 0 {
                    lean_ctor_set(v___x_5106_, 0, v___x_5108_);
                    v___x_5110_ = v___x_5106_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_5111_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5111_, 0, v___x_5108_);
                    v___x_5110_ = v_reuseFailAlloc_5111_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_5110_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___boxed(
    mut v_transparency_5115_: *mut LeanObject,
    mut v_g_5116_: *mut LeanObject,
    mut v_e_5117_: *mut LeanObject,
    mut v_cfg_5118_: *mut LeanObject,
    mut v___x_5119_: *mut LeanObject,
    mut v___x_5120_: *mut LeanObject,
    mut v___x_5121_: *mut LeanObject,
    mut v___x_5122_: *mut LeanObject,
    mut v___f_5123_: *mut LeanObject,
    mut v___y_5124_: *mut LeanObject,
    mut v___y_5125_: *mut LeanObject,
    mut v___y_5126_: *mut LeanObject,
    mut v___y_5127_: *mut LeanObject,
    mut v___y_5128_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_transparency_boxed_5129_: u8 = 0;
    let mut v___x_14817__boxed_5130_: u8 = 0;
    let mut v_res_5131_: *mut LeanObject = core::ptr::null_mut();
    v_transparency_boxed_5129_ = (lean_unbox(v_transparency_5115_) as u8);
    v___x_14817__boxed_5130_ = (lean_unbox(v___x_5121_) as u8);
    v_res_5131_ = l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1(
        v_transparency_boxed_5129_,
        v_g_5116_,
        v_e_5117_,
        v_cfg_5118_,
        v___x_5119_,
        v___x_5120_,
        v___x_14817__boxed_5130_,
        v___x_5122_,
        v___f_5123_,
        v___y_5124_,
        v___y_5125_,
        v___y_5126_,
        v___y_5127_,
    );
    lean_dec(v___y_5127_);
    lean_dec_ref(v___y_5126_);
    lean_dec(v___y_5125_);
    lean_dec_ref(v___y_5124_);
    return v_res_5131_;
}
pub unsafe fn l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2(
    mut v_transparency_5133_: u8,
    mut v_g_5134_: *mut LeanObject,
    mut v_cfg_5135_: *mut LeanObject,
    mut v_e_5136_: *mut LeanObject,
    mut v___y_5137_: *mut LeanObject,
    mut v___y_5138_: *mut LeanObject,
    mut v___y_5139_: *mut LeanObject,
    mut v___y_5140_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5145_: u8 = 0;
    let mut v___x_5146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5150_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_e_5136_);
    v___f_5142_ = lean_alloc_closure(
        l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___boxed as *mut core::ffi::c_void,
        7,
        1,
    );
    lean_closure_set(v___f_5142_, 0, v_e_5136_);
    v___x_5143_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_;
    v___x_5144_ = lean_box(0);
    v___x_5145_ = 1;
    v___x_5146_ = l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___closed__0;
    v___x_5147_ = lean_box((v_transparency_5133_) as usize);
    v___x_5148_ = lean_box((v___x_5145_) as usize);
    v___f_5149_ = lean_alloc_closure(
        l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___boxed as *mut core::ffi::c_void,
        14,
        9,
    );
    lean_closure_set(v___f_5149_, 0, v___x_5147_);
    lean_closure_set(v___f_5149_, 1, v_g_5134_);
    lean_closure_set(v___f_5149_, 2, v_e_5136_);
    lean_closure_set(v___f_5149_, 3, v_cfg_5135_);
    lean_closure_set(v___f_5149_, 4, v___x_5144_);
    lean_closure_set(v___f_5149_, 5, v___x_5143_);
    lean_closure_set(v___f_5149_, 6, v___x_5148_);
    lean_closure_set(v___f_5149_, 7, v___x_5146_);
    lean_closure_set(v___f_5149_, 8, v___f_5142_);
    v___x_5150_ = l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg(
        v___f_5149_,
        v___y_5137_,
        v___y_5138_,
        v___y_5139_,
        v___y_5140_,
    );
    return v___x_5150_;
}
pub unsafe fn l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___boxed(
    mut v_transparency_5151_: *mut LeanObject,
    mut v_g_5152_: *mut LeanObject,
    mut v_cfg_5153_: *mut LeanObject,
    mut v_e_5154_: *mut LeanObject,
    mut v___y_5155_: *mut LeanObject,
    mut v___y_5156_: *mut LeanObject,
    mut v___y_5157_: *mut LeanObject,
    mut v___y_5158_: *mut LeanObject,
    mut v___y_5159_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_transparency_boxed_5160_: u8 = 0;
    let mut v_res_5161_: *mut LeanObject = core::ptr::null_mut();
    v_transparency_boxed_5160_ = (lean_unbox(v_transparency_5151_) as u8);
    v_res_5161_ = l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2(
        v_transparency_boxed_5160_,
        v_g_5152_,
        v_cfg_5153_,
        v_e_5154_,
        v___y_5155_,
        v___y_5156_,
        v___y_5157_,
        v___y_5158_,
    );
    lean_dec(v___y_5158_);
    lean_dec_ref(v___y_5157_);
    lean_dec(v___y_5156_);
    lean_dec_ref(v___y_5155_);
    return v_res_5161_;
}
pub unsafe fn l_Lean_Meta_SolveByElim_applyTactics___redArg(
    mut v_cfg_5162_: *mut LeanObject,
    mut v_transparency_5163_: u8,
    mut v_lemmas_5164_: *mut LeanObject,
    mut v_g_5165_: *mut LeanObject,
    mut v_a_5166_: *mut LeanObject,
    mut v_a_5167_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5173_: u8 = 0;
    let mut v___x_5174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5180_: u8 = 0;
    let mut v_a_5181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5184_: u8 = 0;
    let mut v___x_5186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5188_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5169_ =
                    l_Lean_Meta_Iterator_ofList___redArg(v_lemmas_5164_, v_a_5166_, v_a_5167_);
                if lean_obj_tag(v___x_5169_) == 0 {
                    v_a_5170_ = lean_ctor_get(v___x_5169_, 0);
                    v_isSharedCheck_5180_ = (!lean_is_exclusive(v___x_5169_)) as u8;
                    if v_isSharedCheck_5180_ == 0 {
                        v___x_5172_ = v___x_5169_;
                        v_isShared_5173_ = v_isSharedCheck_5180_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5170_);
                        lean_dec(v___x_5169_);
                        v___x_5172_ = lean_box(0);
                        v_isShared_5173_ = v_isSharedCheck_5180_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_g_5165_);
                    lean_dec_ref(v_cfg_5162_);
                    v_a_5181_ = lean_ctor_get(v___x_5169_, 0);
                    v_isSharedCheck_5188_ = (!lean_is_exclusive(v___x_5169_)) as u8;
                    if v_isSharedCheck_5188_ == 0 {
                        v___x_5183_ = v___x_5169_;
                        v_isShared_5184_ = v_isSharedCheck_5188_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5181_);
                        lean_dec(v___x_5169_);
                        v___x_5183_ = lean_box(0);
                        v_isShared_5184_ = v_isSharedCheck_5188_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5174_ = lean_box((v_transparency_5163_) as usize);
                v___f_5175_ = lean_alloc_closure(
                    l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___boxed
                        as *mut core::ffi::c_void,
                    9,
                    3,
                );
                lean_closure_set(v___f_5175_, 0, v___x_5174_);
                lean_closure_set(v___f_5175_, 1, v_g_5165_);
                lean_closure_set(v___f_5175_, 2, v_cfg_5162_);
                v___x_5176_ = lean_alloc_closure(
                    l___private_Lean_Meta_Iterator_0__Lean_Meta_Iterator_filterMapM___next___boxed
                        as *mut core::ffi::c_void,
                    9,
                    4,
                );
                lean_closure_set(v___x_5176_, 0, lean_box(0));
                lean_closure_set(v___x_5176_, 1, lean_box(0));
                lean_closure_set(v___x_5176_, 2, v___f_5175_);
                lean_closure_set(v___x_5176_, 3, v_a_5170_);
                if v_isShared_5173_ == 0 {
                    lean_ctor_set(v___x_5172_, 0, v___x_5176_);
                    v___x_5178_ = v___x_5172_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5179_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5179_, 0, v___x_5176_);
                    v___x_5178_ = v_reuseFailAlloc_5179_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5178_;
            }
            3 => {
                if v_isShared_5184_ == 0 {
                    v___x_5186_ = v___x_5183_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5187_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5187_, 0, v_a_5181_);
                    v___x_5186_ = v_reuseFailAlloc_5187_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5186_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_SolveByElim_applyTactics___redArg___boxed(
    mut v_cfg_5189_: *mut LeanObject,
    mut v_transparency_5190_: *mut LeanObject,
    mut v_lemmas_5191_: *mut LeanObject,
    mut v_g_5192_: *mut LeanObject,
    mut v_a_5193_: *mut LeanObject,
    mut v_a_5194_: *mut LeanObject,
    mut v_a_5195_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_transparency_boxed_5196_: u8 = 0;
    let mut v_res_5197_: *mut LeanObject = core::ptr::null_mut();
    v_transparency_boxed_5196_ = (lean_unbox(v_transparency_5190_) as u8);
    v_res_5197_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(
        v_cfg_5189_,
        v_transparency_boxed_5196_,
        v_lemmas_5191_,
        v_g_5192_,
        v_a_5193_,
        v_a_5194_,
    );
    lean_dec(v_a_5194_);
    lean_dec(v_a_5193_);
    return v_res_5197_;
}
pub unsafe fn l_Lean_Meta_SolveByElim_applyTactics(
    mut v_cfg_5198_: *mut LeanObject,
    mut v_transparency_5199_: u8,
    mut v_lemmas_5200_: *mut LeanObject,
    mut v_g_5201_: *mut LeanObject,
    mut v_a_5202_: *mut LeanObject,
    mut v_a_5203_: *mut LeanObject,
    mut v_a_5204_: *mut LeanObject,
    mut v_a_5205_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5207_: *mut LeanObject = core::ptr::null_mut();
    v___x_5207_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(
        v_cfg_5198_,
        v_transparency_5199_,
        v_lemmas_5200_,
        v_g_5201_,
        v_a_5203_,
        v_a_5205_,
    );
    return v___x_5207_;
}
pub unsafe fn l_Lean_Meta_SolveByElim_applyTactics___boxed(
    mut v_cfg_5208_: *mut LeanObject,
    mut v_transparency_5209_: *mut LeanObject,
    mut v_lemmas_5210_: *mut LeanObject,
    mut v_g_5211_: *mut LeanObject,
    mut v_a_5212_: *mut LeanObject,
    mut v_a_5213_: *mut LeanObject,
    mut v_a_5214_: *mut LeanObject,
    mut v_a_5215_: *mut LeanObject,
    mut v_a_5216_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_transparency_boxed_5217_: u8 = 0;
    let mut v_res_5218_: *mut LeanObject = core::ptr::null_mut();
    v_transparency_boxed_5217_ = (lean_unbox(v_transparency_5209_) as u8);
    v_res_5218_ = l_Lean_Meta_SolveByElim_applyTactics(
        v_cfg_5208_,
        v_transparency_boxed_5217_,
        v_lemmas_5210_,
        v_g_5211_,
        v_a_5212_,
        v_a_5213_,
        v_a_5214_,
        v_a_5215_,
    );
    lean_dec(v_a_5215_);
    lean_dec_ref(v_a_5214_);
    lean_dec(v_a_5213_);
    lean_dec_ref(v_a_5212_);
    return v_res_5218_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4(
    mut v_00_u03b1_5219_: *mut LeanObject,
    mut v_x_5220_: *mut LeanObject,
    mut v___y_5221_: *mut LeanObject,
    mut v___y_5222_: *mut LeanObject,
    mut v___y_5223_: *mut LeanObject,
    mut v___y_5224_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5226_: *mut LeanObject = core::ptr::null_mut();
    v___x_5226_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4___redArg(v_x_5220_);
    return v___x_5226_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4___boxed(
    mut v_00_u03b1_5227_: *mut LeanObject,
    mut v_x_5228_: *mut LeanObject,
    mut v___y_5229_: *mut LeanObject,
    mut v___y_5230_: *mut LeanObject,
    mut v___y_5231_: *mut LeanObject,
    mut v___y_5232_: *mut LeanObject,
    mut v___y_5233_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5234_: *mut LeanObject = core::ptr::null_mut();
    v_res_5234_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4(v_00_u03b1_5227_, v_x_5228_, v___y_5229_, v___y_5230_, v___y_5231_, v___y_5232_);
    lean_dec(v___y_5232_);
    lean_dec_ref(v___y_5231_);
    lean_dec(v___y_5230_);
    lean_dec_ref(v___y_5229_);
    return v_res_5234_;
}
pub unsafe fn l_Lean_Meta_SolveByElim_applyFirst(
    mut v_cfg_5235_: *mut LeanObject,
    mut v_transparency_5236_: u8,
    mut v_lemmas_5237_: *mut LeanObject,
    mut v_g_5238_: *mut LeanObject,
    mut v_a_5239_: *mut LeanObject,
    mut v_a_5240_: *mut LeanObject,
    mut v_a_5241_: *mut LeanObject,
    mut v_a_5242_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5250_: u8 = 0;
    let mut v___x_5252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5254_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5244_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(
                    v_cfg_5235_,
                    v_transparency_5236_,
                    v_lemmas_5237_,
                    v_g_5238_,
                    v_a_5240_,
                    v_a_5242_,
                );
                if lean_obj_tag(v___x_5244_) == 0 {
                    v_a_5245_ = lean_ctor_get(v___x_5244_, 0);
                    lean_inc(v_a_5245_);
                    lean_dec_ref_known(v___x_5244_, 1);
                    v___x_5246_ = l_Lean_Meta_Iterator_head___redArg(
                        v_a_5245_, v_a_5239_, v_a_5240_, v_a_5241_, v_a_5242_,
                    );
                    return v___x_5246_;
                } else {
                    v_a_5247_ = lean_ctor_get(v___x_5244_, 0);
                    v_isSharedCheck_5254_ = (!lean_is_exclusive(v___x_5244_)) as u8;
                    if v_isSharedCheck_5254_ == 0 {
                        v___x_5249_ = v___x_5244_;
                        v_isShared_5250_ = v_isSharedCheck_5254_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5247_);
                        lean_dec(v___x_5244_);
                        v___x_5249_ = lean_box(0);
                        v_isShared_5250_ = v_isSharedCheck_5254_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5250_ == 0 {
                    v___x_5252_ = v___x_5249_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5253_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5253_, 0, v_a_5247_);
                    v___x_5252_ = v_reuseFailAlloc_5253_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5252_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_SolveByElim_applyFirst___boxed(
    mut v_cfg_5255_: *mut LeanObject,
    mut v_transparency_5256_: *mut LeanObject,
    mut v_lemmas_5257_: *mut LeanObject,
    mut v_g_5258_: *mut LeanObject,
    mut v_a_5259_: *mut LeanObject,
    mut v_a_5260_: *mut LeanObject,
    mut v_a_5261_: *mut LeanObject,
    mut v_a_5262_: *mut LeanObject,
    mut v_a_5263_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_transparency_boxed_5264_: u8 = 0;
    let mut v_res_5265_: *mut LeanObject = core::ptr::null_mut();
    v_transparency_boxed_5264_ = (lean_unbox(v_transparency_5256_) as u8);
    v_res_5265_ = l_Lean_Meta_SolveByElim_applyFirst(
        v_cfg_5255_,
        v_transparency_boxed_5264_,
        v_lemmas_5257_,
        v_g_5258_,
        v_a_5259_,
        v_a_5260_,
        v_a_5261_,
        v_a_5262_,
    );
    lean_dec(v_a_5262_);
    lean_dec_ref(v_a_5261_);
    lean_dec(v_a_5260_);
    lean_dec_ref(v_a_5259_);
    return v_res_5265_;
}
pub unsafe fn l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___lam__0(
    mut v_x_5266_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplyRulesConfig_5267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBacktrackConfig_5268_: *mut LeanObject = core::ptr::null_mut();
    v_toApplyRulesConfig_5267_ = lean_ctor_get(v_x_5266_, 0);
    v_toBacktrackConfig_5268_ = lean_ctor_get(v_toApplyRulesConfig_5267_, 0);
    lean_inc_ref(v_toBacktrackConfig_5268_);
    return v_toBacktrackConfig_5268_;
}
pub unsafe fn l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___lam__0___boxed(
    mut v_x_5269_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5270_: *mut LeanObject = core::ptr::null_mut();
    v_res_5270_ =
        l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___lam__0(v_x_5269_);
    lean_dec_ref(v_x_5269_);
    return v_res_5270_;
}
pub unsafe fn l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0(
    mut v_test_5273_: *mut LeanObject,
    mut v_discharge_5274_: *mut LeanObject,
    mut v_g_5275_: *mut LeanObject,
    mut v___y_5276_: *mut LeanObject,
    mut v___y_5277_: *mut LeanObject,
    mut v___y_5278_: *mut LeanObject,
    mut v___y_5279_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5285_: u8 = 0;
    let mut v___x_5286_: u8 = 0;
    let mut v___x_5287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5292_: u8 = 0;
    let mut v_a_5293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5296_: u8 = 0;
    let mut v___x_5298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5300_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_5279_);
                lean_inc_ref(v___y_5278_);
                lean_inc(v___y_5277_);
                lean_inc_ref(v___y_5276_);
                lean_inc(v_g_5275_);
                v___x_5281_ = lean_apply_6(
                    v_test_5273_,
                    v_g_5275_,
                    v___y_5276_,
                    v___y_5277_,
                    v___y_5278_,
                    v___y_5279_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_5281_) == 0 {
                    v_a_5282_ = lean_ctor_get(v___x_5281_, 0);
                    v_isSharedCheck_5292_ = (!lean_is_exclusive(v___x_5281_)) as u8;
                    if v_isSharedCheck_5292_ == 0 {
                        v___x_5284_ = v___x_5281_;
                        v_isShared_5285_ = v_isSharedCheck_5292_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5282_);
                        lean_dec(v___x_5281_);
                        v___x_5284_ = lean_box(0);
                        v_isShared_5285_ = v_isSharedCheck_5292_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_g_5275_);
                    lean_dec_ref(v_discharge_5274_);
                    v_a_5293_ = lean_ctor_get(v___x_5281_, 0);
                    v_isSharedCheck_5300_ = (!lean_is_exclusive(v___x_5281_)) as u8;
                    if v_isSharedCheck_5300_ == 0 {
                        v___x_5295_ = v___x_5281_;
                        v_isShared_5296_ = v_isSharedCheck_5300_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5293_);
                        lean_dec(v___x_5281_);
                        v___x_5295_ = lean_box(0);
                        v_isShared_5296_ = v_isSharedCheck_5300_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5286_ = (lean_unbox(v_a_5282_) as u8);
                lean_dec(v_a_5282_);
                if v___x_5286_ == 0 {
                    lean_del_object(v___x_5284_);
                    lean_inc(v___y_5279_);
                    lean_inc_ref(v___y_5278_);
                    lean_inc(v___y_5277_);
                    lean_inc_ref(v___y_5276_);
                    v___x_5287_ = lean_apply_6(
                        v_discharge_5274_,
                        v_g_5275_,
                        v___y_5276_,
                        v___y_5277_,
                        v___y_5278_,
                        v___y_5279_,
                        lean_box(0),
                    );
                    return v___x_5287_;
                } else {
                    lean_dec(v_g_5275_);
                    lean_dec_ref(v_discharge_5274_);
                    v___x_5288_ = lean_box(0);
                    if v_isShared_5285_ == 0 {
                        lean_ctor_set(v___x_5284_, 0, v___x_5288_);
                        v___x_5290_ = v___x_5284_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5291_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5291_, 0, v___x_5288_);
                        v___x_5290_ = v_reuseFailAlloc_5291_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5290_;
            }
            3 => {
                if v_isShared_5296_ == 0 {
                    v___x_5298_ = v___x_5295_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5299_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5299_, 0, v_a_5293_);
                    v___x_5298_ = v_reuseFailAlloc_5299_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5298_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0___boxed(
    mut v_test_5301_: *mut LeanObject,
    mut v_discharge_5302_: *mut LeanObject,
    mut v_g_5303_: *mut LeanObject,
    mut v___y_5304_: *mut LeanObject,
    mut v___y_5305_: *mut LeanObject,
    mut v___y_5306_: *mut LeanObject,
    mut v___y_5307_: *mut LeanObject,
    mut v___y_5308_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5309_: *mut LeanObject = core::ptr::null_mut();
    v_res_5309_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0(
        v_test_5301_,
        v_discharge_5302_,
        v_g_5303_,
        v___y_5304_,
        v___y_5305_,
        v___y_5306_,
        v___y_5307_,
    );
    lean_dec(v___y_5307_);
    lean_dec_ref(v___y_5306_);
    lean_dec(v___y_5305_);
    lean_dec_ref(v___y_5304_);
    return v_res_5309_;
}
pub unsafe fn l_Lean_Meta_SolveByElim_SolveByElimConfig_accept(
    mut v_cfg_5310_: *mut LeanObject,
    mut v_test_5311_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplyRulesConfig_5312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBacktrackConfig_5313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_backtracking_5314_: u8 = 0;
    let mut v_intro_5315_: u8 = 0;
    let mut v_constructor_5316_: u8 = 0;
    let mut v_suggestions_5317_: u8 = 0;
    let mut v___x_5319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5320_: u8 = 0;
    let mut v_toApplyConfig_5321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_transparency_5322_: u8 = 0;
    let mut v_symm_5323_: u8 = 0;
    let mut v_exfalso_5324_: u8 = 0;
    let mut v___x_5326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5327_: u8 = 0;
    let mut v_maxDepth_5328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proc_5329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suspend_5330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_discharge_5331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_commitIndependentGoals_5332_: u8 = 0;
    let mut v___x_5334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5335_: u8 = 0;
    let mut v___f_5336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5346_: u8 = 0;
    let mut v_isSharedCheck_5347_: u8 = 0;
    let mut v_unused_5348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5349_: u8 = 0;
    let mut v_unused_5350_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplyRulesConfig_5312_ = lean_ctor_get(v_cfg_5310_, 0);
                lean_inc_ref(v_toApplyRulesConfig_5312_);
                v_toBacktrackConfig_5313_ = lean_ctor_get(v_toApplyRulesConfig_5312_, 0);
                lean_inc_ref(v_toBacktrackConfig_5313_);
                v_backtracking_5314_ = lean_ctor_get_uint8(
                    v_cfg_5310_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_intro_5315_ = lean_ctor_get_uint8(
                    v_cfg_5310_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                );
                v_constructor_5316_ = lean_ctor_get_uint8(
                    v_cfg_5310_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 2) as u32,
                );
                v_suggestions_5317_ = lean_ctor_get_uint8(
                    v_cfg_5310_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 3) as u32,
                );
                v_isSharedCheck_5349_ = (!lean_is_exclusive(v_cfg_5310_)) as u8;
                if v_isSharedCheck_5349_ == 0 {
                    v_unused_5350_ = lean_ctor_get(v_cfg_5310_, 0);
                    lean_dec(v_unused_5350_);
                    v___x_5319_ = v_cfg_5310_;
                    v_isShared_5320_ = v_isSharedCheck_5349_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v_cfg_5310_);
                    v___x_5319_ = lean_box(0);
                    v_isShared_5320_ = v_isSharedCheck_5349_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toApplyConfig_5321_ = lean_ctor_get(v_toApplyRulesConfig_5312_, 1);
                v_transparency_5322_ = lean_ctor_get_uint8(
                    v_toApplyRulesConfig_5312_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                );
                v_symm_5323_ = lean_ctor_get_uint8(
                    v_toApplyRulesConfig_5312_,
                    (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                );
                v_exfalso_5324_ = lean_ctor_get_uint8(
                    v_toApplyRulesConfig_5312_,
                    (core::mem::size_of::<*mut LeanObject>() * 2 + 2) as u32,
                );
                v_isSharedCheck_5347_ = (!lean_is_exclusive(v_toApplyRulesConfig_5312_)) as u8;
                if v_isSharedCheck_5347_ == 0 {
                    v_unused_5348_ = lean_ctor_get(v_toApplyRulesConfig_5312_, 0);
                    lean_dec(v_unused_5348_);
                    v___x_5326_ = v_toApplyRulesConfig_5312_;
                    v_isShared_5327_ = v_isSharedCheck_5347_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_toApplyConfig_5321_);
                    lean_dec(v_toApplyRulesConfig_5312_);
                    v___x_5326_ = lean_box(0);
                    v_isShared_5327_ = v_isSharedCheck_5347_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_maxDepth_5328_ = lean_ctor_get(v_toBacktrackConfig_5313_, 0);
                v_proc_5329_ = lean_ctor_get(v_toBacktrackConfig_5313_, 1);
                v_suspend_5330_ = lean_ctor_get(v_toBacktrackConfig_5313_, 2);
                v_discharge_5331_ = lean_ctor_get(v_toBacktrackConfig_5313_, 3);
                v_commitIndependentGoals_5332_ = lean_ctor_get_uint8(
                    v_toBacktrackConfig_5313_,
                    (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                );
                v_isSharedCheck_5346_ = (!lean_is_exclusive(v_toBacktrackConfig_5313_)) as u8;
                if v_isSharedCheck_5346_ == 0 {
                    v___x_5334_ = v_toBacktrackConfig_5313_;
                    v_isShared_5335_ = v_isSharedCheck_5346_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_discharge_5331_);
                    lean_inc(v_suspend_5330_);
                    lean_inc(v_proc_5329_);
                    lean_inc(v_maxDepth_5328_);
                    lean_dec(v_toBacktrackConfig_5313_);
                    v___x_5334_ = lean_box(0);
                    v_isShared_5335_ = v_isSharedCheck_5346_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___f_5336_ = lean_alloc_closure(
                    l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0___boxed
                        as *mut core::ffi::c_void,
                    8,
                    2,
                );
                lean_closure_set(v___f_5336_, 0, v_test_5311_);
                lean_closure_set(v___f_5336_, 1, v_discharge_5331_);
                if v_isShared_5335_ == 0 {
                    lean_ctor_set(v___x_5334_, 3, v___f_5336_);
                    v___x_5338_ = v___x_5334_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5345_ = lean_alloc_ctor(0, 4, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5345_, 0, v_maxDepth_5328_);
                    lean_ctor_set(v_reuseFailAlloc_5345_, 1, v_proc_5329_);
                    lean_ctor_set(v_reuseFailAlloc_5345_, 2, v_suspend_5330_);
                    lean_ctor_set(v_reuseFailAlloc_5345_, 3, v___f_5336_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5345_,
                        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                        v_commitIndependentGoals_5332_,
                    );
                    v___x_5338_ = v_reuseFailAlloc_5345_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_5327_ == 0 {
                    lean_ctor_set(v___x_5326_, 0, v___x_5338_);
                    v___x_5340_ = v___x_5326_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5344_ = lean_alloc_ctor(0, 2, (3) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5344_, 0, v___x_5338_);
                    lean_ctor_set(v_reuseFailAlloc_5344_, 1, v_toApplyConfig_5321_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5344_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        v_transparency_5322_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5344_,
                        (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                        v_symm_5323_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5344_,
                        (core::mem::size_of::<*mut LeanObject>() * 2 + 2) as u32,
                        v_exfalso_5324_,
                    );
                    v___x_5340_ = v_reuseFailAlloc_5344_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_5320_ == 0 {
                    lean_ctor_set(v___x_5319_, 0, v___x_5340_);
                    v___x_5342_ = v___x_5319_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5343_ = lean_alloc_ctor(0, 1, (4) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5343_, 0, v___x_5340_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5343_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_backtracking_5314_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5343_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                        v_intro_5315_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5343_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 2) as u32,
                        v_constructor_5316_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5343_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 3) as u32,
                        v_suggestions_5317_,
                    );
                    v___x_5342_ = v_reuseFailAlloc_5343_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5342_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0(
    mut v_proc_5351_: *mut LeanObject,
    mut v_proc_5352_: *mut LeanObject,
    mut v_orig_5353_: *mut LeanObject,
    mut v_goals_5354_: *mut LeanObject,
    mut v___y_5355_: *mut LeanObject,
    mut v___y_5356_: *mut LeanObject,
    mut v___y_5357_: *mut LeanObject,
    mut v___y_5358_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_5361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5367_: u8 = 0;
    let mut v___x_5368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5373_: u8 = 0;
    let mut v_a_5374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5377_: u8 = 0;
    let mut v___y_5379_: u8 = 0;
    let mut v___x_5380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5384_: u8 = 0;
    let mut v___x_5385_: u8 = 0;
    let mut v_isSharedCheck_5386_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_goals_5354_) == 0 {
                    lean_dec_ref(v_proc_5352_);
                    lean_inc(v___y_5358_);
                    lean_inc_ref(v___y_5357_);
                    lean_inc(v___y_5356_);
                    lean_inc_ref(v___y_5355_);
                    v___x_5360_ = lean_apply_7(
                        v_proc_5351_,
                        v_orig_5353_,
                        v_goals_5354_,
                        v___y_5355_,
                        v___y_5356_,
                        v___y_5357_,
                        v___y_5358_,
                        lean_box(0),
                    );
                    return v___x_5360_;
                } else {
                    v_head_5361_ = lean_ctor_get(v_goals_5354_, 0);
                    v_tail_5362_ = lean_ctor_get(v_goals_5354_, 1);
                    lean_inc(v___y_5358_);
                    lean_inc_ref(v___y_5357_);
                    lean_inc(v___y_5356_);
                    lean_inc_ref(v___y_5355_);
                    lean_inc(v_head_5361_);
                    v___x_5363_ = lean_apply_6(
                        v_proc_5352_,
                        v_head_5361_,
                        v___y_5355_,
                        v___y_5356_,
                        v___y_5357_,
                        v___y_5358_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_5363_) == 0 {
                        lean_inc(v_tail_5362_);
                        lean_dec_ref_known(v_goals_5354_, 2);
                        lean_dec(v_orig_5353_);
                        lean_dec_ref(v_proc_5351_);
                        v_a_5364_ = lean_ctor_get(v___x_5363_, 0);
                        v_isSharedCheck_5373_ = (!lean_is_exclusive(v___x_5363_)) as u8;
                        if v_isSharedCheck_5373_ == 0 {
                            v___x_5366_ = v___x_5363_;
                            v_isShared_5367_ = v_isSharedCheck_5373_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5364_);
                            lean_dec(v___x_5363_);
                            v___x_5366_ = lean_box(0);
                            v_isShared_5367_ = v_isSharedCheck_5373_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_5374_ = lean_ctor_get(v___x_5363_, 0);
                        v_isSharedCheck_5386_ = (!lean_is_exclusive(v___x_5363_)) as u8;
                        if v_isSharedCheck_5386_ == 0 {
                            v___x_5376_ = v___x_5363_;
                            v_isShared_5377_ = v_isSharedCheck_5386_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_5374_);
                            lean_dec(v___x_5363_);
                            v___x_5376_ = lean_box(0);
                            v_isShared_5377_ = v_isSharedCheck_5386_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5368_ = l_List_appendTR___redArg(v_a_5364_, v_tail_5362_);
                v___x_5369_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_5369_, 0, v___x_5368_);
                if v_isShared_5367_ == 0 {
                    lean_ctor_set(v___x_5366_, 0, v___x_5369_);
                    v___x_5371_ = v___x_5366_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5372_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5372_, 0, v___x_5369_);
                    v___x_5371_ = v_reuseFailAlloc_5372_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5371_;
            }
            3 => {
                v___x_5384_ = l_Lean_Exception_isInterrupt(v_a_5374_);
                if v___x_5384_ == 0 {
                    lean_inc(v_a_5374_);
                    v___x_5385_ = l_Lean_Exception_isRuntime(v_a_5374_);
                    v___y_5379_ = v___x_5385_;
                    state = 4;
                    continue;
                } else {
                    v___y_5379_ = v___x_5384_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v___y_5379_ == 0 {
                    lean_del_object(v___x_5376_);
                    lean_dec(v_a_5374_);
                    lean_inc(v___y_5358_);
                    lean_inc_ref(v___y_5357_);
                    lean_inc(v___y_5356_);
                    lean_inc_ref(v___y_5355_);
                    v___x_5380_ = lean_apply_7(
                        v_proc_5351_,
                        v_orig_5353_,
                        v_goals_5354_,
                        v___y_5355_,
                        v___y_5356_,
                        v___y_5357_,
                        v___y_5358_,
                        lean_box(0),
                    );
                    return v___x_5380_;
                } else {
                    lean_dec_ref_known(v_goals_5354_, 2);
                    lean_dec(v_orig_5353_);
                    lean_dec_ref(v_proc_5351_);
                    if v_isShared_5377_ == 0 {
                        v___x_5382_ = v___x_5376_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5383_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5383_, 0, v_a_5374_);
                        v___x_5382_ = v_reuseFailAlloc_5383_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_5382_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0___boxed(
    mut v_proc_5387_: *mut LeanObject,
    mut v_proc_5388_: *mut LeanObject,
    mut v_orig_5389_: *mut LeanObject,
    mut v_goals_5390_: *mut LeanObject,
    mut v___y_5391_: *mut LeanObject,
    mut v___y_5392_: *mut LeanObject,
    mut v___y_5393_: *mut LeanObject,
    mut v___y_5394_: *mut LeanObject,
    mut v___y_5395_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5396_: *mut LeanObject = core::ptr::null_mut();
    v_res_5396_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0(
        v_proc_5387_,
        v_proc_5388_,
        v_orig_5389_,
        v_goals_5390_,
        v___y_5391_,
        v___y_5392_,
        v___y_5393_,
        v___y_5394_,
    );
    lean_dec(v___y_5394_);
    lean_dec_ref(v___y_5393_);
    lean_dec(v___y_5392_);
    lean_dec_ref(v___y_5391_);
    return v_res_5396_;
}
pub unsafe fn l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc(
    mut v_cfg_5397_: *mut LeanObject,
    mut v_proc_5398_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplyRulesConfig_5399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBacktrackConfig_5400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_backtracking_5401_: u8 = 0;
    let mut v_intro_5402_: u8 = 0;
    let mut v_constructor_5403_: u8 = 0;
    let mut v_suggestions_5404_: u8 = 0;
    let mut v___x_5406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5407_: u8 = 0;
    let mut v_toApplyConfig_5408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_transparency_5409_: u8 = 0;
    let mut v_symm_5410_: u8 = 0;
    let mut v_exfalso_5411_: u8 = 0;
    let mut v___x_5413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5414_: u8 = 0;
    let mut v_maxDepth_5415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proc_5416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suspend_5417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_discharge_5418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_commitIndependentGoals_5419_: u8 = 0;
    let mut v___x_5421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5422_: u8 = 0;
    let mut v___f_5423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5433_: u8 = 0;
    let mut v_isSharedCheck_5434_: u8 = 0;
    let mut v_unused_5435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5436_: u8 = 0;
    let mut v_unused_5437_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplyRulesConfig_5399_ = lean_ctor_get(v_cfg_5397_, 0);
                lean_inc_ref(v_toApplyRulesConfig_5399_);
                v_toBacktrackConfig_5400_ = lean_ctor_get(v_toApplyRulesConfig_5399_, 0);
                lean_inc_ref(v_toBacktrackConfig_5400_);
                v_backtracking_5401_ = lean_ctor_get_uint8(
                    v_cfg_5397_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_intro_5402_ = lean_ctor_get_uint8(
                    v_cfg_5397_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                );
                v_constructor_5403_ = lean_ctor_get_uint8(
                    v_cfg_5397_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 2) as u32,
                );
                v_suggestions_5404_ = lean_ctor_get_uint8(
                    v_cfg_5397_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 3) as u32,
                );
                v_isSharedCheck_5436_ = (!lean_is_exclusive(v_cfg_5397_)) as u8;
                if v_isSharedCheck_5436_ == 0 {
                    v_unused_5437_ = lean_ctor_get(v_cfg_5397_, 0);
                    lean_dec(v_unused_5437_);
                    v___x_5406_ = v_cfg_5397_;
                    v_isShared_5407_ = v_isSharedCheck_5436_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v_cfg_5397_);
                    v___x_5406_ = lean_box(0);
                    v_isShared_5407_ = v_isSharedCheck_5436_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toApplyConfig_5408_ = lean_ctor_get(v_toApplyRulesConfig_5399_, 1);
                v_transparency_5409_ = lean_ctor_get_uint8(
                    v_toApplyRulesConfig_5399_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                );
                v_symm_5410_ = lean_ctor_get_uint8(
                    v_toApplyRulesConfig_5399_,
                    (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                );
                v_exfalso_5411_ = lean_ctor_get_uint8(
                    v_toApplyRulesConfig_5399_,
                    (core::mem::size_of::<*mut LeanObject>() * 2 + 2) as u32,
                );
                v_isSharedCheck_5434_ = (!lean_is_exclusive(v_toApplyRulesConfig_5399_)) as u8;
                if v_isSharedCheck_5434_ == 0 {
                    v_unused_5435_ = lean_ctor_get(v_toApplyRulesConfig_5399_, 0);
                    lean_dec(v_unused_5435_);
                    v___x_5413_ = v_toApplyRulesConfig_5399_;
                    v_isShared_5414_ = v_isSharedCheck_5434_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_toApplyConfig_5408_);
                    lean_dec(v_toApplyRulesConfig_5399_);
                    v___x_5413_ = lean_box(0);
                    v_isShared_5414_ = v_isSharedCheck_5434_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_maxDepth_5415_ = lean_ctor_get(v_toBacktrackConfig_5400_, 0);
                v_proc_5416_ = lean_ctor_get(v_toBacktrackConfig_5400_, 1);
                v_suspend_5417_ = lean_ctor_get(v_toBacktrackConfig_5400_, 2);
                v_discharge_5418_ = lean_ctor_get(v_toBacktrackConfig_5400_, 3);
                v_commitIndependentGoals_5419_ = lean_ctor_get_uint8(
                    v_toBacktrackConfig_5400_,
                    (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                );
                v_isSharedCheck_5433_ = (!lean_is_exclusive(v_toBacktrackConfig_5400_)) as u8;
                if v_isSharedCheck_5433_ == 0 {
                    v___x_5421_ = v_toBacktrackConfig_5400_;
                    v_isShared_5422_ = v_isSharedCheck_5433_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_discharge_5418_);
                    lean_inc(v_suspend_5417_);
                    lean_inc(v_proc_5416_);
                    lean_inc(v_maxDepth_5415_);
                    lean_dec(v_toBacktrackConfig_5400_);
                    v___x_5421_ = lean_box(0);
                    v_isShared_5422_ = v_isSharedCheck_5433_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___f_5423_ = lean_alloc_closure(
                    l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0___boxed
                        as *mut core::ffi::c_void,
                    9,
                    2,
                );
                lean_closure_set(v___f_5423_, 0, v_proc_5416_);
                lean_closure_set(v___f_5423_, 1, v_proc_5398_);
                if v_isShared_5422_ == 0 {
                    lean_ctor_set(v___x_5421_, 1, v___f_5423_);
                    v___x_5425_ = v___x_5421_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5432_ = lean_alloc_ctor(0, 4, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5432_, 0, v_maxDepth_5415_);
                    lean_ctor_set(v_reuseFailAlloc_5432_, 1, v___f_5423_);
                    lean_ctor_set(v_reuseFailAlloc_5432_, 2, v_suspend_5417_);
                    lean_ctor_set(v_reuseFailAlloc_5432_, 3, v_discharge_5418_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5432_,
                        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                        v_commitIndependentGoals_5419_,
                    );
                    v___x_5425_ = v_reuseFailAlloc_5432_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_5414_ == 0 {
                    lean_ctor_set(v___x_5413_, 0, v___x_5425_);
                    v___x_5427_ = v___x_5413_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5431_ = lean_alloc_ctor(0, 2, (3) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5431_, 0, v___x_5425_);
                    lean_ctor_set(v_reuseFailAlloc_5431_, 1, v_toApplyConfig_5408_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5431_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        v_transparency_5409_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5431_,
                        (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                        v_symm_5410_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5431_,
                        (core::mem::size_of::<*mut LeanObject>() * 2 + 2) as u32,
                        v_exfalso_5411_,
                    );
                    v___x_5427_ = v_reuseFailAlloc_5431_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_5407_ == 0 {
                    lean_ctor_set(v___x_5406_, 0, v___x_5427_);
                    v___x_5429_ = v___x_5406_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5430_ = lean_alloc_ctor(0, 1, (4) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5430_, 0, v___x_5427_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5430_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_backtracking_5401_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5430_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                        v_intro_5402_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5430_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 2) as u32,
                        v_constructor_5403_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5430_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 3) as u32,
                        v_suggestions_5404_,
                    );
                    v___x_5429_ = v_reuseFailAlloc_5430_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5429_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___lam__0(
    mut v_g_5438_: *mut LeanObject,
    mut v___y_5439_: *mut LeanObject,
    mut v___y_5440_: *mut LeanObject,
    mut v___y_5441_: *mut LeanObject,
    mut v___y_5442_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5444_: u8 = 0;
    let mut v___x_5445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5449_: u8 = 0;
    let mut v_snd_5450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5453_: u8 = 0;
    let mut v___x_5454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5461_: u8 = 0;
    let mut v_unused_5462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5463_: u8 = 0;
    let mut v_a_5464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5467_: u8 = 0;
    let mut v___x_5469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5471_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5444_ = 1;
                v___x_5445_ = l_Lean_Meta_intro1Core(
                    v_g_5438_,
                    v___x_5444_,
                    v___y_5439_,
                    v___y_5440_,
                    v___y_5441_,
                    v___y_5442_,
                );
                if lean_obj_tag(v___x_5445_) == 0 {
                    v_a_5446_ = lean_ctor_get(v___x_5445_, 0);
                    v_isSharedCheck_5463_ = (!lean_is_exclusive(v___x_5445_)) as u8;
                    if v_isSharedCheck_5463_ == 0 {
                        v___x_5448_ = v___x_5445_;
                        v_isShared_5449_ = v_isSharedCheck_5463_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5446_);
                        lean_dec(v___x_5445_);
                        v___x_5448_ = lean_box(0);
                        v_isShared_5449_ = v_isSharedCheck_5463_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5464_ = lean_ctor_get(v___x_5445_, 0);
                    v_isSharedCheck_5471_ = (!lean_is_exclusive(v___x_5445_)) as u8;
                    if v_isSharedCheck_5471_ == 0 {
                        v___x_5466_ = v___x_5445_;
                        v_isShared_5467_ = v_isSharedCheck_5471_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_5464_);
                        lean_dec(v___x_5445_);
                        v___x_5466_ = lean_box(0);
                        v_isShared_5467_ = v_isSharedCheck_5471_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_5450_ = lean_ctor_get(v_a_5446_, 1);
                v_isSharedCheck_5461_ = (!lean_is_exclusive(v_a_5446_)) as u8;
                if v_isSharedCheck_5461_ == 0 {
                    v_unused_5462_ = lean_ctor_get(v_a_5446_, 0);
                    lean_dec(v_unused_5462_);
                    v___x_5452_ = v_a_5446_;
                    v_isShared_5453_ = v_isSharedCheck_5461_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_5450_);
                    lean_dec(v_a_5446_);
                    v___x_5452_ = lean_box(0);
                    v_isShared_5453_ = v_isSharedCheck_5461_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5454_ = lean_box(0);
                if v_isShared_5453_ == 0 {
                    lean_ctor_set_tag(v___x_5452_, 1);
                    lean_ctor_set(v___x_5452_, 1, v___x_5454_);
                    lean_ctor_set(v___x_5452_, 0, v_snd_5450_);
                    v___x_5456_ = v___x_5452_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5460_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5460_, 0, v_snd_5450_);
                    lean_ctor_set(v_reuseFailAlloc_5460_, 1, v___x_5454_);
                    v___x_5456_ = v_reuseFailAlloc_5460_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5449_ == 0 {
                    lean_ctor_set(v___x_5448_, 0, v___x_5456_);
                    v___x_5458_ = v___x_5448_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5459_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5459_, 0, v___x_5456_);
                    v___x_5458_ = v_reuseFailAlloc_5459_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5458_;
            }
            5 => {
                if v_isShared_5467_ == 0 {
                    v___x_5469_ = v___x_5466_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5470_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5470_, 0, v_a_5464_);
                    v___x_5469_ = v_reuseFailAlloc_5470_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5469_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___lam__0___boxed(
    mut v_g_5472_: *mut LeanObject,
    mut v___y_5473_: *mut LeanObject,
    mut v___y_5474_: *mut LeanObject,
    mut v___y_5475_: *mut LeanObject,
    mut v___y_5476_: *mut LeanObject,
    mut v___y_5477_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5478_: *mut LeanObject = core::ptr::null_mut();
    v_res_5478_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___lam__0(
        v_g_5472_,
        v___y_5473_,
        v___y_5474_,
        v___y_5475_,
        v___y_5476_,
    );
    lean_dec(v___y_5476_);
    lean_dec_ref(v___y_5475_);
    lean_dec(v___y_5474_);
    lean_dec_ref(v___y_5473_);
    return v_res_5478_;
}
pub unsafe fn l_Lean_Meta_SolveByElim_SolveByElimConfig_intros(
    mut v_cfg_5480_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5482_: *mut LeanObject = core::ptr::null_mut();
    v___f_5481_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___closed__0;
    v___x_5482_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc(v_cfg_5480_, v___f_5481_);
    return v___x_5482_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(
    mut v_x_5483_: *mut LeanObject,
    mut v_x_5484_: *mut LeanObject,
    mut v_x_5485_: *mut LeanObject,
    mut v_x_5486_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_5487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_5488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5491_: u8 = 0;
    let mut v___x_5492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5493_: u8 = 0;
    let mut v___x_5494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_5499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5500_: u8 = 0;
    let mut v___x_5502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5512_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_5487_ = lean_ctor_get(v_x_5483_, 0);
                v_vs_5488_ = lean_ctor_get(v_x_5483_, 1);
                v_isSharedCheck_5512_ = (!lean_is_exclusive(v_x_5483_)) as u8;
                if v_isSharedCheck_5512_ == 0 {
                    v___x_5490_ = v_x_5483_;
                    v_isShared_5491_ = v_isSharedCheck_5512_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_5488_);
                    lean_inc(v_ks_5487_);
                    lean_dec(v_x_5483_);
                    v___x_5490_ = lean_box(0);
                    v_isShared_5491_ = v_isSharedCheck_5512_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5492_ = lean_array_get_size(v_ks_5487_);
                v___x_5493_ = lean_nat_dec_lt(v_x_5484_, v___x_5492_);
                if v___x_5493_ == 0 {
                    lean_dec(v_x_5484_);
                    v___x_5494_ = lean_array_push(v_ks_5487_, v_x_5485_);
                    v___x_5495_ = lean_array_push(v_vs_5488_, v_x_5486_);
                    if v_isShared_5491_ == 0 {
                        lean_ctor_set(v___x_5490_, 1, v___x_5495_);
                        lean_ctor_set(v___x_5490_, 0, v___x_5494_);
                        v___x_5497_ = v___x_5490_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5498_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5498_, 0, v___x_5494_);
                        lean_ctor_set(v_reuseFailAlloc_5498_, 1, v___x_5495_);
                        v___x_5497_ = v_reuseFailAlloc_5498_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_5499_ = lean_array_fget_borrowed(v_ks_5487_, v_x_5484_);
                    v___x_5500_ = l_Lean_instBEqMVarId_beq(v_x_5485_, v_k_x27_5499_);
                    if v___x_5500_ == 0 {
                        if v_isShared_5491_ == 0 {
                            v___x_5502_ = v___x_5490_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_5506_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_5506_, 0, v_ks_5487_);
                            lean_ctor_set(v_reuseFailAlloc_5506_, 1, v_vs_5488_);
                            v___x_5502_ = v_reuseFailAlloc_5506_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_5507_ = lean_array_fset(v_ks_5487_, v_x_5484_, v_x_5485_);
                        v___x_5508_ = lean_array_fset(v_vs_5488_, v_x_5484_, v_x_5486_);
                        lean_dec(v_x_5484_);
                        if v_isShared_5491_ == 0 {
                            lean_ctor_set(v___x_5490_, 1, v___x_5508_);
                            lean_ctor_set(v___x_5490_, 0, v___x_5507_);
                            v___x_5510_ = v___x_5490_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_5511_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_5511_, 0, v___x_5507_);
                            lean_ctor_set(v_reuseFailAlloc_5511_, 1, v___x_5508_);
                            v___x_5510_ = v_reuseFailAlloc_5511_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_5497_;
            }
            3 => {
                v___x_5503_ = lean_unsigned_to_nat(1);
                v___x_5504_ = lean_nat_add(v_x_5484_, v___x_5503_);
                lean_dec(v_x_5484_);
                v_x_5483_ = v___x_5502_;
                v_x_5484_ = v___x_5504_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_5510_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_n_5513_: *mut LeanObject,
    mut v_k_5514_: *mut LeanObject,
    mut v_v_5515_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5517_: *mut LeanObject = core::ptr::null_mut();
    v___x_5516_ = lean_unsigned_to_nat(0);
    v___x_5517_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_n_5513_, v___x_5516_, v_k_5514_, v_v_5515_);
    return v___x_5517_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0()
-> usize {
    let mut v___x_5518_: usize = 0;
    let mut v___x_5519_: usize = 0;
    let mut v___x_5520_: usize = 0;
    v___x_5518_ = 5usize;
    v___x_5519_ = 1usize;
    v___x_5520_ = lean_usize_shift_left(v___x_5519_, v___x_5518_);
    return v___x_5520_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__1()
-> usize {
    let mut v___x_5521_: usize = 0;
    let mut v___x_5522_: usize = 0;
    let mut v___x_5523_: usize = 0;
    v___x_5521_ = 1usize;
    v___x_5522_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0);
    v___x_5523_ = lean_usize_sub(v___x_5522_, v___x_5521_);
    return v___x_5523_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_5524_: *mut LeanObject = core::ptr::null_mut();
    v___x_5524_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_5524_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(
    mut v_x_5525_: *mut LeanObject,
    mut v_x_5526_: usize,
    mut v_x_5527_: usize,
    mut v_x_5528_: *mut LeanObject,
    mut v_x_5529_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_5530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5531_: usize = 0;
    let mut v___x_5532_: usize = 0;
    let mut v___x_5533_: usize = 0;
    let mut v___x_5534_: usize = 0;
    let mut v_j_5535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5537_: u8 = 0;
    let mut v___x_5539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5540_: u8 = 0;
    let mut v_v_5541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_5543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_5550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5554_: u8 = 0;
    let mut v___x_5555_: u8 = 0;
    let mut v___x_5556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5561_: u8 = 0;
    let mut v_node_5562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5565_: u8 = 0;
    let mut v___x_5566_: usize = 0;
    let mut v___x_5567_: usize = 0;
    let mut v___x_5568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5572_: u8 = 0;
    let mut v___x_5573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5574_: u8 = 0;
    let mut v_unused_5575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_5576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_5577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5580_: u8 = 0;
    let mut v___x_5582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_5583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5585_: u8 = 0;
    let mut v_ks_5586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_5587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5591_: usize = 0;
    let mut v___x_5592_: u8 = 0;
    let mut v___x_5593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5595_: u8 = 0;
    let mut v_reuseFailAlloc_5596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5597_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5525_) == 0 {
                    v_es_5530_ = lean_ctor_get(v_x_5525_, 0);
                    v___x_5531_ = 5usize;
                    v___x_5532_ = 1usize;
                    v___x_5533_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__1);
                    v___x_5534_ = lean_usize_land(v_x_5526_, v___x_5533_);
                    v_j_5535_ = lean_usize_to_nat(v___x_5534_);
                    v___x_5536_ = lean_array_get_size(v_es_5530_);
                    v___x_5537_ = lean_nat_dec_lt(v_j_5535_, v___x_5536_);
                    if v___x_5537_ == 0 {
                        lean_dec(v_j_5535_);
                        lean_dec(v_x_5529_);
                        lean_dec(v_x_5528_);
                        return v_x_5525_;
                    } else {
                        lean_inc_ref(v_es_5530_);
                        v_isSharedCheck_5574_ = (!lean_is_exclusive(v_x_5525_)) as u8;
                        if v_isSharedCheck_5574_ == 0 {
                            v_unused_5575_ = lean_ctor_get(v_x_5525_, 0);
                            lean_dec(v_unused_5575_);
                            v___x_5539_ = v_x_5525_;
                            v_isShared_5540_ = v_isSharedCheck_5574_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_5525_);
                            v___x_5539_ = lean_box(0);
                            v_isShared_5540_ = v_isSharedCheck_5574_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_5576_ = lean_ctor_get(v_x_5525_, 0);
                    v_vs_5577_ = lean_ctor_get(v_x_5525_, 1);
                    v_isSharedCheck_5597_ = (!lean_is_exclusive(v_x_5525_)) as u8;
                    if v_isSharedCheck_5597_ == 0 {
                        v___x_5579_ = v_x_5525_;
                        v_isShared_5580_ = v_isSharedCheck_5597_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_5577_);
                        lean_inc(v_ks_5576_);
                        lean_dec(v_x_5525_);
                        v___x_5579_ = lean_box(0);
                        v_isShared_5580_ = v_isSharedCheck_5597_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_5541_ = lean_array_fget(v_es_5530_, v_j_5535_);
                v___x_5542_ = lean_box(0);
                v_xs_x27_5543_ = lean_array_fset(v_es_5530_, v_j_5535_, v___x_5542_);
                match lean_obj_tag(v_v_5541_) {
                    0 => {
                        v_key_5550_ = lean_ctor_get(v_v_5541_, 0);
                        v_val_5551_ = lean_ctor_get(v_v_5541_, 1);
                        v_isSharedCheck_5561_ = (!lean_is_exclusive(v_v_5541_)) as u8;
                        if v_isSharedCheck_5561_ == 0 {
                            v___x_5553_ = v_v_5541_;
                            v_isShared_5554_ = v_isSharedCheck_5561_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_5551_);
                            lean_inc(v_key_5550_);
                            lean_dec(v_v_5541_);
                            v___x_5553_ = lean_box(0);
                            v_isShared_5554_ = v_isSharedCheck_5561_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_5562_ = lean_ctor_get(v_v_5541_, 0);
                        v_isSharedCheck_5572_ = (!lean_is_exclusive(v_v_5541_)) as u8;
                        if v_isSharedCheck_5572_ == 0 {
                            v___x_5564_ = v_v_5541_;
                            v_isShared_5565_ = v_isSharedCheck_5572_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_5562_);
                            lean_dec(v_v_5541_);
                            v___x_5564_ = lean_box(0);
                            v_isShared_5565_ = v_isSharedCheck_5572_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_5573_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_5573_, 0, v_x_5528_);
                        lean_ctor_set(v___x_5573_, 1, v_x_5529_);
                        v___y_5545_ = v___x_5573_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5546_ = lean_array_fset(v_xs_x27_5543_, v_j_5535_, v___y_5545_);
                lean_dec(v_j_5535_);
                if v_isShared_5540_ == 0 {
                    lean_ctor_set(v___x_5539_, 0, v___x_5546_);
                    v___x_5548_ = v___x_5539_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5549_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5549_, 0, v___x_5546_);
                    v___x_5548_ = v_reuseFailAlloc_5549_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5548_;
            }
            4 => {
                v___x_5555_ = l_Lean_instBEqMVarId_beq(v_x_5528_, v_key_5550_);
                if v___x_5555_ == 0 {
                    lean_del_object(v___x_5553_);
                    v___x_5556_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_5550_,
                        v_val_5551_,
                        v_x_5528_,
                        v_x_5529_,
                    );
                    v___x_5557_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_5557_, 0, v___x_5556_);
                    v___y_5545_ = v___x_5557_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_5551_);
                    lean_dec(v_key_5550_);
                    if v_isShared_5554_ == 0 {
                        lean_ctor_set(v___x_5553_, 1, v_x_5529_);
                        lean_ctor_set(v___x_5553_, 0, v_x_5528_);
                        v___x_5559_ = v___x_5553_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5560_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5560_, 0, v_x_5528_);
                        lean_ctor_set(v_reuseFailAlloc_5560_, 1, v_x_5529_);
                        v___x_5559_ = v_reuseFailAlloc_5560_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_5545_ = v___x_5559_;
                state = 2;
                continue;
            }
            6 => {
                v___x_5566_ = lean_usize_shift_right(v_x_5526_, v___x_5531_);
                v___x_5567_ = lean_usize_add(v_x_5527_, v___x_5532_);
                v___x_5568_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_node_5562_, v___x_5566_, v___x_5567_, v_x_5528_, v_x_5529_);
                if v_isShared_5565_ == 0 {
                    lean_ctor_set(v___x_5564_, 0, v___x_5568_);
                    v___x_5570_ = v___x_5564_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5571_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5571_, 0, v___x_5568_);
                    v___x_5570_ = v_reuseFailAlloc_5571_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_5545_ = v___x_5570_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_5580_ == 0 {
                    v___x_5582_ = v___x_5579_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5596_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5596_, 0, v_ks_5576_);
                    lean_ctor_set(v_reuseFailAlloc_5596_, 1, v_vs_5577_);
                    v___x_5582_ = v_reuseFailAlloc_5596_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_5583_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2___redArg(v___x_5582_, v_x_5528_, v_x_5529_);
                v___x_5591_ = 7usize;
                v___x_5592_ = lean_usize_dec_le(v___x_5591_, v_x_5527_);
                if v___x_5592_ == 0 {
                    v___x_5593_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_5583_);
                    v___x_5594_ = lean_unsigned_to_nat(4);
                    v___x_5595_ = lean_nat_dec_lt(v___x_5593_, v___x_5594_);
                    lean_dec(v___x_5593_);
                    v___y_5585_ = v___x_5595_;
                    state = 10;
                    continue;
                } else {
                    v___y_5585_ = v___x_5592_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_5585_ == 0 {
                    v_ks_5586_ = lean_ctor_get(v_newNode_5583_, 0);
                    lean_inc_ref(v_ks_5586_);
                    v_vs_5587_ = lean_ctor_get(v_newNode_5583_, 1);
                    lean_inc_ref(v_vs_5587_);
                    lean_dec_ref(v_newNode_5583_);
                    v___x_5588_ = lean_unsigned_to_nat(0);
                    v___x_5589_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__2);
                    v___x_5590_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(v_x_5527_, v_ks_5586_, v_vs_5587_, v___x_5588_, v___x_5589_);
                    lean_dec_ref(v_vs_5587_);
                    lean_dec_ref(v_ks_5586_);
                    return v___x_5590_;
                } else {
                    return v_newNode_5583_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(
    mut v_depth_5598_: usize,
    mut v_keys_5599_: *mut LeanObject,
    mut v_vals_5600_: *mut LeanObject,
    mut v_i_5601_: *mut LeanObject,
    mut v_entries_5602_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5604_: u8 = 0;
    let mut v_k_5605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_5606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5607_: u64 = 0;
    let mut v_h_5608_: usize = 0;
    let mut v___x_5609_: usize = 0;
    let mut v___x_5610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5611_: usize = 0;
    let mut v___x_5612_: usize = 0;
    let mut v___x_5613_: usize = 0;
    let mut v_h_5614_: usize = 0;
    let mut v___x_5615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5616_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5603_ = lean_array_get_size(v_keys_5599_);
                v___x_5604_ = lean_nat_dec_lt(v_i_5601_, v___x_5603_);
                if v___x_5604_ == 0 {
                    lean_dec(v_i_5601_);
                    return v_entries_5602_;
                } else {
                    v_k_5605_ = lean_array_fget_borrowed(v_keys_5599_, v_i_5601_);
                    v_v_5606_ = lean_array_fget_borrowed(v_vals_5600_, v_i_5601_);
                    v___x_5607_ = l_Lean_instHashableMVarId_hash(v_k_5605_);
                    v_h_5608_ = lean_uint64_to_usize(v___x_5607_);
                    v___x_5609_ = 5usize;
                    v___x_5610_ = lean_unsigned_to_nat(1);
                    v___x_5611_ = 1usize;
                    v___x_5612_ = lean_usize_sub(v_depth_5598_, v___x_5611_);
                    v___x_5613_ = lean_usize_mul(v___x_5609_, v___x_5612_);
                    v_h_5614_ = lean_usize_shift_right(v_h_5608_, v___x_5613_);
                    v___x_5615_ = lean_nat_add(v_i_5601_, v___x_5610_);
                    lean_dec(v_i_5601_);
                    lean_inc(v_v_5606_);
                    lean_inc(v_k_5605_);
                    v___x_5616_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_entries_5602_, v_h_5614_, v_depth_5598_, v_k_5605_, v_v_5606_);
                    v_i_5601_ = v___x_5615_;
                    v_entries_5602_ = v___x_5616_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg___boxed(
    mut v_depth_5618_: *mut LeanObject,
    mut v_keys_5619_: *mut LeanObject,
    mut v_vals_5620_: *mut LeanObject,
    mut v_i_5621_: *mut LeanObject,
    mut v_entries_5622_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_5623_: usize = 0;
    let mut v_res_5624_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_5623_ = lean_unbox_usize(v_depth_5618_);
    lean_dec(v_depth_5618_);
    v_res_5624_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_5623_, v_keys_5619_, v_vals_5620_, v_i_5621_, v_entries_5622_);
    lean_dec_ref(v_vals_5620_);
    lean_dec_ref(v_keys_5619_);
    return v_res_5624_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_x_5625_: *mut LeanObject,
    mut v_x_5626_: *mut LeanObject,
    mut v_x_5627_: *mut LeanObject,
    mut v_x_5628_: *mut LeanObject,
    mut v_x_5629_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_838__boxed_5630_: usize = 0;
    let mut v_x_839__boxed_5631_: usize = 0;
    let mut v_res_5632_: *mut LeanObject = core::ptr::null_mut();
    v_x_838__boxed_5630_ = lean_unbox_usize(v_x_5626_);
    lean_dec(v_x_5626_);
    v_x_839__boxed_5631_ = lean_unbox_usize(v_x_5627_);
    lean_dec(v_x_5627_);
    v_res_5632_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_x_5625_, v_x_838__boxed_5630_, v_x_839__boxed_5631_, v_x_5628_, v_x_5629_);
    return v_res_5632_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0___redArg(
    mut v_x_5633_: *mut LeanObject,
    mut v_x_5634_: *mut LeanObject,
    mut v_x_5635_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5636_: u64 = 0;
    let mut v___x_5637_: usize = 0;
    let mut v___x_5638_: usize = 0;
    let mut v___x_5639_: *mut LeanObject = core::ptr::null_mut();
    v___x_5636_ = l_Lean_instHashableMVarId_hash(v_x_5634_);
    v___x_5637_ = lean_uint64_to_usize(v___x_5636_);
    v___x_5638_ = 1usize;
    v___x_5639_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_x_5633_, v___x_5637_, v___x_5638_, v_x_5634_, v_x_5635_);
    return v___x_5639_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(
    mut v_mvarId_5640_: *mut LeanObject,
    mut v_val_5641_: *mut LeanObject,
    mut v___y_5642_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_5645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_5646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_5648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_5649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5652_: u8 = 0;
    let mut v_depth_5653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_5654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_5655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_5656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lDecls_5657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_5658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_userNames_5659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_5660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_5661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_5662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5665_: u8 = 0;
    let mut v___x_5666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5676_: u8 = 0;
    let mut v_isSharedCheck_5677_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5644_ = lean_st_ref_take(v___y_5642_);
                v_mctx_5645_ = lean_ctor_get(v___x_5644_, 0);
                v_cache_5646_ = lean_ctor_get(v___x_5644_, 1);
                v_zetaDeltaFVarIds_5647_ = lean_ctor_get(v___x_5644_, 2);
                v_postponed_5648_ = lean_ctor_get(v___x_5644_, 3);
                v_diag_5649_ = lean_ctor_get(v___x_5644_, 4);
                v_isSharedCheck_5677_ = (!lean_is_exclusive(v___x_5644_)) as u8;
                if v_isSharedCheck_5677_ == 0 {
                    v___x_5651_ = v___x_5644_;
                    v_isShared_5652_ = v_isSharedCheck_5677_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_diag_5649_);
                    lean_inc(v_postponed_5648_);
                    lean_inc(v_zetaDeltaFVarIds_5647_);
                    lean_inc(v_cache_5646_);
                    lean_inc(v_mctx_5645_);
                    lean_dec(v___x_5644_);
                    v___x_5651_ = lean_box(0);
                    v_isShared_5652_ = v_isSharedCheck_5677_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_5653_ = lean_ctor_get(v_mctx_5645_, 0);
                v_levelAssignDepth_5654_ = lean_ctor_get(v_mctx_5645_, 1);
                v_lmvarCounter_5655_ = lean_ctor_get(v_mctx_5645_, 2);
                v_mvarCounter_5656_ = lean_ctor_get(v_mctx_5645_, 3);
                v_lDecls_5657_ = lean_ctor_get(v_mctx_5645_, 4);
                v_decls_5658_ = lean_ctor_get(v_mctx_5645_, 5);
                v_userNames_5659_ = lean_ctor_get(v_mctx_5645_, 6);
                v_lAssignment_5660_ = lean_ctor_get(v_mctx_5645_, 7);
                v_eAssignment_5661_ = lean_ctor_get(v_mctx_5645_, 8);
                v_dAssignment_5662_ = lean_ctor_get(v_mctx_5645_, 9);
                v_isSharedCheck_5676_ = (!lean_is_exclusive(v_mctx_5645_)) as u8;
                if v_isSharedCheck_5676_ == 0 {
                    v___x_5664_ = v_mctx_5645_;
                    v_isShared_5665_ = v_isSharedCheck_5676_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_dAssignment_5662_);
                    lean_inc(v_eAssignment_5661_);
                    lean_inc(v_lAssignment_5660_);
                    lean_inc(v_userNames_5659_);
                    lean_inc(v_decls_5658_);
                    lean_inc(v_lDecls_5657_);
                    lean_inc(v_mvarCounter_5656_);
                    lean_inc(v_lmvarCounter_5655_);
                    lean_inc(v_levelAssignDepth_5654_);
                    lean_inc(v_depth_5653_);
                    lean_dec(v_mctx_5645_);
                    v___x_5664_ = lean_box(0);
                    v_isShared_5665_ = v_isSharedCheck_5676_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5666_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0___redArg(v_eAssignment_5661_, v_mvarId_5640_, v_val_5641_);
                if v_isShared_5665_ == 0 {
                    lean_ctor_set(v___x_5664_, 8, v___x_5666_);
                    v___x_5668_ = v___x_5664_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5675_ = lean_alloc_ctor(0, 10, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5675_, 0, v_depth_5653_);
                    lean_ctor_set(v_reuseFailAlloc_5675_, 1, v_levelAssignDepth_5654_);
                    lean_ctor_set(v_reuseFailAlloc_5675_, 2, v_lmvarCounter_5655_);
                    lean_ctor_set(v_reuseFailAlloc_5675_, 3, v_mvarCounter_5656_);
                    lean_ctor_set(v_reuseFailAlloc_5675_, 4, v_lDecls_5657_);
                    lean_ctor_set(v_reuseFailAlloc_5675_, 5, v_decls_5658_);
                    lean_ctor_set(v_reuseFailAlloc_5675_, 6, v_userNames_5659_);
                    lean_ctor_set(v_reuseFailAlloc_5675_, 7, v_lAssignment_5660_);
                    lean_ctor_set(v_reuseFailAlloc_5675_, 8, v___x_5666_);
                    lean_ctor_set(v_reuseFailAlloc_5675_, 9, v_dAssignment_5662_);
                    v___x_5668_ = v_reuseFailAlloc_5675_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5652_ == 0 {
                    lean_ctor_set(v___x_5651_, 0, v___x_5668_);
                    v___x_5670_ = v___x_5651_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5674_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5674_, 0, v___x_5668_);
                    lean_ctor_set(v_reuseFailAlloc_5674_, 1, v_cache_5646_);
                    lean_ctor_set(v_reuseFailAlloc_5674_, 2, v_zetaDeltaFVarIds_5647_);
                    lean_ctor_set(v_reuseFailAlloc_5674_, 3, v_postponed_5648_);
                    lean_ctor_set(v_reuseFailAlloc_5674_, 4, v_diag_5649_);
                    v___x_5670_ = v_reuseFailAlloc_5674_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5671_ = lean_st_ref_set(v___y_5642_, v___x_5670_);
                v___x_5672_ = lean_box(0);
                v___x_5673_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5673_, 0, v___x_5672_);
                return v___x_5673_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg___boxed(
    mut v_mvarId_5678_: *mut LeanObject,
    mut v_val_5679_: *mut LeanObject,
    mut v___y_5680_: *mut LeanObject,
    mut v___y_5681_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5682_: *mut LeanObject = core::ptr::null_mut();
    v_res_5682_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_mvarId_5678_, v_val_5679_, v___y_5680_);
    lean_dec(v___y_5680_);
    return v_res_5682_;
}
pub unsafe fn l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lam__0(
    mut v_g_5683_: *mut LeanObject,
    mut v___y_5684_: *mut LeanObject,
    mut v___y_5685_: *mut LeanObject,
    mut v___y_5686_: *mut LeanObject,
    mut v___y_5687_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5697_: u8 = 0;
    let mut v___x_5698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5702_: u8 = 0;
    let mut v_unused_5703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5707_: u8 = 0;
    let mut v___x_5709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5711_: u8 = 0;
    let mut v_a_5712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5715_: u8 = 0;
    let mut v___x_5717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5719_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_g_5683_);
                v___x_5689_ = l_Lean_MVarId_getType(
                    v_g_5683_,
                    v___y_5684_,
                    v___y_5685_,
                    v___y_5686_,
                    v___y_5687_,
                );
                if lean_obj_tag(v___x_5689_) == 0 {
                    v_a_5690_ = lean_ctor_get(v___x_5689_, 0);
                    lean_inc(v_a_5690_);
                    lean_dec_ref_known(v___x_5689_, 1);
                    v___x_5691_ = lean_box(0);
                    v___x_5692_ = l_Lean_Meta_synthInstance(
                        v_a_5690_,
                        v___x_5691_,
                        v___y_5684_,
                        v___y_5685_,
                        v___y_5686_,
                        v___y_5687_,
                    );
                    if lean_obj_tag(v___x_5692_) == 0 {
                        v_a_5693_ = lean_ctor_get(v___x_5692_, 0);
                        lean_inc(v_a_5693_);
                        lean_dec_ref_known(v___x_5692_, 1);
                        v___x_5694_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_g_5683_, v_a_5693_, v___y_5685_);
                        v_isSharedCheck_5702_ = (!lean_is_exclusive(v___x_5694_)) as u8;
                        if v_isSharedCheck_5702_ == 0 {
                            v_unused_5703_ = lean_ctor_get(v___x_5694_, 0);
                            lean_dec(v_unused_5703_);
                            v___x_5696_ = v___x_5694_;
                            v_isShared_5697_ = v_isSharedCheck_5702_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v___x_5694_);
                            v___x_5696_ = lean_box(0);
                            v_isShared_5697_ = v_isSharedCheck_5702_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_g_5683_);
                        v_a_5704_ = lean_ctor_get(v___x_5692_, 0);
                        v_isSharedCheck_5711_ = (!lean_is_exclusive(v___x_5692_)) as u8;
                        if v_isSharedCheck_5711_ == 0 {
                            v___x_5706_ = v___x_5692_;
                            v_isShared_5707_ = v_isSharedCheck_5711_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_5704_);
                            lean_dec(v___x_5692_);
                            v___x_5706_ = lean_box(0);
                            v_isShared_5707_ = v_isSharedCheck_5711_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_g_5683_);
                    v_a_5712_ = lean_ctor_get(v___x_5689_, 0);
                    v_isSharedCheck_5719_ = (!lean_is_exclusive(v___x_5689_)) as u8;
                    if v_isSharedCheck_5719_ == 0 {
                        v___x_5714_ = v___x_5689_;
                        v_isShared_5715_ = v_isSharedCheck_5719_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_5712_);
                        lean_dec(v___x_5689_);
                        v___x_5714_ = lean_box(0);
                        v_isShared_5715_ = v_isSharedCheck_5719_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5698_ = lean_box(0);
                if v_isShared_5697_ == 0 {
                    lean_ctor_set(v___x_5696_, 0, v___x_5698_);
                    v___x_5700_ = v___x_5696_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5701_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5701_, 0, v___x_5698_);
                    v___x_5700_ = v_reuseFailAlloc_5701_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5700_;
            }
            3 => {
                if v_isShared_5707_ == 0 {
                    v___x_5709_ = v___x_5706_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5710_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5710_, 0, v_a_5704_);
                    v___x_5709_ = v_reuseFailAlloc_5710_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5709_;
            }
            5 => {
                if v_isShared_5715_ == 0 {
                    v___x_5717_ = v___x_5714_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5718_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5718_, 0, v_a_5712_);
                    v___x_5717_ = v_reuseFailAlloc_5718_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5717_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lam__0___boxed(
    mut v_g_5720_: *mut LeanObject,
    mut v___y_5721_: *mut LeanObject,
    mut v___y_5722_: *mut LeanObject,
    mut v___y_5723_: *mut LeanObject,
    mut v___y_5724_: *mut LeanObject,
    mut v___y_5725_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5726_: *mut LeanObject = core::ptr::null_mut();
    v_res_5726_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lam__0(
        v_g_5720_,
        v___y_5721_,
        v___y_5722_,
        v___y_5723_,
        v___y_5724_,
    );
    lean_dec(v___y_5724_);
    lean_dec_ref(v___y_5723_);
    lean_dec(v___y_5722_);
    lean_dec_ref(v___y_5721_);
    return v_res_5726_;
}
pub unsafe fn l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance(
    mut v_cfg_5728_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5730_: *mut LeanObject = core::ptr::null_mut();
    v___f_5729_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___closed__0;
    v___x_5730_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc(v_cfg_5728_, v___f_5729_);
    return v___x_5730_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0(
    mut v_mvarId_5731_: *mut LeanObject,
    mut v_val_5732_: *mut LeanObject,
    mut v___y_5733_: *mut LeanObject,
    mut v___y_5734_: *mut LeanObject,
    mut v___y_5735_: *mut LeanObject,
    mut v___y_5736_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5738_: *mut LeanObject = core::ptr::null_mut();
    v___x_5738_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_mvarId_5731_, v_val_5732_, v___y_5734_);
    return v___x_5738_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___boxed(
    mut v_mvarId_5739_: *mut LeanObject,
    mut v_val_5740_: *mut LeanObject,
    mut v___y_5741_: *mut LeanObject,
    mut v___y_5742_: *mut LeanObject,
    mut v___y_5743_: *mut LeanObject,
    mut v___y_5744_: *mut LeanObject,
    mut v___y_5745_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5746_: *mut LeanObject = core::ptr::null_mut();
    v_res_5746_ =
        l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0(
            v_mvarId_5739_,
            v_val_5740_,
            v___y_5741_,
            v___y_5742_,
            v___y_5743_,
            v___y_5744_,
        );
    lean_dec(v___y_5744_);
    lean_dec_ref(v___y_5743_);
    lean_dec(v___y_5742_);
    lean_dec_ref(v___y_5741_);
    return v_res_5746_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0(
    mut v_00_u03b2_5747_: *mut LeanObject,
    mut v_x_5748_: *mut LeanObject,
    mut v_x_5749_: *mut LeanObject,
    mut v_x_5750_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5751_: *mut LeanObject = core::ptr::null_mut();
    v___x_5751_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0___redArg(v_x_5748_, v_x_5749_, v_x_5750_);
    return v___x_5751_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1(
    mut v_00_u03b2_5752_: *mut LeanObject,
    mut v_x_5753_: *mut LeanObject,
    mut v_x_5754_: usize,
    mut v_x_5755_: usize,
    mut v_x_5756_: *mut LeanObject,
    mut v_x_5757_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5758_: *mut LeanObject = core::ptr::null_mut();
    v___x_5758_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_x_5753_, v_x_5754_, v_x_5755_, v_x_5756_, v_x_5757_);
    return v___x_5758_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_5759_: *mut LeanObject,
    mut v_x_5760_: *mut LeanObject,
    mut v_x_5761_: *mut LeanObject,
    mut v_x_5762_: *mut LeanObject,
    mut v_x_5763_: *mut LeanObject,
    mut v_x_5764_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_1169__boxed_5765_: usize = 0;
    let mut v_x_1170__boxed_5766_: usize = 0;
    let mut v_res_5767_: *mut LeanObject = core::ptr::null_mut();
    v_x_1169__boxed_5765_ = lean_unbox_usize(v_x_5761_);
    lean_dec(v_x_5761_);
    v_x_1170__boxed_5766_ = lean_unbox_usize(v_x_5762_);
    lean_dec(v_x_5762_);
    v_res_5767_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1(v_00_u03b2_5759_, v_x_5760_, v_x_1169__boxed_5765_, v_x_1170__boxed_5766_, v_x_5763_, v_x_5764_);
    return v_res_5767_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b2_5768_: *mut LeanObject,
    mut v_n_5769_: *mut LeanObject,
    mut v_k_5770_: *mut LeanObject,
    mut v_v_5771_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5772_: *mut LeanObject = core::ptr::null_mut();
    v___x_5772_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2___redArg(v_n_5769_, v_k_5770_, v_v_5771_);
    return v___x_5772_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3(
    mut v_00_u03b2_5773_: *mut LeanObject,
    mut v_depth_5774_: usize,
    mut v_keys_5775_: *mut LeanObject,
    mut v_vals_5776_: *mut LeanObject,
    mut v_heq_5777_: *mut LeanObject,
    mut v_i_5778_: *mut LeanObject,
    mut v_entries_5779_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5780_: *mut LeanObject = core::ptr::null_mut();
    v___x_5780_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_5774_, v_keys_5775_, v_vals_5776_, v_i_5778_, v_entries_5779_);
    return v___x_5780_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___boxed(
    mut v_00_u03b2_5781_: *mut LeanObject,
    mut v_depth_5782_: *mut LeanObject,
    mut v_keys_5783_: *mut LeanObject,
    mut v_vals_5784_: *mut LeanObject,
    mut v_heq_5785_: *mut LeanObject,
    mut v_i_5786_: *mut LeanObject,
    mut v_entries_5787_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_5788_: usize = 0;
    let mut v_res_5789_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_5788_ = lean_unbox_usize(v_depth_5782_);
    lean_dec(v_depth_5782_);
    v_res_5789_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_5781_, v_depth_boxed_5788_, v_keys_5783_, v_vals_5784_, v_heq_5785_, v_i_5786_, v_entries_5787_);
    lean_dec_ref(v_vals_5784_);
    lean_dec_ref(v_keys_5783_);
    return v_res_5789_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3(
    mut v_00_u03b2_5790_: *mut LeanObject,
    mut v_x_5791_: *mut LeanObject,
    mut v_x_5792_: *mut LeanObject,
    mut v_x_5793_: *mut LeanObject,
    mut v_x_5794_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5795_: *mut LeanObject = core::ptr::null_mut();
    v___x_5795_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_5791_, v_x_5792_, v_x_5793_, v_x_5794_);
    return v___x_5795_;
}
pub unsafe fn l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0(
    mut v_discharge_5796_: *mut LeanObject,
    mut v_discharge_5797_: *mut LeanObject,
    mut v_g_5798_: *mut LeanObject,
    mut v___y_5799_: *mut LeanObject,
    mut v___y_5800_: *mut LeanObject,
    mut v___y_5801_: *mut LeanObject,
    mut v___y_5802_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5807_: u8 = 0;
    let mut v___x_5808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5809_: u8 = 0;
    let mut v___x_5810_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_5802_);
                lean_inc_ref(v___y_5801_);
                lean_inc(v___y_5800_);
                lean_inc_ref(v___y_5799_);
                lean_inc(v_g_5798_);
                v___x_5804_ = lean_apply_6(
                    v_discharge_5796_,
                    v_g_5798_,
                    v___y_5799_,
                    v___y_5800_,
                    v___y_5801_,
                    v___y_5802_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_5804_) == 0 {
                    lean_dec(v_g_5798_);
                    lean_dec_ref(v_discharge_5797_);
                    return v___x_5804_;
                } else {
                    v_a_5805_ = lean_ctor_get(v___x_5804_, 0);
                    lean_inc(v_a_5805_);
                    v___x_5809_ = l_Lean_Exception_isInterrupt(v_a_5805_);
                    if v___x_5809_ == 0 {
                        v___x_5810_ = l_Lean_Exception_isRuntime(v_a_5805_);
                        v___y_5807_ = v___x_5810_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_a_5805_);
                        v___y_5807_ = v___x_5809_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_5807_ == 0 {
                    lean_dec_ref_known(v___x_5804_, 1);
                    lean_inc(v___y_5802_);
                    lean_inc_ref(v___y_5801_);
                    lean_inc(v___y_5800_);
                    lean_inc_ref(v___y_5799_);
                    v___x_5808_ = lean_apply_6(
                        v_discharge_5797_,
                        v_g_5798_,
                        v___y_5799_,
                        v___y_5800_,
                        v___y_5801_,
                        v___y_5802_,
                        lean_box(0),
                    );
                    return v___x_5808_;
                } else {
                    lean_dec(v_g_5798_);
                    lean_dec_ref(v_discharge_5797_);
                    return v___x_5804_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0___boxed(
    mut v_discharge_5811_: *mut LeanObject,
    mut v_discharge_5812_: *mut LeanObject,
    mut v_g_5813_: *mut LeanObject,
    mut v___y_5814_: *mut LeanObject,
    mut v___y_5815_: *mut LeanObject,
    mut v___y_5816_: *mut LeanObject,
    mut v___y_5817_: *mut LeanObject,
    mut v___y_5818_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5819_: *mut LeanObject = core::ptr::null_mut();
    v_res_5819_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0(
        v_discharge_5811_,
        v_discharge_5812_,
        v_g_5813_,
        v___y_5814_,
        v___y_5815_,
        v___y_5816_,
        v___y_5817_,
    );
    lean_dec(v___y_5817_);
    lean_dec_ref(v___y_5816_);
    lean_dec(v___y_5815_);
    lean_dec_ref(v___y_5814_);
    return v_res_5819_;
}
pub unsafe fn l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(
    mut v_cfg_5820_: *mut LeanObject,
    mut v_discharge_5821_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplyRulesConfig_5822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBacktrackConfig_5823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_backtracking_5824_: u8 = 0;
    let mut v_intro_5825_: u8 = 0;
    let mut v_constructor_5826_: u8 = 0;
    let mut v_suggestions_5827_: u8 = 0;
    let mut v___x_5829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5830_: u8 = 0;
    let mut v_toApplyConfig_5831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_transparency_5832_: u8 = 0;
    let mut v_symm_5833_: u8 = 0;
    let mut v_exfalso_5834_: u8 = 0;
    let mut v___x_5836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5837_: u8 = 0;
    let mut v_maxDepth_5838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proc_5839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suspend_5840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_discharge_5841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_commitIndependentGoals_5842_: u8 = 0;
    let mut v___x_5844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5845_: u8 = 0;
    let mut v___f_5846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5856_: u8 = 0;
    let mut v_isSharedCheck_5857_: u8 = 0;
    let mut v_unused_5858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5859_: u8 = 0;
    let mut v_unused_5860_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplyRulesConfig_5822_ = lean_ctor_get(v_cfg_5820_, 0);
                lean_inc_ref(v_toApplyRulesConfig_5822_);
                v_toBacktrackConfig_5823_ = lean_ctor_get(v_toApplyRulesConfig_5822_, 0);
                lean_inc_ref(v_toBacktrackConfig_5823_);
                v_backtracking_5824_ = lean_ctor_get_uint8(
                    v_cfg_5820_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_intro_5825_ = lean_ctor_get_uint8(
                    v_cfg_5820_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                );
                v_constructor_5826_ = lean_ctor_get_uint8(
                    v_cfg_5820_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 2) as u32,
                );
                v_suggestions_5827_ = lean_ctor_get_uint8(
                    v_cfg_5820_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 3) as u32,
                );
                v_isSharedCheck_5859_ = (!lean_is_exclusive(v_cfg_5820_)) as u8;
                if v_isSharedCheck_5859_ == 0 {
                    v_unused_5860_ = lean_ctor_get(v_cfg_5820_, 0);
                    lean_dec(v_unused_5860_);
                    v___x_5829_ = v_cfg_5820_;
                    v_isShared_5830_ = v_isSharedCheck_5859_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v_cfg_5820_);
                    v___x_5829_ = lean_box(0);
                    v_isShared_5830_ = v_isSharedCheck_5859_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toApplyConfig_5831_ = lean_ctor_get(v_toApplyRulesConfig_5822_, 1);
                v_transparency_5832_ = lean_ctor_get_uint8(
                    v_toApplyRulesConfig_5822_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                );
                v_symm_5833_ = lean_ctor_get_uint8(
                    v_toApplyRulesConfig_5822_,
                    (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                );
                v_exfalso_5834_ = lean_ctor_get_uint8(
                    v_toApplyRulesConfig_5822_,
                    (core::mem::size_of::<*mut LeanObject>() * 2 + 2) as u32,
                );
                v_isSharedCheck_5857_ = (!lean_is_exclusive(v_toApplyRulesConfig_5822_)) as u8;
                if v_isSharedCheck_5857_ == 0 {
                    v_unused_5858_ = lean_ctor_get(v_toApplyRulesConfig_5822_, 0);
                    lean_dec(v_unused_5858_);
                    v___x_5836_ = v_toApplyRulesConfig_5822_;
                    v_isShared_5837_ = v_isSharedCheck_5857_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_toApplyConfig_5831_);
                    lean_dec(v_toApplyRulesConfig_5822_);
                    v___x_5836_ = lean_box(0);
                    v_isShared_5837_ = v_isSharedCheck_5857_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_maxDepth_5838_ = lean_ctor_get(v_toBacktrackConfig_5823_, 0);
                v_proc_5839_ = lean_ctor_get(v_toBacktrackConfig_5823_, 1);
                v_suspend_5840_ = lean_ctor_get(v_toBacktrackConfig_5823_, 2);
                v_discharge_5841_ = lean_ctor_get(v_toBacktrackConfig_5823_, 3);
                v_commitIndependentGoals_5842_ = lean_ctor_get_uint8(
                    v_toBacktrackConfig_5823_,
                    (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                );
                v_isSharedCheck_5856_ = (!lean_is_exclusive(v_toBacktrackConfig_5823_)) as u8;
                if v_isSharedCheck_5856_ == 0 {
                    v___x_5844_ = v_toBacktrackConfig_5823_;
                    v_isShared_5845_ = v_isSharedCheck_5856_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_discharge_5841_);
                    lean_inc(v_suspend_5840_);
                    lean_inc(v_proc_5839_);
                    lean_inc(v_maxDepth_5838_);
                    lean_dec(v_toBacktrackConfig_5823_);
                    v___x_5844_ = lean_box(0);
                    v_isShared_5845_ = v_isSharedCheck_5856_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___f_5846_ = lean_alloc_closure(
                    l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0___boxed
                        as *mut core::ffi::c_void,
                    8,
                    2,
                );
                lean_closure_set(v___f_5846_, 0, v_discharge_5821_);
                lean_closure_set(v___f_5846_, 1, v_discharge_5841_);
                if v_isShared_5845_ == 0 {
                    lean_ctor_set(v___x_5844_, 3, v___f_5846_);
                    v___x_5848_ = v___x_5844_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5855_ = lean_alloc_ctor(0, 4, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5855_, 0, v_maxDepth_5838_);
                    lean_ctor_set(v_reuseFailAlloc_5855_, 1, v_proc_5839_);
                    lean_ctor_set(v_reuseFailAlloc_5855_, 2, v_suspend_5840_);
                    lean_ctor_set(v_reuseFailAlloc_5855_, 3, v___f_5846_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5855_,
                        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                        v_commitIndependentGoals_5842_,
                    );
                    v___x_5848_ = v_reuseFailAlloc_5855_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_5837_ == 0 {
                    lean_ctor_set(v___x_5836_, 0, v___x_5848_);
                    v___x_5850_ = v___x_5836_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5854_ = lean_alloc_ctor(0, 2, (3) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5854_, 0, v___x_5848_);
                    lean_ctor_set(v_reuseFailAlloc_5854_, 1, v_toApplyConfig_5831_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5854_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        v_transparency_5832_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5854_,
                        (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                        v_symm_5833_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5854_,
                        (core::mem::size_of::<*mut LeanObject>() * 2 + 2) as u32,
                        v_exfalso_5834_,
                    );
                    v___x_5850_ = v_reuseFailAlloc_5854_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_5830_ == 0 {
                    lean_ctor_set(v___x_5829_, 0, v___x_5850_);
                    v___x_5852_ = v___x_5829_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5853_ = lean_alloc_ctor(0, 1, (4) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5853_, 0, v___x_5850_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5853_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_backtracking_5824_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5853_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                        v_intro_5825_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5853_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 2) as u32,
                        v_constructor_5826_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5853_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 3) as u32,
                        v_suggestions_5827_,
                    );
                    v___x_5852_ = v_reuseFailAlloc_5853_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5852_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0(
    mut v_g_5861_: *mut LeanObject,
    mut v___y_5862_: *mut LeanObject,
    mut v___y_5863_: *mut LeanObject,
    mut v___y_5864_: *mut LeanObject,
    mut v___y_5865_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5867_: u8 = 0;
    let mut v___x_5868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5872_: u8 = 0;
    let mut v_snd_5873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5876_: u8 = 0;
    let mut v___x_5877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5885_: u8 = 0;
    let mut v_unused_5886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5887_: u8 = 0;
    let mut v_a_5888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5891_: u8 = 0;
    let mut v___x_5893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5895_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5867_ = 1;
                v___x_5868_ = l_Lean_Meta_intro1Core(
                    v_g_5861_,
                    v___x_5867_,
                    v___y_5862_,
                    v___y_5863_,
                    v___y_5864_,
                    v___y_5865_,
                );
                if lean_obj_tag(v___x_5868_) == 0 {
                    v_a_5869_ = lean_ctor_get(v___x_5868_, 0);
                    v_isSharedCheck_5887_ = (!lean_is_exclusive(v___x_5868_)) as u8;
                    if v_isSharedCheck_5887_ == 0 {
                        v___x_5871_ = v___x_5868_;
                        v_isShared_5872_ = v_isSharedCheck_5887_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5869_);
                        lean_dec(v___x_5868_);
                        v___x_5871_ = lean_box(0);
                        v_isShared_5872_ = v_isSharedCheck_5887_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5888_ = lean_ctor_get(v___x_5868_, 0);
                    v_isSharedCheck_5895_ = (!lean_is_exclusive(v___x_5868_)) as u8;
                    if v_isSharedCheck_5895_ == 0 {
                        v___x_5890_ = v___x_5868_;
                        v_isShared_5891_ = v_isSharedCheck_5895_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_5888_);
                        lean_dec(v___x_5868_);
                        v___x_5890_ = lean_box(0);
                        v_isShared_5891_ = v_isSharedCheck_5895_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_5873_ = lean_ctor_get(v_a_5869_, 1);
                v_isSharedCheck_5885_ = (!lean_is_exclusive(v_a_5869_)) as u8;
                if v_isSharedCheck_5885_ == 0 {
                    v_unused_5886_ = lean_ctor_get(v_a_5869_, 0);
                    lean_dec(v_unused_5886_);
                    v___x_5875_ = v_a_5869_;
                    v_isShared_5876_ = v_isSharedCheck_5885_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_5873_);
                    lean_dec(v_a_5869_);
                    v___x_5875_ = lean_box(0);
                    v_isShared_5876_ = v_isSharedCheck_5885_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5877_ = lean_box(0);
                if v_isShared_5876_ == 0 {
                    lean_ctor_set_tag(v___x_5875_, 1);
                    lean_ctor_set(v___x_5875_, 1, v___x_5877_);
                    lean_ctor_set(v___x_5875_, 0, v_snd_5873_);
                    v___x_5879_ = v___x_5875_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5884_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5884_, 0, v_snd_5873_);
                    lean_ctor_set(v_reuseFailAlloc_5884_, 1, v___x_5877_);
                    v___x_5879_ = v_reuseFailAlloc_5884_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5880_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_5880_, 0, v___x_5879_);
                if v_isShared_5872_ == 0 {
                    lean_ctor_set(v___x_5871_, 0, v___x_5880_);
                    v___x_5882_ = v___x_5871_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5883_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5883_, 0, v___x_5880_);
                    v___x_5882_ = v_reuseFailAlloc_5883_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5882_;
            }
            5 => {
                if v_isShared_5891_ == 0 {
                    v___x_5893_ = v___x_5890_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5894_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5894_, 0, v_a_5888_);
                    v___x_5893_ = v_reuseFailAlloc_5894_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5893_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0___boxed(
    mut v_g_5896_: *mut LeanObject,
    mut v___y_5897_: *mut LeanObject,
    mut v___y_5898_: *mut LeanObject,
    mut v___y_5899_: *mut LeanObject,
    mut v___y_5900_: *mut LeanObject,
    mut v___y_5901_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5902_: *mut LeanObject = core::ptr::null_mut();
    v_res_5902_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0(
        v_g_5896_,
        v___y_5897_,
        v___y_5898_,
        v___y_5899_,
        v___y_5900_,
    );
    lean_dec(v___y_5900_);
    lean_dec_ref(v___y_5899_);
    lean_dec(v___y_5898_);
    lean_dec_ref(v___y_5897_);
    return v_res_5902_;
}
pub unsafe fn l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter(
    mut v_cfg_5904_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5906_: *mut LeanObject = core::ptr::null_mut();
    v___f_5905_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___closed__0;
    v___x_5906_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(v_cfg_5904_, v___f_5905_);
    return v___x_5906_;
}
pub unsafe fn l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0(
    mut v_g_5911_: *mut LeanObject,
    mut v___y_5912_: *mut LeanObject,
    mut v___y_5913_: *mut LeanObject,
    mut v___y_5914_: *mut LeanObject,
    mut v___y_5915_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5922_: u8 = 0;
    let mut v___x_5923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5927_: u8 = 0;
    let mut v_a_5928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5931_: u8 = 0;
    let mut v___x_5933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5935_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5917_ =
                    l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0___closed__0;
                v___x_5918_ = l_Lean_MVarId_constructor(
                    v_g_5911_,
                    v___x_5917_,
                    v___y_5912_,
                    v___y_5913_,
                    v___y_5914_,
                    v___y_5915_,
                );
                if lean_obj_tag(v___x_5918_) == 0 {
                    v_a_5919_ = lean_ctor_get(v___x_5918_, 0);
                    v_isSharedCheck_5927_ = (!lean_is_exclusive(v___x_5918_)) as u8;
                    if v_isSharedCheck_5927_ == 0 {
                        v___x_5921_ = v___x_5918_;
                        v_isShared_5922_ = v_isSharedCheck_5927_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5919_);
                        lean_dec(v___x_5918_);
                        v___x_5921_ = lean_box(0);
                        v_isShared_5922_ = v_isSharedCheck_5927_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5928_ = lean_ctor_get(v___x_5918_, 0);
                    v_isSharedCheck_5935_ = (!lean_is_exclusive(v___x_5918_)) as u8;
                    if v_isSharedCheck_5935_ == 0 {
                        v___x_5930_ = v___x_5918_;
                        v_isShared_5931_ = v_isSharedCheck_5935_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5928_);
                        lean_dec(v___x_5918_);
                        v___x_5930_ = lean_box(0);
                        v_isShared_5931_ = v_isSharedCheck_5935_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5923_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_5923_, 0, v_a_5919_);
                if v_isShared_5922_ == 0 {
                    lean_ctor_set(v___x_5921_, 0, v___x_5923_);
                    v___x_5925_ = v___x_5921_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5926_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5926_, 0, v___x_5923_);
                    v___x_5925_ = v_reuseFailAlloc_5926_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5925_;
            }
            3 => {
                if v_isShared_5931_ == 0 {
                    v___x_5933_ = v___x_5930_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5934_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5934_, 0, v_a_5928_);
                    v___x_5933_ = v_reuseFailAlloc_5934_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5933_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0___boxed(
    mut v_g_5936_: *mut LeanObject,
    mut v___y_5937_: *mut LeanObject,
    mut v___y_5938_: *mut LeanObject,
    mut v___y_5939_: *mut LeanObject,
    mut v___y_5940_: *mut LeanObject,
    mut v___y_5941_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5942_: *mut LeanObject = core::ptr::null_mut();
    v_res_5942_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0(
        v_g_5936_,
        v___y_5937_,
        v___y_5938_,
        v___y_5939_,
        v___y_5940_,
    );
    lean_dec(v___y_5940_);
    lean_dec_ref(v___y_5939_);
    lean_dec(v___y_5938_);
    lean_dec_ref(v___y_5937_);
    return v_res_5942_;
}
pub unsafe fn l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter(
    mut v_cfg_5944_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5946_: *mut LeanObject = core::ptr::null_mut();
    v___f_5945_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___closed__0;
    v___x_5946_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(v_cfg_5944_, v___f_5945_);
    return v___x_5946_;
}
pub unsafe fn l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0(
    mut v_g_5949_: *mut LeanObject,
    mut v___y_5950_: *mut LeanObject,
    mut v___y_5951_: *mut LeanObject,
    mut v___y_5952_: *mut LeanObject,
    mut v___y_5953_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5963_: u8 = 0;
    let mut v___x_5964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5968_: u8 = 0;
    let mut v_unused_5969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5973_: u8 = 0;
    let mut v___x_5975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5977_: u8 = 0;
    let mut v_a_5978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5981_: u8 = 0;
    let mut v___x_5983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5985_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_g_5949_);
                v___x_5955_ = l_Lean_MVarId_getType(
                    v_g_5949_,
                    v___y_5950_,
                    v___y_5951_,
                    v___y_5952_,
                    v___y_5953_,
                );
                if lean_obj_tag(v___x_5955_) == 0 {
                    v_a_5956_ = lean_ctor_get(v___x_5955_, 0);
                    lean_inc(v_a_5956_);
                    lean_dec_ref_known(v___x_5955_, 1);
                    v___x_5957_ = lean_box(0);
                    v___x_5958_ = l_Lean_Meta_synthInstance(
                        v_a_5956_,
                        v___x_5957_,
                        v___y_5950_,
                        v___y_5951_,
                        v___y_5952_,
                        v___y_5953_,
                    );
                    if lean_obj_tag(v___x_5958_) == 0 {
                        v_a_5959_ = lean_ctor_get(v___x_5958_, 0);
                        lean_inc(v_a_5959_);
                        lean_dec_ref_known(v___x_5958_, 1);
                        v___x_5960_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_g_5949_, v_a_5959_, v___y_5951_);
                        v_isSharedCheck_5968_ = (!lean_is_exclusive(v___x_5960_)) as u8;
                        if v_isSharedCheck_5968_ == 0 {
                            v_unused_5969_ = lean_ctor_get(v___x_5960_, 0);
                            lean_dec(v_unused_5969_);
                            v___x_5962_ = v___x_5960_;
                            v_isShared_5963_ = v_isSharedCheck_5968_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v___x_5960_);
                            v___x_5962_ = lean_box(0);
                            v_isShared_5963_ = v_isSharedCheck_5968_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_g_5949_);
                        v_a_5970_ = lean_ctor_get(v___x_5958_, 0);
                        v_isSharedCheck_5977_ = (!lean_is_exclusive(v___x_5958_)) as u8;
                        if v_isSharedCheck_5977_ == 0 {
                            v___x_5972_ = v___x_5958_;
                            v_isShared_5973_ = v_isSharedCheck_5977_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_5970_);
                            lean_dec(v___x_5958_);
                            v___x_5972_ = lean_box(0);
                            v_isShared_5973_ = v_isSharedCheck_5977_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_g_5949_);
                    v_a_5978_ = lean_ctor_get(v___x_5955_, 0);
                    v_isSharedCheck_5985_ = (!lean_is_exclusive(v___x_5955_)) as u8;
                    if v_isSharedCheck_5985_ == 0 {
                        v___x_5980_ = v___x_5955_;
                        v_isShared_5981_ = v_isSharedCheck_5985_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_5978_);
                        lean_dec(v___x_5955_);
                        v___x_5980_ = lean_box(0);
                        v_isShared_5981_ = v_isSharedCheck_5985_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5964_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0___closed__0;
                if v_isShared_5963_ == 0 {
                    lean_ctor_set(v___x_5962_, 0, v___x_5964_);
                    v___x_5966_ = v___x_5962_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5967_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5967_, 0, v___x_5964_);
                    v___x_5966_ = v_reuseFailAlloc_5967_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5966_;
            }
            3 => {
                if v_isShared_5973_ == 0 {
                    v___x_5975_ = v___x_5972_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5976_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5976_, 0, v_a_5970_);
                    v___x_5975_ = v_reuseFailAlloc_5976_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5975_;
            }
            5 => {
                if v_isShared_5981_ == 0 {
                    v___x_5983_ = v___x_5980_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5984_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5984_, 0, v_a_5978_);
                    v___x_5983_ = v_reuseFailAlloc_5984_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5983_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0___boxed(
    mut v_g_5986_: *mut LeanObject,
    mut v___y_5987_: *mut LeanObject,
    mut v___y_5988_: *mut LeanObject,
    mut v___y_5989_: *mut LeanObject,
    mut v___y_5990_: *mut LeanObject,
    mut v___y_5991_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5992_: *mut LeanObject = core::ptr::null_mut();
    v_res_5992_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0(
        v_g_5986_,
        v___y_5987_,
        v___y_5988_,
        v___y_5989_,
        v___y_5990_,
    );
    lean_dec(v___y_5990_);
    lean_dec_ref(v___y_5989_);
    lean_dec(v___y_5988_);
    lean_dec_ref(v___y_5987_);
    return v_res_5992_;
}
pub unsafe fn l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter(
    mut v_cfg_5994_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5996_: *mut LeanObject = core::ptr::null_mut();
    v___f_5995_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___closed__0;
    v___x_5996_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(v_cfg_5994_, v___f_5995_);
    return v___x_5996_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg(
    mut v_e_5997_: *mut LeanObject,
    mut v___y_5998_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6000_: u8 = 0;
    let mut v___x_6001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_6003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_6005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_6008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_6009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_6010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_6011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6014_: u8 = 0;
    let mut v___x_6016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6020_: u8 = 0;
    let mut v_unused_6021_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6000_ = l_Lean_Expr_hasMVar(v_e_5997_);
                if v___x_6000_ == 0 {
                    v___x_6001_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6001_, 0, v_e_5997_);
                    return v___x_6001_;
                } else {
                    v___x_6002_ = lean_st_ref_get(v___y_5998_);
                    v_mctx_6003_ = lean_ctor_get(v___x_6002_, 0);
                    lean_inc_ref(v_mctx_6003_);
                    lean_dec(v___x_6002_);
                    v___x_6004_ = l_Lean_instantiateMVarsCore(v_mctx_6003_, v_e_5997_);
                    v_fst_6005_ = lean_ctor_get(v___x_6004_, 0);
                    lean_inc(v_fst_6005_);
                    v_snd_6006_ = lean_ctor_get(v___x_6004_, 1);
                    lean_inc(v_snd_6006_);
                    lean_dec_ref(v___x_6004_);
                    v___x_6007_ = lean_st_ref_take(v___y_5998_);
                    v_cache_6008_ = lean_ctor_get(v___x_6007_, 1);
                    v_zetaDeltaFVarIds_6009_ = lean_ctor_get(v___x_6007_, 2);
                    v_postponed_6010_ = lean_ctor_get(v___x_6007_, 3);
                    v_diag_6011_ = lean_ctor_get(v___x_6007_, 4);
                    v_isSharedCheck_6020_ = (!lean_is_exclusive(v___x_6007_)) as u8;
                    if v_isSharedCheck_6020_ == 0 {
                        v_unused_6021_ = lean_ctor_get(v___x_6007_, 0);
                        lean_dec(v_unused_6021_);
                        v___x_6013_ = v___x_6007_;
                        v_isShared_6014_ = v_isSharedCheck_6020_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_diag_6011_);
                        lean_inc(v_postponed_6010_);
                        lean_inc(v_zetaDeltaFVarIds_6009_);
                        lean_inc(v_cache_6008_);
                        lean_dec(v___x_6007_);
                        v___x_6013_ = lean_box(0);
                        v_isShared_6014_ = v_isSharedCheck_6020_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6014_ == 0 {
                    lean_ctor_set(v___x_6013_, 0, v_snd_6006_);
                    v___x_6016_ = v___x_6013_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6019_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6019_, 0, v_snd_6006_);
                    lean_ctor_set(v_reuseFailAlloc_6019_, 1, v_cache_6008_);
                    lean_ctor_set(v_reuseFailAlloc_6019_, 2, v_zetaDeltaFVarIds_6009_);
                    lean_ctor_set(v_reuseFailAlloc_6019_, 3, v_postponed_6010_);
                    lean_ctor_set(v_reuseFailAlloc_6019_, 4, v_diag_6011_);
                    v___x_6016_ = v_reuseFailAlloc_6019_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6017_ = lean_st_ref_set(v___y_5998_, v___x_6016_);
                v___x_6018_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6018_, 0, v_fst_6005_);
                return v___x_6018_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg___boxed(
    mut v_e_6022_: *mut LeanObject,
    mut v___y_6023_: *mut LeanObject,
    mut v___y_6024_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6025_: *mut LeanObject = core::ptr::null_mut();
    v_res_6025_ = l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg(v_e_6022_, v___y_6023_);
    lean_dec(v___y_6023_);
    return v_res_6025_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0(
    mut v_e_6026_: *mut LeanObject,
    mut v___y_6027_: *mut LeanObject,
    mut v___y_6028_: *mut LeanObject,
    mut v___y_6029_: *mut LeanObject,
    mut v___y_6030_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6032_: *mut LeanObject = core::ptr::null_mut();
    v___x_6032_ = l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg(v_e_6026_, v___y_6028_);
    return v___x_6032_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___boxed(
    mut v_e_6033_: *mut LeanObject,
    mut v___y_6034_: *mut LeanObject,
    mut v___y_6035_: *mut LeanObject,
    mut v___y_6036_: *mut LeanObject,
    mut v___y_6037_: *mut LeanObject,
    mut v___y_6038_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6039_: *mut LeanObject = core::ptr::null_mut();
    v_res_6039_ = l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0(v_e_6033_, v___y_6034_, v___y_6035_, v___y_6036_, v___y_6037_);
    lean_dec(v___y_6037_);
    lean_dec_ref(v___y_6036_);
    lean_dec(v___y_6035_);
    lean_dec_ref(v___y_6034_);
    return v_res_6039_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(
    mut v_mvarId_6040_: *mut LeanObject,
    mut v_x_6041_: *mut LeanObject,
    mut v___y_6042_: *mut LeanObject,
    mut v___y_6043_: *mut LeanObject,
    mut v___y_6044_: *mut LeanObject,
    mut v___y_6045_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6051_: u8 = 0;
    let mut v___x_6053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6055_: u8 = 0;
    let mut v_a_6056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6059_: u8 = 0;
    let mut v___x_6061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6063_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6047_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    lean_box(0),
                    v_mvarId_6040_,
                    v_x_6041_,
                    v___y_6042_,
                    v___y_6043_,
                    v___y_6044_,
                    v___y_6045_,
                );
                if lean_obj_tag(v___x_6047_) == 0 {
                    v_a_6048_ = lean_ctor_get(v___x_6047_, 0);
                    v_isSharedCheck_6055_ = (!lean_is_exclusive(v___x_6047_)) as u8;
                    if v_isSharedCheck_6055_ == 0 {
                        v___x_6050_ = v___x_6047_;
                        v_isShared_6051_ = v_isSharedCheck_6055_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6048_);
                        lean_dec(v___x_6047_);
                        v___x_6050_ = lean_box(0);
                        v_isShared_6051_ = v_isSharedCheck_6055_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6056_ = lean_ctor_get(v___x_6047_, 0);
                    v_isSharedCheck_6063_ = (!lean_is_exclusive(v___x_6047_)) as u8;
                    if v_isSharedCheck_6063_ == 0 {
                        v___x_6058_ = v___x_6047_;
                        v_isShared_6059_ = v_isSharedCheck_6063_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6056_);
                        lean_dec(v___x_6047_);
                        v___x_6058_ = lean_box(0);
                        v_isShared_6059_ = v_isSharedCheck_6063_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6051_ == 0 {
                    v___x_6053_ = v___x_6050_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6054_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6054_, 0, v_a_6048_);
                    v___x_6053_ = v_reuseFailAlloc_6054_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6053_;
            }
            3 => {
                if v_isShared_6059_ == 0 {
                    v___x_6061_ = v___x_6058_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6062_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6062_, 0, v_a_6056_);
                    v___x_6061_ = v_reuseFailAlloc_6062_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6061_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg___boxed(
    mut v_mvarId_6064_: *mut LeanObject,
    mut v_x_6065_: *mut LeanObject,
    mut v___y_6066_: *mut LeanObject,
    mut v___y_6067_: *mut LeanObject,
    mut v___y_6068_: *mut LeanObject,
    mut v___y_6069_: *mut LeanObject,
    mut v___y_6070_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6071_: *mut LeanObject = core::ptr::null_mut();
    v_res_6071_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_mvarId_6064_, v_x_6065_, v___y_6066_, v___y_6067_, v___y_6068_, v___y_6069_);
    lean_dec(v___y_6069_);
    lean_dec_ref(v___y_6068_);
    lean_dec(v___y_6067_);
    lean_dec_ref(v___y_6066_);
    return v_res_6071_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1(
    mut v_00_u03b1_6072_: *mut LeanObject,
    mut v_mvarId_6073_: *mut LeanObject,
    mut v_x_6074_: *mut LeanObject,
    mut v___y_6075_: *mut LeanObject,
    mut v___y_6076_: *mut LeanObject,
    mut v___y_6077_: *mut LeanObject,
    mut v___y_6078_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6080_: *mut LeanObject = core::ptr::null_mut();
    v___x_6080_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_mvarId_6073_, v_x_6074_, v___y_6075_, v___y_6076_, v___y_6077_, v___y_6078_);
    return v___x_6080_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___boxed(
    mut v_00_u03b1_6081_: *mut LeanObject,
    mut v_mvarId_6082_: *mut LeanObject,
    mut v_x_6083_: *mut LeanObject,
    mut v___y_6084_: *mut LeanObject,
    mut v___y_6085_: *mut LeanObject,
    mut v___y_6086_: *mut LeanObject,
    mut v___y_6087_: *mut LeanObject,
    mut v___y_6088_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6089_: *mut LeanObject = core::ptr::null_mut();
    v_res_6089_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1(v_00_u03b1_6081_, v_mvarId_6082_, v_x_6083_, v___y_6084_, v___y_6085_, v___y_6086_, v___y_6087_);
    lean_dec(v___y_6087_);
    lean_dec_ref(v___y_6086_);
    lean_dec(v___y_6085_);
    lean_dec_ref(v___y_6084_);
    return v_res_6089_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(
    mut v_msg_6090_: *mut LeanObject,
    mut v___y_6091_: *mut LeanObject,
    mut v___y_6092_: *mut LeanObject,
    mut v___y_6093_: *mut LeanObject,
    mut v___y_6094_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_6096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6101_: u8 = 0;
    let mut v___x_6102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6106_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_6096_ = lean_ctor_get(v___y_6093_, 5);
                v___x_6097_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3_spec__6(v_msg_6090_, v___y_6091_, v___y_6092_, v___y_6093_, v___y_6094_);
                v_a_6098_ = lean_ctor_get(v___x_6097_, 0);
                v_isSharedCheck_6106_ = (!lean_is_exclusive(v___x_6097_)) as u8;
                if v_isSharedCheck_6106_ == 0 {
                    v___x_6100_ = v___x_6097_;
                    v_isShared_6101_ = v_isSharedCheck_6106_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_6098_);
                    lean_dec(v___x_6097_);
                    v___x_6100_ = lean_box(0);
                    v_isShared_6101_ = v_isSharedCheck_6106_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_6096_);
                v___x_6102_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6102_, 0, v_ref_6096_);
                lean_ctor_set(v___x_6102_, 1, v_a_6098_);
                if v_isShared_6101_ == 0 {
                    lean_ctor_set_tag(v___x_6100_, 1);
                    lean_ctor_set(v___x_6100_, 0, v___x_6102_);
                    v___x_6104_ = v___x_6100_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6105_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6105_, 0, v___x_6102_);
                    v___x_6104_ = v_reuseFailAlloc_6105_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6104_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg___boxed(
    mut v_msg_6107_: *mut LeanObject,
    mut v___y_6108_: *mut LeanObject,
    mut v___y_6109_: *mut LeanObject,
    mut v___y_6110_: *mut LeanObject,
    mut v___y_6111_: *mut LeanObject,
    mut v___y_6112_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6113_: *mut LeanObject = core::ptr::null_mut();
    v_res_6113_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v_msg_6107_, v___y_6108_, v___y_6109_, v___y_6110_, v___y_6111_);
    lean_dec(v___y_6111_);
    lean_dec_ref(v___y_6110_);
    lean_dec(v___y_6109_);
    lean_dec_ref(v___y_6108_);
    return v_res_6113_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2(
    mut v_x_6114_: *mut LeanObject,
    mut v_x_6115_: *mut LeanObject,
    mut v___y_6116_: *mut LeanObject,
    mut v___y_6117_: *mut LeanObject,
    mut v___y_6118_: *mut LeanObject,
    mut v___y_6119_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_6123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6127_: u8 = 0;
    let mut v___x_6128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6139_: u8 = 0;
    let mut v___x_6141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6143_: u8 = 0;
    let mut v_isSharedCheck_6144_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6114_) == 0 {
                    v___x_6121_ = l_List_reverse___redArg(v_x_6115_);
                    v___x_6122_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6122_, 0, v___x_6121_);
                    return v___x_6122_;
                } else {
                    v_head_6123_ = lean_ctor_get(v_x_6114_, 0);
                    v_tail_6124_ = lean_ctor_get(v_x_6114_, 1);
                    v_isSharedCheck_6144_ = (!lean_is_exclusive(v_x_6114_)) as u8;
                    if v_isSharedCheck_6144_ == 0 {
                        v___x_6126_ = v_x_6114_;
                        v_isShared_6127_ = v_isSharedCheck_6144_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_6124_);
                        lean_inc(v_head_6123_);
                        lean_dec(v_x_6114_);
                        v___x_6126_ = lean_box(0);
                        v_isShared_6127_ = v_isSharedCheck_6144_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_head_6123_);
                v___x_6128_ = l_Lean_Expr_mvar___override(v_head_6123_);
                v___x_6129_ = lean_alloc_closure(l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___boxed as *mut core::ffi::c_void, 6, 1);
                lean_closure_set(v___x_6129_, 0, v___x_6128_);
                v___x_6130_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_head_6123_, v___x_6129_, v___y_6116_, v___y_6117_, v___y_6118_, v___y_6119_);
                if lean_obj_tag(v___x_6130_) == 0 {
                    v_a_6131_ = lean_ctor_get(v___x_6130_, 0);
                    lean_inc(v_a_6131_);
                    lean_dec_ref_known(v___x_6130_, 1);
                    if v_isShared_6127_ == 0 {
                        lean_ctor_set(v___x_6126_, 1, v_x_6115_);
                        lean_ctor_set(v___x_6126_, 0, v_a_6131_);
                        v___x_6133_ = v___x_6126_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6135_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6135_, 0, v_a_6131_);
                        lean_ctor_set(v_reuseFailAlloc_6135_, 1, v_x_6115_);
                        v___x_6133_ = v_reuseFailAlloc_6135_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_6126_);
                    lean_dec(v_tail_6124_);
                    lean_dec(v_x_6115_);
                    v_a_6136_ = lean_ctor_get(v___x_6130_, 0);
                    v_isSharedCheck_6143_ = (!lean_is_exclusive(v___x_6130_)) as u8;
                    if v_isSharedCheck_6143_ == 0 {
                        v___x_6138_ = v___x_6130_;
                        v_isShared_6139_ = v_isSharedCheck_6143_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6136_);
                        lean_dec(v___x_6130_);
                        v___x_6138_ = lean_box(0);
                        v_isShared_6139_ = v_isSharedCheck_6143_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v_x_6114_ = v_tail_6124_;
                v_x_6115_ = v___x_6133_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_6139_ == 0 {
                    v___x_6141_ = v___x_6138_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6142_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6142_, 0, v_a_6136_);
                    v___x_6141_ = v_reuseFailAlloc_6142_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6141_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2___boxed(
    mut v_x_6145_: *mut LeanObject,
    mut v_x_6146_: *mut LeanObject,
    mut v___y_6147_: *mut LeanObject,
    mut v___y_6148_: *mut LeanObject,
    mut v___y_6149_: *mut LeanObject,
    mut v___y_6150_: *mut LeanObject,
    mut v___y_6151_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6152_: *mut LeanObject = core::ptr::null_mut();
    v_res_6152_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2(v_x_6145_, v_x_6146_, v___y_6147_, v___y_6148_, v___y_6149_, v___y_6150_);
    lean_dec(v___y_6150_);
    lean_dec_ref(v___y_6149_);
    lean_dec(v___y_6148_);
    lean_dec_ref(v___y_6147_);
    return v_res_6152_;
}
pub unsafe fn _init_l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1()
-> *mut LeanObject {
    let mut v___x_6154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6155_: *mut LeanObject = core::ptr::null_mut();
    v___x_6154_ =
        l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__0;
    v___x_6155_ = l_Lean_stringToMessageData(v___x_6154_);
    return v___x_6155_;
}
pub unsafe fn l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0(
    mut v_test_6156_: *mut LeanObject,
    mut v_proc_6157_: *mut LeanObject,
    mut v_orig_6158_: *mut LeanObject,
    mut v_goals_6159_: *mut LeanObject,
    mut v___y_6160_: *mut LeanObject,
    mut v___y_6161_: *mut LeanObject,
    mut v___y_6162_: *mut LeanObject,
    mut v___y_6163_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6170_: u8 = 0;
    let mut v___x_6171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6176_: u8 = 0;
    let mut v___x_6178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6180_: u8 = 0;
    let mut v___x_6181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6185_: u8 = 0;
    let mut v___x_6187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6189_: u8 = 0;
    let mut v_a_6190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6193_: u8 = 0;
    let mut v___x_6195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6197_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6165_ = lean_box(0);
                lean_inc(v_orig_6158_);
                v___x_6166_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2(v_orig_6158_, v___x_6165_, v___y_6160_, v___y_6161_, v___y_6162_, v___y_6163_);
                if lean_obj_tag(v___x_6166_) == 0 {
                    v_a_6167_ = lean_ctor_get(v___x_6166_, 0);
                    lean_inc(v_a_6167_);
                    lean_dec_ref_known(v___x_6166_, 1);
                    lean_inc(v___y_6163_);
                    lean_inc_ref(v___y_6162_);
                    lean_inc(v___y_6161_);
                    lean_inc_ref(v___y_6160_);
                    v___x_6168_ = lean_apply_6(
                        v_test_6156_,
                        v_a_6167_,
                        v___y_6160_,
                        v___y_6161_,
                        v___y_6162_,
                        v___y_6163_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_6168_) == 0 {
                        v_a_6169_ = lean_ctor_get(v___x_6168_, 0);
                        lean_inc(v_a_6169_);
                        lean_dec_ref_known(v___x_6168_, 1);
                        v___x_6170_ = (lean_unbox(v_a_6169_) as u8);
                        lean_dec(v_a_6169_);
                        if v___x_6170_ == 0 {
                            lean_dec(v_goals_6159_);
                            lean_dec(v_orig_6158_);
                            lean_dec_ref(v_proc_6157_);
                            v___x_6171_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1_once), _init_l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1);
                            v___x_6172_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_6171_, v___y_6160_, v___y_6161_, v___y_6162_, v___y_6163_);
                            v_a_6173_ = lean_ctor_get(v___x_6172_, 0);
                            v_isSharedCheck_6180_ = (!lean_is_exclusive(v___x_6172_)) as u8;
                            if v_isSharedCheck_6180_ == 0 {
                                v___x_6175_ = v___x_6172_;
                                v_isShared_6176_ = v_isSharedCheck_6180_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_6173_);
                                lean_dec(v___x_6172_);
                                v___x_6175_ = lean_box(0);
                                v_isShared_6176_ = v_isSharedCheck_6180_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_inc(v___y_6163_);
                            lean_inc_ref(v___y_6162_);
                            lean_inc(v___y_6161_);
                            lean_inc_ref(v___y_6160_);
                            v___x_6181_ = lean_apply_7(
                                v_proc_6157_,
                                v_orig_6158_,
                                v_goals_6159_,
                                v___y_6160_,
                                v___y_6161_,
                                v___y_6162_,
                                v___y_6163_,
                                lean_box(0),
                            );
                            return v___x_6181_;
                        }
                    } else {
                        lean_dec(v_goals_6159_);
                        lean_dec(v_orig_6158_);
                        lean_dec_ref(v_proc_6157_);
                        v_a_6182_ = lean_ctor_get(v___x_6168_, 0);
                        v_isSharedCheck_6189_ = (!lean_is_exclusive(v___x_6168_)) as u8;
                        if v_isSharedCheck_6189_ == 0 {
                            v___x_6184_ = v___x_6168_;
                            v_isShared_6185_ = v_isSharedCheck_6189_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_6182_);
                            lean_dec(v___x_6168_);
                            v___x_6184_ = lean_box(0);
                            v_isShared_6185_ = v_isSharedCheck_6189_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_goals_6159_);
                    lean_dec(v_orig_6158_);
                    lean_dec_ref(v_proc_6157_);
                    lean_dec_ref(v_test_6156_);
                    v_a_6190_ = lean_ctor_get(v___x_6166_, 0);
                    v_isSharedCheck_6197_ = (!lean_is_exclusive(v___x_6166_)) as u8;
                    if v_isSharedCheck_6197_ == 0 {
                        v___x_6192_ = v___x_6166_;
                        v_isShared_6193_ = v_isSharedCheck_6197_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_6190_);
                        lean_dec(v___x_6166_);
                        v___x_6192_ = lean_box(0);
                        v_isShared_6193_ = v_isSharedCheck_6197_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6176_ == 0 {
                    v___x_6178_ = v___x_6175_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6179_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6179_, 0, v_a_6173_);
                    v___x_6178_ = v_reuseFailAlloc_6179_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6178_;
            }
            3 => {
                if v_isShared_6185_ == 0 {
                    v___x_6187_ = v___x_6184_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6188_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6188_, 0, v_a_6182_);
                    v___x_6187_ = v_reuseFailAlloc_6188_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6187_;
            }
            5 => {
                if v_isShared_6193_ == 0 {
                    v___x_6195_ = v___x_6192_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6196_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6196_, 0, v_a_6190_);
                    v___x_6195_ = v_reuseFailAlloc_6196_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6195_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___boxed(
    mut v_test_6198_: *mut LeanObject,
    mut v_proc_6199_: *mut LeanObject,
    mut v_orig_6200_: *mut LeanObject,
    mut v_goals_6201_: *mut LeanObject,
    mut v___y_6202_: *mut LeanObject,
    mut v___y_6203_: *mut LeanObject,
    mut v___y_6204_: *mut LeanObject,
    mut v___y_6205_: *mut LeanObject,
    mut v___y_6206_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6207_: *mut LeanObject = core::ptr::null_mut();
    v_res_6207_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0(
        v_test_6198_,
        v_proc_6199_,
        v_orig_6200_,
        v_goals_6201_,
        v___y_6202_,
        v___y_6203_,
        v___y_6204_,
        v___y_6205_,
    );
    lean_dec(v___y_6205_);
    lean_dec_ref(v___y_6204_);
    lean_dec(v___y_6203_);
    lean_dec_ref(v___y_6202_);
    return v_res_6207_;
}
pub unsafe fn l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions(
    mut v_cfg_6208_: *mut LeanObject,
    mut v_test_6209_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplyRulesConfig_6210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBacktrackConfig_6211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_backtracking_6212_: u8 = 0;
    let mut v_intro_6213_: u8 = 0;
    let mut v_constructor_6214_: u8 = 0;
    let mut v_suggestions_6215_: u8 = 0;
    let mut v___x_6217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6218_: u8 = 0;
    let mut v_toApplyConfig_6219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_transparency_6220_: u8 = 0;
    let mut v_symm_6221_: u8 = 0;
    let mut v_exfalso_6222_: u8 = 0;
    let mut v___x_6224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6225_: u8 = 0;
    let mut v_maxDepth_6226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proc_6227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suspend_6228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_discharge_6229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_commitIndependentGoals_6230_: u8 = 0;
    let mut v___x_6232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6233_: u8 = 0;
    let mut v___f_6234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6244_: u8 = 0;
    let mut v_isSharedCheck_6245_: u8 = 0;
    let mut v_unused_6246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6247_: u8 = 0;
    let mut v_unused_6248_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplyRulesConfig_6210_ = lean_ctor_get(v_cfg_6208_, 0);
                lean_inc_ref(v_toApplyRulesConfig_6210_);
                v_toBacktrackConfig_6211_ = lean_ctor_get(v_toApplyRulesConfig_6210_, 0);
                lean_inc_ref(v_toBacktrackConfig_6211_);
                v_backtracking_6212_ = lean_ctor_get_uint8(
                    v_cfg_6208_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_intro_6213_ = lean_ctor_get_uint8(
                    v_cfg_6208_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                );
                v_constructor_6214_ = lean_ctor_get_uint8(
                    v_cfg_6208_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 2) as u32,
                );
                v_suggestions_6215_ = lean_ctor_get_uint8(
                    v_cfg_6208_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 3) as u32,
                );
                v_isSharedCheck_6247_ = (!lean_is_exclusive(v_cfg_6208_)) as u8;
                if v_isSharedCheck_6247_ == 0 {
                    v_unused_6248_ = lean_ctor_get(v_cfg_6208_, 0);
                    lean_dec(v_unused_6248_);
                    v___x_6217_ = v_cfg_6208_;
                    v_isShared_6218_ = v_isSharedCheck_6247_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v_cfg_6208_);
                    v___x_6217_ = lean_box(0);
                    v_isShared_6218_ = v_isSharedCheck_6247_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toApplyConfig_6219_ = lean_ctor_get(v_toApplyRulesConfig_6210_, 1);
                v_transparency_6220_ = lean_ctor_get_uint8(
                    v_toApplyRulesConfig_6210_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                );
                v_symm_6221_ = lean_ctor_get_uint8(
                    v_toApplyRulesConfig_6210_,
                    (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                );
                v_exfalso_6222_ = lean_ctor_get_uint8(
                    v_toApplyRulesConfig_6210_,
                    (core::mem::size_of::<*mut LeanObject>() * 2 + 2) as u32,
                );
                v_isSharedCheck_6245_ = (!lean_is_exclusive(v_toApplyRulesConfig_6210_)) as u8;
                if v_isSharedCheck_6245_ == 0 {
                    v_unused_6246_ = lean_ctor_get(v_toApplyRulesConfig_6210_, 0);
                    lean_dec(v_unused_6246_);
                    v___x_6224_ = v_toApplyRulesConfig_6210_;
                    v_isShared_6225_ = v_isSharedCheck_6245_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_toApplyConfig_6219_);
                    lean_dec(v_toApplyRulesConfig_6210_);
                    v___x_6224_ = lean_box(0);
                    v_isShared_6225_ = v_isSharedCheck_6245_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_maxDepth_6226_ = lean_ctor_get(v_toBacktrackConfig_6211_, 0);
                v_proc_6227_ = lean_ctor_get(v_toBacktrackConfig_6211_, 1);
                v_suspend_6228_ = lean_ctor_get(v_toBacktrackConfig_6211_, 2);
                v_discharge_6229_ = lean_ctor_get(v_toBacktrackConfig_6211_, 3);
                v_commitIndependentGoals_6230_ = lean_ctor_get_uint8(
                    v_toBacktrackConfig_6211_,
                    (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                );
                v_isSharedCheck_6244_ = (!lean_is_exclusive(v_toBacktrackConfig_6211_)) as u8;
                if v_isSharedCheck_6244_ == 0 {
                    v___x_6232_ = v_toBacktrackConfig_6211_;
                    v_isShared_6233_ = v_isSharedCheck_6244_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_discharge_6229_);
                    lean_inc(v_suspend_6228_);
                    lean_inc(v_proc_6227_);
                    lean_inc(v_maxDepth_6226_);
                    lean_dec(v_toBacktrackConfig_6211_);
                    v___x_6232_ = lean_box(0);
                    v_isShared_6233_ = v_isSharedCheck_6244_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___f_6234_ = lean_alloc_closure(
                    l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___boxed
                        as *mut core::ffi::c_void,
                    9,
                    2,
                );
                lean_closure_set(v___f_6234_, 0, v_test_6209_);
                lean_closure_set(v___f_6234_, 1, v_proc_6227_);
                if v_isShared_6233_ == 0 {
                    lean_ctor_set(v___x_6232_, 1, v___f_6234_);
                    v___x_6236_ = v___x_6232_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6243_ = lean_alloc_ctor(0, 4, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6243_, 0, v_maxDepth_6226_);
                    lean_ctor_set(v_reuseFailAlloc_6243_, 1, v___f_6234_);
                    lean_ctor_set(v_reuseFailAlloc_6243_, 2, v_suspend_6228_);
                    lean_ctor_set(v_reuseFailAlloc_6243_, 3, v_discharge_6229_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_6243_,
                        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                        v_commitIndependentGoals_6230_,
                    );
                    v___x_6236_ = v_reuseFailAlloc_6243_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_6225_ == 0 {
                    lean_ctor_set(v___x_6224_, 0, v___x_6236_);
                    v___x_6238_ = v___x_6224_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6242_ = lean_alloc_ctor(0, 2, (3) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6242_, 0, v___x_6236_);
                    lean_ctor_set(v_reuseFailAlloc_6242_, 1, v_toApplyConfig_6219_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_6242_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        v_transparency_6220_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_6242_,
                        (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                        v_symm_6221_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_6242_,
                        (core::mem::size_of::<*mut LeanObject>() * 2 + 2) as u32,
                        v_exfalso_6222_,
                    );
                    v___x_6238_ = v_reuseFailAlloc_6242_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_6218_ == 0 {
                    lean_ctor_set(v___x_6217_, 0, v___x_6238_);
                    v___x_6240_ = v___x_6217_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6241_ = lean_alloc_ctor(0, 1, (4) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6241_, 0, v___x_6238_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_6241_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_backtracking_6212_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_6241_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                        v_intro_6213_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_6241_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 2) as u32,
                        v_constructor_6214_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_6241_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 3) as u32,
                        v_suggestions_6215_,
                    );
                    v___x_6240_ = v_reuseFailAlloc_6241_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6240_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3(
    mut v_00_u03b1_6249_: *mut LeanObject,
    mut v_msg_6250_: *mut LeanObject,
    mut v___y_6251_: *mut LeanObject,
    mut v___y_6252_: *mut LeanObject,
    mut v___y_6253_: *mut LeanObject,
    mut v___y_6254_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6256_: *mut LeanObject = core::ptr::null_mut();
    v___x_6256_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v_msg_6250_, v___y_6251_, v___y_6252_, v___y_6253_, v___y_6254_);
    return v___x_6256_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___boxed(
    mut v_00_u03b1_6257_: *mut LeanObject,
    mut v_msg_6258_: *mut LeanObject,
    mut v___y_6259_: *mut LeanObject,
    mut v___y_6260_: *mut LeanObject,
    mut v___y_6261_: *mut LeanObject,
    mut v___y_6262_: *mut LeanObject,
    mut v___y_6263_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6264_: *mut LeanObject = core::ptr::null_mut();
    v_res_6264_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3(v_00_u03b1_6257_, v_msg_6258_, v___y_6259_, v___y_6260_, v___y_6261_, v___y_6262_);
    lean_dec(v___y_6262_);
    lean_dec_ref(v___y_6261_);
    lean_dec(v___y_6260_);
    lean_dec_ref(v___y_6259_);
    return v_res_6264_;
}
pub unsafe fn l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions_spec__0(
    mut v_x_6265_: *mut LeanObject,
) -> u8 {
    let mut v___x_6266_: u8 = 0;
    let mut v_head_6267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6269_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6265_) == 0 {
                    v___x_6266_ = 0;
                    return v___x_6266_;
                } else {
                    v_head_6267_ = lean_ctor_get(v_x_6265_, 0);
                    v_tail_6268_ = lean_ctor_get(v_x_6265_, 1);
                    v___x_6269_ = l_Lean_Expr_hasMVar(v_head_6267_);
                    if v___x_6269_ == 0 {
                        v_x_6265_ = v_tail_6268_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_6269_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions_spec__0___boxed(
    mut v_x_6271_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6272_: u8 = 0;
    let mut v_r_6273_: *mut LeanObject = core::ptr::null_mut();
    v_res_6272_ = l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions_spec__0(
        v_x_6271_,
    );
    lean_dec(v_x_6271_);
    v_r_6273_ = lean_box((v_res_6272_) as usize);
    return v_r_6273_;
}
pub unsafe fn l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0(
    mut v_test_6274_: *mut LeanObject,
    mut v_sols_6275_: *mut LeanObject,
    mut v___y_6276_: *mut LeanObject,
    mut v___y_6277_: *mut LeanObject,
    mut v___y_6278_: *mut LeanObject,
    mut v___y_6279_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6281_: u8 = 0;
    v___x_6281_ = l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions_spec__0(
        v_sols_6275_,
    );
    if v___x_6281_ == 0 {
        let mut v___x_6282_: *mut LeanObject = core::ptr::null_mut();
        lean_inc(v___y_6279_);
        lean_inc_ref(v___y_6278_);
        lean_inc(v___y_6277_);
        lean_inc_ref(v___y_6276_);
        v___x_6282_ = lean_apply_6(
            v_test_6274_,
            v_sols_6275_,
            v___y_6276_,
            v___y_6277_,
            v___y_6278_,
            v___y_6279_,
            lean_box(0),
        );
        return v___x_6282_;
    } else {
        let mut v___x_6283_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6284_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_sols_6275_);
        lean_dec_ref(v_test_6274_);
        v___x_6283_ = lean_box((v___x_6281_) as usize);
        v___x_6284_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_6284_, 0, v___x_6283_);
        return v___x_6284_;
    }
}
pub unsafe fn l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0___boxed(
    mut v_test_6285_: *mut LeanObject,
    mut v_sols_6286_: *mut LeanObject,
    mut v___y_6287_: *mut LeanObject,
    mut v___y_6288_: *mut LeanObject,
    mut v___y_6289_: *mut LeanObject,
    mut v___y_6290_: *mut LeanObject,
    mut v___y_6291_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6292_: *mut LeanObject = core::ptr::null_mut();
    v_res_6292_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0(
        v_test_6285_,
        v_sols_6286_,
        v___y_6287_,
        v___y_6288_,
        v___y_6289_,
        v___y_6290_,
    );
    lean_dec(v___y_6290_);
    lean_dec_ref(v___y_6289_);
    lean_dec(v___y_6288_);
    lean_dec_ref(v___y_6287_);
    return v_res_6292_;
}
pub unsafe fn l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions(
    mut v_cfg_6293_: *mut LeanObject,
    mut v_test_6294_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6296_: *mut LeanObject = core::ptr::null_mut();
    v___f_6295_ = lean_alloc_closure(
        l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0___boxed
            as *mut core::ffi::c_void,
        7,
        1,
    );
    lean_closure_set(v___f_6295_, 0, v_test_6294_);
    v___x_6296_ =
        l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions(v_cfg_6293_, v___f_6295_);
    return v___x_6296_;
}
pub unsafe fn l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__0(
    mut v_e_6297_: *mut LeanObject,
    mut v_x_6298_: *mut LeanObject,
) -> u8 {
    let mut v___x_6299_: u8 = 0;
    let mut v_head_6300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6302_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6298_) == 0 {
                    lean_dec_ref(v_e_6297_);
                    v___x_6299_ = 0;
                    return v___x_6299_;
                } else {
                    v_head_6300_ = lean_ctor_get(v_x_6298_, 0);
                    v_tail_6301_ = lean_ctor_get(v_x_6298_, 1);
                    lean_inc_ref(v_e_6297_);
                    v___x_6302_ = l_Lean_Expr_occurs(v_e_6297_, v_head_6300_);
                    if v___x_6302_ == 0 {
                        v_x_6298_ = v_tail_6301_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_e_6297_);
                        return v___x_6302_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__0___boxed(
    mut v_e_6304_: *mut LeanObject,
    mut v_x_6305_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6306_: u8 = 0;
    let mut v_r_6307_: *mut LeanObject = core::ptr::null_mut();
    v_res_6306_ =
        l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__0(
            v_e_6304_, v_x_6305_,
        );
    lean_dec(v_x_6305_);
    v_r_6307_ = lean_box((v_res_6306_) as usize);
    return v_r_6307_;
}
pub unsafe fn l_List_all___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__1(
    mut v_sols_6308_: *mut LeanObject,
    mut v_x_6309_: *mut LeanObject,
) -> u8 {
    let mut v___x_6310_: u8 = 0;
    let mut v_head_6311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6313_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6309_) == 0 {
                    v___x_6310_ = 1;
                    return v___x_6310_;
                } else {
                    v_head_6311_ = lean_ctor_get(v_x_6309_, 0);
                    lean_inc(v_head_6311_);
                    v_tail_6312_ = lean_ctor_get(v_x_6309_, 1);
                    lean_inc(v_tail_6312_);
                    lean_dec_ref_known(v_x_6309_, 2);
                    v___x_6313_ = l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__0(v_head_6311_, v_sols_6308_);
                    if v___x_6313_ == 0 {
                        lean_dec(v_tail_6312_);
                        return v___x_6313_;
                    } else {
                        v_x_6309_ = v_tail_6312_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_all___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__1___boxed(
    mut v_sols_6315_: *mut LeanObject,
    mut v_x_6316_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6317_: u8 = 0;
    let mut v_r_6318_: *mut LeanObject = core::ptr::null_mut();
    v_res_6317_ =
        l_List_all___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__1(
            v_sols_6315_,
            v_x_6316_,
        );
    lean_dec(v_sols_6315_);
    v_r_6318_ = lean_box((v_res_6317_) as usize);
    return v_r_6318_;
}
pub unsafe fn l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0(
    mut v_use_6319_: *mut LeanObject,
    mut v_sols_6320_: *mut LeanObject,
    mut v___y_6321_: *mut LeanObject,
    mut v___y_6322_: *mut LeanObject,
    mut v___y_6323_: *mut LeanObject,
    mut v___y_6324_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6326_: u8 = 0;
    let mut v___x_6327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6328_: *mut LeanObject = core::ptr::null_mut();
    v___x_6326_ =
        l_List_all___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__1(
            v_sols_6320_,
            v_use_6319_,
        );
    v___x_6327_ = lean_box((v___x_6326_) as usize);
    v___x_6328_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_6328_, 0, v___x_6327_);
    return v___x_6328_;
}
pub unsafe fn l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0___boxed(
    mut v_use_6329_: *mut LeanObject,
    mut v_sols_6330_: *mut LeanObject,
    mut v___y_6331_: *mut LeanObject,
    mut v___y_6332_: *mut LeanObject,
    mut v___y_6333_: *mut LeanObject,
    mut v___y_6334_: *mut LeanObject,
    mut v___y_6335_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6336_: *mut LeanObject = core::ptr::null_mut();
    v_res_6336_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0(
        v_use_6329_,
        v_sols_6330_,
        v___y_6331_,
        v___y_6332_,
        v___y_6333_,
        v___y_6334_,
    );
    lean_dec(v___y_6334_);
    lean_dec_ref(v___y_6333_);
    lean_dec(v___y_6332_);
    lean_dec_ref(v___y_6331_);
    lean_dec(v_sols_6330_);
    return v_res_6336_;
}
pub unsafe fn l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll(
    mut v_cfg_6337_: *mut LeanObject,
    mut v_use_6338_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6340_: *mut LeanObject = core::ptr::null_mut();
    v___f_6339_ = lean_alloc_closure(
        l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0___boxed
            as *mut core::ffi::c_void,
        7,
        1,
    );
    lean_closure_set(v___f_6339_, 0, v_use_6338_);
    v___x_6340_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions(v_cfg_6337_, v___f_6339_);
    return v___x_6340_;
}
pub unsafe fn l_Lean_Meta_SolveByElim_SolveByElimConfig_processOptions(
    mut v_cfg_6341_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_6343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplyRulesConfig_6344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_backtracking_6345_: u8 = 0;
    let mut v_intro_6346_: u8 = 0;
    let mut v_constructor_6347_: u8 = 0;
    let mut v_suggestions_6348_: u8 = 0;
    let mut v___x_6349_: u8 = 0;
    let mut v___x_6350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_intro_6352_: u8 = 0;
    let mut v_toApplyRulesConfig_6353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_backtracking_6354_: u8 = 0;
    let mut v_constructor_6355_: u8 = 0;
    let mut v_suggestions_6356_: u8 = 0;
    let mut v_toApplyRulesConfig_6357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_backtracking_6358_: u8 = 0;
    let mut v_constructor_6359_: u8 = 0;
    let mut v_suggestions_6360_: u8 = 0;
    let mut v___x_6362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6363_: u8 = 0;
    let mut v___x_6364_: u8 = 0;
    let mut v___x_6366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplyRulesConfig_6368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_backtracking_6369_: u8 = 0;
    let mut v_intro_6370_: u8 = 0;
    let mut v_constructor_6371_: u8 = 0;
    let mut v_suggestions_6372_: u8 = 0;
    let mut v_reuseFailAlloc_6373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6374_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_intro_6352_ = lean_ctor_get_uint8(
                    v_cfg_6341_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                );
                if v_intro_6352_ == 0 {
                    v_toApplyRulesConfig_6353_ = lean_ctor_get(v_cfg_6341_, 0);
                    lean_inc_ref(v_toApplyRulesConfig_6353_);
                    v_backtracking_6354_ = lean_ctor_get_uint8(
                        v_cfg_6341_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    v_constructor_6355_ = lean_ctor_get_uint8(
                        v_cfg_6341_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 2) as u32,
                    );
                    v_suggestions_6356_ = lean_ctor_get_uint8(
                        v_cfg_6341_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 3) as u32,
                    );
                    v___y_6343_ = v_cfg_6341_;
                    v_toApplyRulesConfig_6344_ = v_toApplyRulesConfig_6353_;
                    v_backtracking_6345_ = v_backtracking_6354_;
                    v_intro_6346_ = v_intro_6352_;
                    v_constructor_6347_ = v_constructor_6355_;
                    v_suggestions_6348_ = v_suggestions_6356_;
                    state = 1;
                    continue;
                } else {
                    v_toApplyRulesConfig_6357_ = lean_ctor_get(v_cfg_6341_, 0);
                    v_backtracking_6358_ = lean_ctor_get_uint8(
                        v_cfg_6341_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    v_constructor_6359_ = lean_ctor_get_uint8(
                        v_cfg_6341_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 2) as u32,
                    );
                    v_suggestions_6360_ = lean_ctor_get_uint8(
                        v_cfg_6341_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 3) as u32,
                    );
                    v_isSharedCheck_6374_ = (!lean_is_exclusive(v_cfg_6341_)) as u8;
                    if v_isSharedCheck_6374_ == 0 {
                        v___x_6362_ = v_cfg_6341_;
                        v_isShared_6363_ = v_isSharedCheck_6374_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_toApplyRulesConfig_6357_);
                        lean_dec(v_cfg_6341_);
                        v___x_6362_ = lean_box(0);
                        v_isShared_6363_ = v_isSharedCheck_6374_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                if v_constructor_6347_ == 0 {
                    lean_dec_ref(v_toApplyRulesConfig_6344_);
                    return v___y_6343_;
                } else {
                    lean_dec_ref(v___y_6343_);
                    v___x_6349_ = 0;
                    v___x_6350_ = lean_alloc_ctor(0, 1, (4) as u32);
                    lean_ctor_set(v___x_6350_, 0, v_toApplyRulesConfig_6344_);
                    lean_ctor_set_uint8(
                        v___x_6350_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_backtracking_6345_,
                    );
                    lean_ctor_set_uint8(
                        v___x_6350_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                        v_intro_6346_,
                    );
                    lean_ctor_set_uint8(
                        v___x_6350_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 2) as u32,
                        v___x_6349_,
                    );
                    lean_ctor_set_uint8(
                        v___x_6350_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 3) as u32,
                        v_suggestions_6348_,
                    );
                    v___x_6351_ =
                        l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter(v___x_6350_);
                    return v___x_6351_;
                }
            }
            2 => {
                v___x_6364_ = 0;
                if v_isShared_6363_ == 0 {
                    v___x_6366_ = v___x_6362_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6373_ = lean_alloc_ctor(0, 1, (4) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6373_, 0, v_toApplyRulesConfig_6357_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_6373_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_backtracking_6358_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_6373_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 2) as u32,
                        v_constructor_6359_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_6373_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 3) as u32,
                        v_suggestions_6360_,
                    );
                    v___x_6366_ = v_reuseFailAlloc_6373_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_ctor_set_uint8(
                    v___x_6366_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                    v___x_6364_,
                );
                v___x_6367_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter(v___x_6366_);
                v_toApplyRulesConfig_6368_ = lean_ctor_get(v___x_6367_, 0);
                lean_inc_ref(v_toApplyRulesConfig_6368_);
                v_backtracking_6369_ = lean_ctor_get_uint8(
                    v___x_6367_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_intro_6370_ = lean_ctor_get_uint8(
                    v___x_6367_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                );
                v_constructor_6371_ = lean_ctor_get_uint8(
                    v___x_6367_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 2) as u32,
                );
                v_suggestions_6372_ = lean_ctor_get_uint8(
                    v___x_6367_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 3) as u32,
                );
                v___y_6343_ = v___x_6367_;
                v_toApplyRulesConfig_6344_ = v_toApplyRulesConfig_6368_;
                v_backtracking_6345_ = v_backtracking_6369_;
                v_intro_6346_ = v_intro_6370_;
                v_constructor_6347_ = v_constructor_6371_;
                v_suggestions_6348_ = v_suggestions_6372_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0(
    mut v_x_6375_: *mut LeanObject,
    mut v_x_6376_: *mut LeanObject,
    mut v___y_6377_: *mut LeanObject,
    mut v___y_6378_: *mut LeanObject,
    mut v___y_6379_: *mut LeanObject,
    mut v___y_6380_: *mut LeanObject,
    mut v___y_6381_: *mut LeanObject,
    mut v___y_6382_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_6386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6390_: u8 = 0;
    let mut v___x_6391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6400_: u8 = 0;
    let mut v___x_6402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6404_: u8 = 0;
    let mut v_isSharedCheck_6405_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6375_) == 0 {
                    v___x_6384_ = l_List_reverse___redArg(v_x_6376_);
                    v___x_6385_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6385_, 0, v___x_6384_);
                    return v___x_6385_;
                } else {
                    v_head_6386_ = lean_ctor_get(v_x_6375_, 0);
                    v_tail_6387_ = lean_ctor_get(v_x_6375_, 1);
                    v_isSharedCheck_6405_ = (!lean_is_exclusive(v_x_6375_)) as u8;
                    if v_isSharedCheck_6405_ == 0 {
                        v___x_6389_ = v_x_6375_;
                        v_isShared_6390_ = v_isSharedCheck_6405_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_6387_);
                        lean_inc(v_head_6386_);
                        lean_dec(v_x_6375_);
                        v___x_6389_ = lean_box(0);
                        v_isShared_6390_ = v_isSharedCheck_6405_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v___y_6382_);
                lean_inc_ref(v___y_6381_);
                lean_inc(v___y_6380_);
                lean_inc_ref(v___y_6379_);
                lean_inc(v___y_6378_);
                lean_inc_ref(v___y_6377_);
                v___x_6391_ = lean_apply_7(
                    v_head_6386_,
                    v___y_6377_,
                    v___y_6378_,
                    v___y_6379_,
                    v___y_6380_,
                    v___y_6381_,
                    v___y_6382_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_6391_) == 0 {
                    v_a_6392_ = lean_ctor_get(v___x_6391_, 0);
                    lean_inc(v_a_6392_);
                    lean_dec_ref_known(v___x_6391_, 1);
                    if v_isShared_6390_ == 0 {
                        lean_ctor_set(v___x_6389_, 1, v_x_6376_);
                        lean_ctor_set(v___x_6389_, 0, v_a_6392_);
                        v___x_6394_ = v___x_6389_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6396_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6396_, 0, v_a_6392_);
                        lean_ctor_set(v_reuseFailAlloc_6396_, 1, v_x_6376_);
                        v___x_6394_ = v_reuseFailAlloc_6396_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_6389_);
                    lean_dec(v_tail_6387_);
                    lean_dec(v_x_6376_);
                    v_a_6397_ = lean_ctor_get(v___x_6391_, 0);
                    v_isSharedCheck_6404_ = (!lean_is_exclusive(v___x_6391_)) as u8;
                    if v_isSharedCheck_6404_ == 0 {
                        v___x_6399_ = v___x_6391_;
                        v_isShared_6400_ = v_isSharedCheck_6404_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6397_);
                        lean_dec(v___x_6391_);
                        v___x_6399_ = lean_box(0);
                        v_isShared_6400_ = v_isSharedCheck_6404_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v_x_6375_ = v_tail_6387_;
                v_x_6376_ = v___x_6394_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_6400_ == 0 {
                    v___x_6402_ = v___x_6399_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6403_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6403_, 0, v_a_6397_);
                    v___x_6402_ = v_reuseFailAlloc_6403_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6402_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0___boxed(
    mut v_x_6406_: *mut LeanObject,
    mut v_x_6407_: *mut LeanObject,
    mut v___y_6408_: *mut LeanObject,
    mut v___y_6409_: *mut LeanObject,
    mut v___y_6410_: *mut LeanObject,
    mut v___y_6411_: *mut LeanObject,
    mut v___y_6412_: *mut LeanObject,
    mut v___y_6413_: *mut LeanObject,
    mut v___y_6414_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6415_: *mut LeanObject = core::ptr::null_mut();
    v_res_6415_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0(
        v_x_6406_,
        v_x_6407_,
        v___y_6408_,
        v___y_6409_,
        v___y_6410_,
        v___y_6411_,
        v___y_6412_,
        v___y_6413_,
    );
    lean_dec(v___y_6413_);
    lean_dec_ref(v___y_6412_);
    lean_dec(v___y_6411_);
    lean_dec_ref(v___y_6410_);
    lean_dec(v___y_6409_);
    lean_dec_ref(v___y_6408_);
    return v_res_6415_;
}
pub unsafe fn l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0(
    mut v_ctx_6416_: *mut LeanObject,
    mut v_cfg_6417_: *mut LeanObject,
    mut v_lemmas_6418_: *mut LeanObject,
    mut v___y_6419_: *mut LeanObject,
    mut v___y_6420_: *mut LeanObject,
    mut v___y_6421_: *mut LeanObject,
    mut v___y_6422_: *mut LeanObject,
    mut v___y_6423_: *mut LeanObject,
    mut v___y_6424_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6433_: u8 = 0;
    let mut v___x_6434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6438_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_6424_);
                lean_inc_ref(v___y_6423_);
                lean_inc(v___y_6422_);
                lean_inc_ref(v___y_6421_);
                lean_inc(v___y_6420_);
                lean_inc_ref(v___y_6419_);
                v___x_6426_ = lean_apply_8(
                    v_ctx_6416_,
                    v_cfg_6417_,
                    v___y_6419_,
                    v___y_6420_,
                    v___y_6421_,
                    v___y_6422_,
                    v___y_6423_,
                    v___y_6424_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_6426_) == 0 {
                    v_a_6427_ = lean_ctor_get(v___x_6426_, 0);
                    lean_inc(v_a_6427_);
                    lean_dec_ref_known(v___x_6426_, 1);
                    v___x_6428_ = lean_box(0);
                    v___x_6429_ =
                        l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0(
                            v_lemmas_6418_,
                            v___x_6428_,
                            v___y_6419_,
                            v___y_6420_,
                            v___y_6421_,
                            v___y_6422_,
                            v___y_6423_,
                            v___y_6424_,
                        );
                    lean_dec(v___y_6424_);
                    lean_dec_ref(v___y_6423_);
                    lean_dec(v___y_6422_);
                    lean_dec_ref(v___y_6421_);
                    lean_dec(v___y_6420_);
                    lean_dec_ref(v___y_6419_);
                    if lean_obj_tag(v___x_6429_) == 0 {
                        v_a_6430_ = lean_ctor_get(v___x_6429_, 0);
                        v_isSharedCheck_6438_ = (!lean_is_exclusive(v___x_6429_)) as u8;
                        if v_isSharedCheck_6438_ == 0 {
                            v___x_6432_ = v___x_6429_;
                            v_isShared_6433_ = v_isSharedCheck_6438_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_6430_);
                            lean_dec(v___x_6429_);
                            v___x_6432_ = lean_box(0);
                            v_isShared_6433_ = v_isSharedCheck_6438_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_6427_);
                        return v___x_6429_;
                    }
                } else {
                    lean_dec(v___y_6424_);
                    lean_dec_ref(v___y_6423_);
                    lean_dec(v___y_6422_);
                    lean_dec_ref(v___y_6421_);
                    lean_dec(v___y_6420_);
                    lean_dec_ref(v___y_6419_);
                    lean_dec(v_lemmas_6418_);
                    return v___x_6426_;
                }
            }
            1 => {
                v___x_6434_ = l_List_appendTR___redArg(v_a_6427_, v_a_6430_);
                if v_isShared_6433_ == 0 {
                    lean_ctor_set(v___x_6432_, 0, v___x_6434_);
                    v___x_6436_ = v___x_6432_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6437_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6437_, 0, v___x_6434_);
                    v___x_6436_ = v_reuseFailAlloc_6437_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6436_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0___boxed(
    mut v_ctx_6439_: *mut LeanObject,
    mut v_cfg_6440_: *mut LeanObject,
    mut v_lemmas_6441_: *mut LeanObject,
    mut v___y_6442_: *mut LeanObject,
    mut v___y_6443_: *mut LeanObject,
    mut v___y_6444_: *mut LeanObject,
    mut v___y_6445_: *mut LeanObject,
    mut v___y_6446_: *mut LeanObject,
    mut v___y_6447_: *mut LeanObject,
    mut v___y_6448_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6449_: *mut LeanObject = core::ptr::null_mut();
    v_res_6449_ = l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0(
        v_ctx_6439_,
        v_cfg_6440_,
        v_lemmas_6441_,
        v___y_6442_,
        v___y_6443_,
        v___y_6444_,
        v___y_6445_,
        v___y_6446_,
        v___y_6447_,
    );
    return v_res_6449_;
}
pub unsafe fn l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1(
    mut v_x_6450_: *mut LeanObject,
) -> u8 {
    let mut v___x_6451_: u8 = 0;
    v___x_6451_ = 0;
    return v___x_6451_;
}
pub unsafe fn l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1___boxed(
    mut v_x_6452_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6453_: u8 = 0;
    let mut v_r_6454_: *mut LeanObject = core::ptr::null_mut();
    v_res_6453_ = l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1(v_x_6452_);
    lean_dec(v_x_6452_);
    v_r_6454_ = lean_box((v_res_6453_) as usize);
    return v_r_6454_;
}
pub unsafe fn l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2(
    mut v___f_6455_: *mut LeanObject,
    mut v___x_6456_: *mut LeanObject,
    mut v___x_6457_: *mut LeanObject,
    mut v___y_6458_: *mut LeanObject,
    mut v___y_6459_: *mut LeanObject,
    mut v___y_6460_: *mut LeanObject,
    mut v___y_6461_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6467_: u8 = 0;
    let mut v_fst_6468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6472_: u8 = 0;
    let mut v_a_6473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6476_: u8 = 0;
    let mut v___x_6478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6480_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6463_ = l_Lean_Elab_Term_TermElabM_run___redArg(
                    v___f_6455_,
                    v___x_6456_,
                    v___x_6457_,
                    v___y_6458_,
                    v___y_6459_,
                    v___y_6460_,
                    v___y_6461_,
                );
                if lean_obj_tag(v___x_6463_) == 0 {
                    v_a_6464_ = lean_ctor_get(v___x_6463_, 0);
                    v_isSharedCheck_6472_ = (!lean_is_exclusive(v___x_6463_)) as u8;
                    if v_isSharedCheck_6472_ == 0 {
                        v___x_6466_ = v___x_6463_;
                        v_isShared_6467_ = v_isSharedCheck_6472_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6464_);
                        lean_dec(v___x_6463_);
                        v___x_6466_ = lean_box(0);
                        v_isShared_6467_ = v_isSharedCheck_6472_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6473_ = lean_ctor_get(v___x_6463_, 0);
                    v_isSharedCheck_6480_ = (!lean_is_exclusive(v___x_6463_)) as u8;
                    if v_isSharedCheck_6480_ == 0 {
                        v___x_6475_ = v___x_6463_;
                        v_isShared_6476_ = v_isSharedCheck_6480_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6473_);
                        lean_dec(v___x_6463_);
                        v___x_6475_ = lean_box(0);
                        v_isShared_6476_ = v_isSharedCheck_6480_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_6468_ = lean_ctor_get(v_a_6464_, 0);
                lean_inc(v_fst_6468_);
                lean_dec(v_a_6464_);
                if v_isShared_6467_ == 0 {
                    lean_ctor_set(v___x_6466_, 0, v_fst_6468_);
                    v___x_6470_ = v___x_6466_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6471_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6471_, 0, v_fst_6468_);
                    v___x_6470_ = v_reuseFailAlloc_6471_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6470_;
            }
            3 => {
                if v_isShared_6476_ == 0 {
                    v___x_6478_ = v___x_6475_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6479_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6479_, 0, v_a_6473_);
                    v___x_6478_ = v_reuseFailAlloc_6479_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6478_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2___boxed(
    mut v___f_6481_: *mut LeanObject,
    mut v___x_6482_: *mut LeanObject,
    mut v___x_6483_: *mut LeanObject,
    mut v___y_6484_: *mut LeanObject,
    mut v___y_6485_: *mut LeanObject,
    mut v___y_6486_: *mut LeanObject,
    mut v___y_6487_: *mut LeanObject,
    mut v___y_6488_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6489_: *mut LeanObject = core::ptr::null_mut();
    v_res_6489_ = l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2(
        v___f_6481_,
        v___x_6482_,
        v___x_6483_,
        v___y_6484_,
        v___y_6485_,
        v___y_6486_,
        v___y_6487_,
    );
    lean_dec(v___y_6487_);
    lean_dec_ref(v___y_6486_);
    lean_dec(v___y_6485_);
    lean_dec_ref(v___y_6484_);
    return v_res_6489_;
}
pub unsafe fn l_Lean_Meta_SolveByElim_elabContextLemmas(
    mut v_cfg_6504_: *mut LeanObject,
    mut v_g_6505_: *mut LeanObject,
    mut v_lemmas_6506_: *mut LeanObject,
    mut v_ctx_6507_: *mut LeanObject,
    mut v_a_6508_: *mut LeanObject,
    mut v_a_6509_: *mut LeanObject,
    mut v_a_6510_: *mut LeanObject,
    mut v_a_6511_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6517_: *mut LeanObject = core::ptr::null_mut();
    v___f_6513_ = lean_alloc_closure(
        l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0___boxed as *mut core::ffi::c_void,
        10,
        3,
    );
    lean_closure_set(v___f_6513_, 0, v_ctx_6507_);
    lean_closure_set(v___f_6513_, 1, v_cfg_6504_);
    lean_closure_set(v___f_6513_, 2, v_lemmas_6506_);
    v___x_6514_ = l_Lean_Meta_SolveByElim_elabContextLemmas___closed__2;
    v___x_6515_ = l_Lean_Meta_SolveByElim_elabContextLemmas___closed__3;
    v___f_6516_ = lean_alloc_closure(
        l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    lean_closure_set(v___f_6516_, 0, v___f_6513_);
    lean_closure_set(v___f_6516_, 1, v___x_6514_);
    lean_closure_set(v___f_6516_, 2, v___x_6515_);
    v___x_6517_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_g_6505_, v___f_6516_, v_a_6508_, v_a_6509_, v_a_6510_, v_a_6511_);
    return v___x_6517_;
}
pub unsafe fn l_Lean_Meta_SolveByElim_elabContextLemmas___boxed(
    mut v_cfg_6518_: *mut LeanObject,
    mut v_g_6519_: *mut LeanObject,
    mut v_lemmas_6520_: *mut LeanObject,
    mut v_ctx_6521_: *mut LeanObject,
    mut v_a_6522_: *mut LeanObject,
    mut v_a_6523_: *mut LeanObject,
    mut v_a_6524_: *mut LeanObject,
    mut v_a_6525_: *mut LeanObject,
    mut v_a_6526_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6527_: *mut LeanObject = core::ptr::null_mut();
    v_res_6527_ = l_Lean_Meta_SolveByElim_elabContextLemmas(
        v_cfg_6518_,
        v_g_6519_,
        v_lemmas_6520_,
        v_ctx_6521_,
        v_a_6522_,
        v_a_6523_,
        v_a_6524_,
        v_a_6525_,
    );
    lean_dec(v_a_6525_);
    lean_dec_ref(v_a_6524_);
    lean_dec(v_a_6523_);
    lean_dec_ref(v_a_6522_);
    return v_res_6527_;
}
pub unsafe fn l_Lean_Meta_SolveByElim_applyLemmas(
    mut v_cfg_6528_: *mut LeanObject,
    mut v_lemmas_6529_: *mut LeanObject,
    mut v_ctx_6530_: *mut LeanObject,
    mut v_g_6531_: *mut LeanObject,
    mut v_a_6532_: *mut LeanObject,
    mut v_a_6533_: *mut LeanObject,
    mut v_a_6534_: *mut LeanObject,
    mut v_a_6535_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplyRulesConfig_6538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplyConfig_6540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_transparency_6541_: u8 = 0;
    let mut v___x_6542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6546_: u8 = 0;
    let mut v___x_6548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6550_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_g_6531_);
                lean_inc_ref(v_cfg_6528_);
                v___x_6537_ = l_Lean_Meta_SolveByElim_elabContextLemmas(
                    v_cfg_6528_,
                    v_g_6531_,
                    v_lemmas_6529_,
                    v_ctx_6530_,
                    v_a_6532_,
                    v_a_6533_,
                    v_a_6534_,
                    v_a_6535_,
                );
                if lean_obj_tag(v___x_6537_) == 0 {
                    v_toApplyRulesConfig_6538_ = lean_ctor_get(v_cfg_6528_, 0);
                    lean_inc_ref(v_toApplyRulesConfig_6538_);
                    lean_dec_ref(v_cfg_6528_);
                    v_a_6539_ = lean_ctor_get(v___x_6537_, 0);
                    lean_inc(v_a_6539_);
                    lean_dec_ref_known(v___x_6537_, 1);
                    v_toApplyConfig_6540_ = lean_ctor_get(v_toApplyRulesConfig_6538_, 1);
                    lean_inc_ref(v_toApplyConfig_6540_);
                    v_transparency_6541_ = lean_ctor_get_uint8(
                        v_toApplyRulesConfig_6538_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    lean_dec_ref(v_toApplyRulesConfig_6538_);
                    v___x_6542_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(
                        v_toApplyConfig_6540_,
                        v_transparency_6541_,
                        v_a_6539_,
                        v_g_6531_,
                        v_a_6533_,
                        v_a_6535_,
                    );
                    return v___x_6542_;
                } else {
                    lean_dec(v_g_6531_);
                    lean_dec_ref(v_cfg_6528_);
                    v_a_6543_ = lean_ctor_get(v___x_6537_, 0);
                    v_isSharedCheck_6550_ = (!lean_is_exclusive(v___x_6537_)) as u8;
                    if v_isSharedCheck_6550_ == 0 {
                        v___x_6545_ = v___x_6537_;
                        v_isShared_6546_ = v_isSharedCheck_6550_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6543_);
                        lean_dec(v___x_6537_);
                        v___x_6545_ = lean_box(0);
                        v_isShared_6546_ = v_isSharedCheck_6550_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6546_ == 0 {
                    v___x_6548_ = v___x_6545_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6549_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6549_, 0, v_a_6543_);
                    v___x_6548_ = v_reuseFailAlloc_6549_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6548_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_SolveByElim_applyLemmas___boxed(
    mut v_cfg_6551_: *mut LeanObject,
    mut v_lemmas_6552_: *mut LeanObject,
    mut v_ctx_6553_: *mut LeanObject,
    mut v_g_6554_: *mut LeanObject,
    mut v_a_6555_: *mut LeanObject,
    mut v_a_6556_: *mut LeanObject,
    mut v_a_6557_: *mut LeanObject,
    mut v_a_6558_: *mut LeanObject,
    mut v_a_6559_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6560_: *mut LeanObject = core::ptr::null_mut();
    v_res_6560_ = l_Lean_Meta_SolveByElim_applyLemmas(
        v_cfg_6551_,
        v_lemmas_6552_,
        v_ctx_6553_,
        v_g_6554_,
        v_a_6555_,
        v_a_6556_,
        v_a_6557_,
        v_a_6558_,
    );
    lean_dec(v_a_6558_);
    lean_dec_ref(v_a_6557_);
    lean_dec(v_a_6556_);
    lean_dec_ref(v_a_6555_);
    return v_res_6560_;
}
pub unsafe fn l_Lean_Meta_SolveByElim_applyFirstLemma(
    mut v_cfg_6561_: *mut LeanObject,
    mut v_lemmas_6562_: *mut LeanObject,
    mut v_ctx_6563_: *mut LeanObject,
    mut v_g_6564_: *mut LeanObject,
    mut v_a_6565_: *mut LeanObject,
    mut v_a_6566_: *mut LeanObject,
    mut v_a_6567_: *mut LeanObject,
    mut v_a_6568_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplyRulesConfig_6571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplyConfig_6573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_transparency_6574_: u8 = 0;
    let mut v___x_6575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6579_: u8 = 0;
    let mut v___x_6581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6583_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_g_6564_);
                lean_inc_ref(v_cfg_6561_);
                v___x_6570_ = l_Lean_Meta_SolveByElim_elabContextLemmas(
                    v_cfg_6561_,
                    v_g_6564_,
                    v_lemmas_6562_,
                    v_ctx_6563_,
                    v_a_6565_,
                    v_a_6566_,
                    v_a_6567_,
                    v_a_6568_,
                );
                if lean_obj_tag(v___x_6570_) == 0 {
                    v_toApplyRulesConfig_6571_ = lean_ctor_get(v_cfg_6561_, 0);
                    lean_inc_ref(v_toApplyRulesConfig_6571_);
                    lean_dec_ref(v_cfg_6561_);
                    v_a_6572_ = lean_ctor_get(v___x_6570_, 0);
                    lean_inc(v_a_6572_);
                    lean_dec_ref_known(v___x_6570_, 1);
                    v_toApplyConfig_6573_ = lean_ctor_get(v_toApplyRulesConfig_6571_, 1);
                    lean_inc_ref(v_toApplyConfig_6573_);
                    v_transparency_6574_ = lean_ctor_get_uint8(
                        v_toApplyRulesConfig_6571_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    lean_dec_ref(v_toApplyRulesConfig_6571_);
                    v___x_6575_ = l_Lean_Meta_SolveByElim_applyFirst(
                        v_toApplyConfig_6573_,
                        v_transparency_6574_,
                        v_a_6572_,
                        v_g_6564_,
                        v_a_6565_,
                        v_a_6566_,
                        v_a_6567_,
                        v_a_6568_,
                    );
                    return v___x_6575_;
                } else {
                    lean_dec(v_g_6564_);
                    lean_dec_ref(v_cfg_6561_);
                    v_a_6576_ = lean_ctor_get(v___x_6570_, 0);
                    v_isSharedCheck_6583_ = (!lean_is_exclusive(v___x_6570_)) as u8;
                    if v_isSharedCheck_6583_ == 0 {
                        v___x_6578_ = v___x_6570_;
                        v_isShared_6579_ = v_isSharedCheck_6583_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6576_);
                        lean_dec(v___x_6570_);
                        v___x_6578_ = lean_box(0);
                        v_isShared_6579_ = v_isSharedCheck_6583_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6579_ == 0 {
                    v___x_6581_ = v___x_6578_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6582_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6582_, 0, v_a_6576_);
                    v___x_6581_ = v_reuseFailAlloc_6582_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6581_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_SolveByElim_applyFirstLemma___boxed(
    mut v_cfg_6584_: *mut LeanObject,
    mut v_lemmas_6585_: *mut LeanObject,
    mut v_ctx_6586_: *mut LeanObject,
    mut v_g_6587_: *mut LeanObject,
    mut v_a_6588_: *mut LeanObject,
    mut v_a_6589_: *mut LeanObject,
    mut v_a_6590_: *mut LeanObject,
    mut v_a_6591_: *mut LeanObject,
    mut v_a_6592_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6593_: *mut LeanObject = core::ptr::null_mut();
    v_res_6593_ = l_Lean_Meta_SolveByElim_applyFirstLemma(
        v_cfg_6584_,
        v_lemmas_6585_,
        v_ctx_6586_,
        v_g_6587_,
        v_a_6588_,
        v_a_6589_,
        v_a_6590_,
        v_a_6591_,
    );
    lean_dec(v_a_6591_);
    lean_dec_ref(v_a_6590_);
    lean_dec(v_a_6589_);
    lean_dec_ref(v_a_6588_);
    return v_res_6593_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(
    mut v_keys_6594_: *mut LeanObject,
    mut v_i_6595_: *mut LeanObject,
    mut v_k_6596_: *mut LeanObject,
) -> u8 {
    let mut v___x_6597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6598_: u8 = 0;
    let mut v_k_x27_6599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6600_: u8 = 0;
    let mut v___x_6601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6602_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6597_ = lean_array_get_size(v_keys_6594_);
                v___x_6598_ = lean_nat_dec_lt(v_i_6595_, v___x_6597_);
                if v___x_6598_ == 0 {
                    lean_dec(v_i_6595_);
                    return v___x_6598_;
                } else {
                    v_k_x27_6599_ = lean_array_fget_borrowed(v_keys_6594_, v_i_6595_);
                    v___x_6600_ = l_Lean_instBEqMVarId_beq(v_k_6596_, v_k_x27_6599_);
                    if v___x_6600_ == 0 {
                        v___x_6601_ = lean_unsigned_to_nat(1);
                        v___x_6602_ = lean_nat_add(v_i_6595_, v___x_6601_);
                        lean_dec(v_i_6595_);
                        v_i_6595_ = v___x_6602_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_i_6595_);
                        return v___x_6600_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg___boxed(
    mut v_keys_6604_: *mut LeanObject,
    mut v_i_6605_: *mut LeanObject,
    mut v_k_6606_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6607_: u8 = 0;
    let mut v_r_6608_: *mut LeanObject = core::ptr::null_mut();
    v_res_6607_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(v_keys_6604_, v_i_6605_, v_k_6606_);
    lean_dec(v_k_6606_);
    lean_dec_ref(v_keys_6604_);
    v_r_6608_ = lean_box((v_res_6607_) as usize);
    return v_r_6608_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(
    mut v_x_6609_: *mut LeanObject,
    mut v_x_6610_: usize,
    mut v_x_6611_: *mut LeanObject,
) -> u8 {
    let mut v_es_6612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6614_: usize = 0;
    let mut v___x_6615_: usize = 0;
    let mut v___x_6616_: usize = 0;
    let mut v_j_6617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_6619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6620_: u8 = 0;
    let mut v_node_6621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6622_: usize = 0;
    let mut v___x_6624_: u8 = 0;
    let mut v_ks_6625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6627_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6609_) == 0 {
                    v_es_6612_ = lean_ctor_get(v_x_6609_, 0);
                    v___x_6613_ = lean_box(2);
                    v___x_6614_ = 5usize;
                    v___x_6615_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__1);
                    v___x_6616_ = lean_usize_land(v_x_6610_, v___x_6615_);
                    v_j_6617_ = lean_usize_to_nat(v___x_6616_);
                    v___x_6618_ = lean_array_get_borrowed(v___x_6613_, v_es_6612_, v_j_6617_);
                    lean_dec(v_j_6617_);
                    match lean_obj_tag(v___x_6618_) {
                        0 => {
                            v_key_6619_ = lean_ctor_get(v___x_6618_, 0);
                            v___x_6620_ = l_Lean_instBEqMVarId_beq(v_x_6611_, v_key_6619_);
                            return v___x_6620_;
                        }
                        1 => {
                            v_node_6621_ = lean_ctor_get(v___x_6618_, 0);
                            v___x_6622_ = lean_usize_shift_right(v_x_6610_, v___x_6614_);
                            v_x_6609_ = v_node_6621_;
                            v_x_6610_ = v___x_6622_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_6624_ = 0;
                            return v___x_6624_;
                        }
                    }
                } else {
                    v_ks_6625_ = lean_ctor_get(v_x_6609_, 0);
                    v___x_6626_ = lean_unsigned_to_nat(0);
                    v___x_6627_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(v_ks_6625_, v___x_6626_, v_x_6611_);
                    return v___x_6627_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg___boxed(
    mut v_x_6628_: *mut LeanObject,
    mut v_x_6629_: *mut LeanObject,
    mut v_x_6630_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_2218__boxed_6631_: usize = 0;
    let mut v_res_6632_: u8 = 0;
    let mut v_r_6633_: *mut LeanObject = core::ptr::null_mut();
    v_x_2218__boxed_6631_ = lean_unbox_usize(v_x_6629_);
    lean_dec(v_x_6629_);
    v_res_6632_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_6628_, v_x_2218__boxed_6631_, v_x_6630_);
    lean_dec(v_x_6630_);
    lean_dec_ref(v_x_6628_);
    v_r_6633_ = lean_box((v_res_6632_) as usize);
    return v_r_6633_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(
    mut v_x_6634_: *mut LeanObject,
    mut v_x_6635_: *mut LeanObject,
) -> u8 {
    let mut v___x_6636_: u64 = 0;
    let mut v___x_6637_: usize = 0;
    let mut v___x_6638_: u8 = 0;
    v___x_6636_ = l_Lean_instHashableMVarId_hash(v_x_6635_);
    v___x_6637_ = lean_uint64_to_usize(v___x_6636_);
    v___x_6638_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_6634_, v___x_6637_, v_x_6635_);
    return v___x_6638_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg___boxed(
    mut v_x_6639_: *mut LeanObject,
    mut v_x_6640_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6641_: u8 = 0;
    let mut v_r_6642_: *mut LeanObject = core::ptr::null_mut();
    v_res_6641_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(v_x_6639_, v_x_6640_);
    lean_dec(v_x_6640_);
    lean_dec_ref(v_x_6639_);
    v_r_6642_ = lean_box((v_res_6641_) as usize);
    return v_r_6642_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(
    mut v_mvarId_6643_: *mut LeanObject,
    mut v___y_6644_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_6647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_6648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6649_: u8 = 0;
    let mut v___x_6650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6651_: *mut LeanObject = core::ptr::null_mut();
    v___x_6646_ = lean_st_ref_get(v___y_6644_);
    v_mctx_6647_ = lean_ctor_get(v___x_6646_, 0);
    lean_inc_ref(v_mctx_6647_);
    lean_dec(v___x_6646_);
    v_eAssignment_6648_ = lean_ctor_get(v_mctx_6647_, 8);
    lean_inc_ref(v_eAssignment_6648_);
    lean_dec_ref(v_mctx_6647_);
    v___x_6649_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(v_eAssignment_6648_, v_mvarId_6643_);
    lean_dec_ref(v_eAssignment_6648_);
    v___x_6650_ = lean_box((v___x_6649_) as usize);
    v___x_6651_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_6651_, 0, v___x_6650_);
    return v___x_6651_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_mvarId_6652_: *mut LeanObject,
    mut v___y_6653_: *mut LeanObject,
    mut v___y_6654_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6655_: *mut LeanObject = core::ptr::null_mut();
    v_res_6655_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v_mvarId_6652_, v___y_6653_);
    lean_dec(v___y_6653_);
    lean_dec(v_mvarId_6652_);
    return v_res_6655_;
}
pub unsafe fn l_List_foldl___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1_spec__2(
    mut v_x_6656_: *mut LeanObject,
    mut v_x_6657_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_6658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6660_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6657_) == 0 {
                    return v_x_6656_;
                } else {
                    v_head_6658_ = lean_ctor_get(v_x_6657_, 0);
                    lean_inc(v_head_6658_);
                    v_tail_6659_ = lean_ctor_get(v_x_6657_, 1);
                    lean_inc(v_tail_6659_);
                    lean_dec_ref_known(v_x_6657_, 2);
                    v___x_6660_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(
                        v_x_6656_,
                        v_head_6658_,
                    );
                    v_x_6656_ = v___x_6660_;
                    v_x_6657_ = v_tail_6659_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1(
    mut v_f_6662_: *mut LeanObject,
    mut v_a_6663_: *mut LeanObject,
    mut v_a_6664_: u8,
    mut v_a_6665_: *mut LeanObject,
    mut v_a_6666_: *mut LeanObject,
    mut v_a_6667_: *mut LeanObject,
    mut v___y_6668_: *mut LeanObject,
    mut v___y_6669_: *mut LeanObject,
    mut v___y_6670_: *mut LeanObject,
    mut v___y_6671_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_6676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_6679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6683_: u8 = 0;
    let mut v___x_6684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6688_: u8 = 0;
    let mut v___x_6689_: u8 = 0;
    let mut v_zero_6690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_6691_: u8 = 0;
    let mut v___x_6692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_6703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_6704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6708_: u8 = 0;
    let mut v___x_6710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6716_: u8 = 0;
    let mut v___x_6718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6720_: u8 = 0;
    let mut v_isSharedCheck_6722_: u8 = 0;
    let mut v_isSharedCheck_6723_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_6665_) == 0 {
                    if lean_obj_tag(v_a_6666_) == 0 {
                        lean_dec(v_a_6663_);
                        lean_dec_ref(v_f_6662_);
                        v___x_6673_ = lean_box((v_a_6664_) as usize);
                        v___x_6674_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_6674_, 0, v___x_6673_);
                        lean_ctor_set(v___x_6674_, 1, v_a_6667_);
                        v___x_6675_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_6675_, 0, v___x_6674_);
                        return v___x_6675_;
                    } else {
                        v_head_6676_ = lean_ctor_get(v_a_6666_, 0);
                        lean_inc(v_head_6676_);
                        v_tail_6677_ = lean_ctor_get(v_a_6666_, 1);
                        lean_inc(v_tail_6677_);
                        lean_dec_ref_known(v_a_6666_, 2);
                        v_a_6665_ = v_head_6676_;
                        v_a_6666_ = v_tail_6677_;
                        state = 0;
                        continue;
                    }
                } else {
                    v_head_6679_ = lean_ctor_get(v_a_6665_, 0);
                    v_tail_6680_ = lean_ctor_get(v_a_6665_, 1);
                    v_isSharedCheck_6723_ = (!lean_is_exclusive(v_a_6665_)) as u8;
                    if v_isSharedCheck_6723_ == 0 {
                        v___x_6682_ = v_a_6665_;
                        v_isShared_6683_ = v_isSharedCheck_6723_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_6680_);
                        lean_inc(v_head_6679_);
                        lean_dec(v_a_6665_);
                        v___x_6682_ = lean_box(0);
                        v_isShared_6683_ = v_isSharedCheck_6723_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6684_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v_head_6679_, v___y_6669_);
                v_a_6685_ = lean_ctor_get(v___x_6684_, 0);
                v_isSharedCheck_6722_ = (!lean_is_exclusive(v___x_6684_)) as u8;
                if v_isSharedCheck_6722_ == 0 {
                    v___x_6687_ = v___x_6684_;
                    v_isShared_6688_ = v_isSharedCheck_6722_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_a_6685_);
                    lean_dec(v___x_6684_);
                    v___x_6687_ = lean_box(0);
                    v_isShared_6688_ = v_isSharedCheck_6722_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6689_ = (lean_unbox(v_a_6685_) as u8);
                lean_dec(v_a_6685_);
                if v___x_6689_ == 0 {
                    v_zero_6690_ = lean_unsigned_to_nat(0);
                    v_isZero_6691_ = lean_nat_dec_eq(v_a_6663_, v_zero_6690_);
                    if v_isZero_6691_ == 1 {
                        lean_del_object(v___x_6682_);
                        lean_dec(v_a_6663_);
                        lean_dec_ref(v_f_6662_);
                        v___x_6692_ = lean_array_push(v_a_6667_, v_head_6679_);
                        v___x_6693_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(
                            v___x_6692_,
                            v_tail_6680_,
                        );
                        v___x_6694_ = l_List_foldl___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1_spec__2(v___x_6693_, v_a_6666_);
                        v___x_6695_ = lean_box((v_a_6664_) as usize);
                        v___x_6696_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_6696_, 0, v___x_6695_);
                        lean_ctor_set(v___x_6696_, 1, v___x_6694_);
                        if v_isShared_6688_ == 0 {
                            lean_ctor_set(v___x_6687_, 0, v___x_6696_);
                            v___x_6698_ = v___x_6687_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_6699_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_6699_, 0, v___x_6696_);
                            v___x_6698_ = v_reuseFailAlloc_6699_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_6687_);
                        lean_inc_ref(v_f_6662_);
                        lean_inc(v_head_6679_);
                        v___x_6700_ = lean_apply_1(v_f_6662_, v_head_6679_);
                        v___x_6701_ = l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg(v___x_6700_, v___y_6668_, v___y_6669_, v___y_6670_, v___y_6671_);
                        if lean_obj_tag(v___x_6701_) == 0 {
                            v_a_6702_ = lean_ctor_get(v___x_6701_, 0);
                            lean_inc(v_a_6702_);
                            lean_dec_ref_known(v___x_6701_, 1);
                            v_one_6703_ = lean_unsigned_to_nat(1);
                            v_n_6704_ = lean_nat_sub(v_a_6663_, v_one_6703_);
                            lean_dec(v_a_6663_);
                            if lean_obj_tag(v_a_6702_) == 0 {
                                lean_del_object(v___x_6682_);
                                v___x_6705_ = lean_array_push(v_a_6667_, v_head_6679_);
                                v_a_6663_ = v_n_6704_;
                                v_a_6665_ = v_tail_6680_;
                                v_a_6667_ = v___x_6705_;
                                state = 0;
                                continue;
                            } else {
                                lean_dec(v_head_6679_);
                                v_val_6707_ = lean_ctor_get(v_a_6702_, 0);
                                lean_inc(v_val_6707_);
                                lean_dec_ref_known(v_a_6702_, 1);
                                v___x_6708_ = 1;
                                if v_isShared_6683_ == 0 {
                                    lean_ctor_set(v___x_6682_, 1, v_a_6666_);
                                    lean_ctor_set(v___x_6682_, 0, v_tail_6680_);
                                    v___x_6710_ = v___x_6682_;
                                    state = 4;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_6712_ = lean_alloc_ctor(1, 2, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_6712_, 0, v_tail_6680_);
                                    lean_ctor_set(v_reuseFailAlloc_6712_, 1, v_a_6666_);
                                    v___x_6710_ = v_reuseFailAlloc_6712_;
                                    state = 4;
                                    continue;
                                }
                            }
                        } else {
                            lean_del_object(v___x_6682_);
                            lean_dec(v_tail_6680_);
                            lean_dec(v_head_6679_);
                            lean_dec_ref(v_a_6667_);
                            lean_dec(v_a_6666_);
                            lean_dec(v_a_6663_);
                            lean_dec_ref(v_f_6662_);
                            v_a_6713_ = lean_ctor_get(v___x_6701_, 0);
                            v_isSharedCheck_6720_ = (!lean_is_exclusive(v___x_6701_)) as u8;
                            if v_isSharedCheck_6720_ == 0 {
                                v___x_6715_ = v___x_6701_;
                                v_isShared_6716_ = v_isSharedCheck_6720_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_6713_);
                                lean_dec(v___x_6701_);
                                v___x_6715_ = lean_box(0);
                                v_isShared_6716_ = v_isSharedCheck_6720_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_del_object(v___x_6687_);
                    lean_del_object(v___x_6682_);
                    lean_dec(v_head_6679_);
                    v_a_6665_ = v_tail_6680_;
                    state = 0;
                    continue;
                }
            }
            3 => {
                return v___x_6698_;
            }
            4 => {
                v_a_6663_ = v_n_6704_;
                v_a_6664_ = v___x_6708_;
                v_a_6665_ = v_val_6707_;
                v_a_6666_ = v___x_6710_;
                state = 0;
                continue;
            }
            5 => {
                if v_isShared_6716_ == 0 {
                    v___x_6718_ = v___x_6715_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6719_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6719_, 0, v_a_6713_);
                    v___x_6718_ = v_reuseFailAlloc_6719_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6718_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1___boxed(
    mut v_f_6724_: *mut LeanObject,
    mut v_a_6725_: *mut LeanObject,
    mut v_a_6726_: *mut LeanObject,
    mut v_a_6727_: *mut LeanObject,
    mut v_a_6728_: *mut LeanObject,
    mut v_a_6729_: *mut LeanObject,
    mut v___y_6730_: *mut LeanObject,
    mut v___y_6731_: *mut LeanObject,
    mut v___y_6732_: *mut LeanObject,
    mut v___y_6733_: *mut LeanObject,
    mut v___y_6734_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2299__boxed_6735_: u8 = 0;
    let mut v_res_6736_: *mut LeanObject = core::ptr::null_mut();
    v_a_2299__boxed_6735_ = (lean_unbox(v_a_6726_) as u8);
    v_res_6736_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1(v_f_6724_, v_a_6725_, v_a_2299__boxed_6735_, v_a_6727_, v_a_6728_, v_a_6729_, v___y_6730_, v___y_6731_, v___y_6732_, v___y_6733_);
    lean_dec(v___y_6733_);
    lean_dec_ref(v___y_6732_);
    lean_dec(v___y_6731_);
    lean_dec_ref(v___y_6730_);
    return v_res_6736_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(
    mut v_as_6737_: *mut LeanObject,
    mut v_i_6738_: usize,
    mut v_stop_6739_: usize,
    mut v_b_6740_: *mut LeanObject,
    mut v___y_6741_: *mut LeanObject,
    mut v___y_6742_: *mut LeanObject,
    mut v___y_6743_: *mut LeanObject,
    mut v___y_6744_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_6747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6748_: usize = 0;
    let mut v___x_6749_: usize = 0;
    let mut v___x_6751_: u8 = 0;
    let mut v___x_6752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6757_: u8 = 0;
    let mut v_a_6758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6759_: u8 = 0;
    let mut v_a_6760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6763_: u8 = 0;
    let mut v___x_6765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6767_: u8 = 0;
    let mut v___x_6768_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6751_ = lean_usize_dec_eq(v_i_6738_, v_stop_6739_);
                if v___x_6751_ == 0 {
                    v___x_6752_ = lean_array_uget_borrowed(v_as_6737_, v_i_6738_);
                    v___x_6755_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v___x_6752_, v___y_6742_);
                    if lean_obj_tag(v___x_6755_) == 0 {
                        v_a_6756_ = lean_ctor_get(v___x_6755_, 0);
                        lean_inc(v_a_6756_);
                        lean_dec_ref_known(v___x_6755_, 1);
                        v___x_6757_ = (lean_unbox(v_a_6756_) as u8);
                        lean_dec(v_a_6756_);
                        if v___x_6757_ == 0 {
                            state = 2;
                            continue;
                        } else {
                            v_a_6747_ = v_b_6740_;
                            state = 1;
                            continue;
                        }
                    } else {
                        if lean_obj_tag(v___x_6755_) == 0 {
                            v_a_6758_ = lean_ctor_get(v___x_6755_, 0);
                            lean_inc(v_a_6758_);
                            lean_dec_ref_known(v___x_6755_, 1);
                            v___x_6759_ = (lean_unbox(v_a_6758_) as u8);
                            lean_dec(v_a_6758_);
                            if v___x_6759_ == 0 {
                                v_a_6747_ = v_b_6740_;
                                state = 1;
                                continue;
                            } else {
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v_b_6740_);
                            v_a_6760_ = lean_ctor_get(v___x_6755_, 0);
                            v_isSharedCheck_6767_ = (!lean_is_exclusive(v___x_6755_)) as u8;
                            if v_isSharedCheck_6767_ == 0 {
                                v___x_6762_ = v___x_6755_;
                                v_isShared_6763_ = v_isSharedCheck_6767_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_6760_);
                                lean_dec(v___x_6755_);
                                v___x_6762_ = lean_box(0);
                                v_isShared_6763_ = v_isSharedCheck_6767_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                } else {
                    v___x_6768_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6768_, 0, v_b_6740_);
                    return v___x_6768_;
                }
            }
            1 => {
                v___x_6748_ = 1usize;
                v___x_6749_ = lean_usize_add(v_i_6738_, v___x_6748_);
                v_i_6738_ = v___x_6749_;
                v_b_6740_ = v_a_6747_;
                state = 0;
                continue;
            }
            2 => {
                lean_inc(v___x_6752_);
                v___x_6754_ = lean_array_push(v_b_6740_, v___x_6752_);
                v_a_6747_ = v___x_6754_;
                state = 1;
                continue;
            }
            3 => {
                if v_isShared_6763_ == 0 {
                    v___x_6765_ = v___x_6762_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6766_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6766_, 0, v_a_6760_);
                    v___x_6765_ = v_reuseFailAlloc_6766_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6765_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3___boxed(
    mut v_as_6769_: *mut LeanObject,
    mut v_i_6770_: *mut LeanObject,
    mut v_stop_6771_: *mut LeanObject,
    mut v_b_6772_: *mut LeanObject,
    mut v___y_6773_: *mut LeanObject,
    mut v___y_6774_: *mut LeanObject,
    mut v___y_6775_: *mut LeanObject,
    mut v___y_6776_: *mut LeanObject,
    mut v___y_6777_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_6778_: usize = 0;
    let mut v_stop_boxed_6779_: usize = 0;
    let mut v_res_6780_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_6778_ = lean_unbox_usize(v_i_6770_);
    lean_dec(v_i_6770_);
    v_stop_boxed_6779_ = lean_unbox_usize(v_stop_6771_);
    lean_dec(v_stop_6771_);
    v_res_6780_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(v_as_6769_, v_i_boxed_6778_, v_stop_boxed_6779_, v_b_6772_, v___y_6773_, v___y_6774_, v___y_6775_, v___y_6776_);
    lean_dec(v___y_6776_);
    lean_dec_ref(v___y_6775_);
    lean_dec(v___y_6774_);
    lean_dec_ref(v___y_6773_);
    lean_dec_ref(v_as_6769_);
    return v_res_6780_;
}
pub unsafe fn _init_l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1()
-> *mut LeanObject {
    let mut v___x_6783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6784_: *mut LeanObject = core::ptr::null_mut();
    v___x_6783_ = l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__0;
    v___x_6784_ = lean_array_to_list(v___x_6783_);
    return v___x_6784_;
}
pub unsafe fn l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0(
    mut v_f_6785_: *mut LeanObject,
    mut v_goals_6786_: *mut LeanObject,
    mut v_maxIters_6787_: *mut LeanObject,
    mut v___y_6788_: *mut LeanObject,
    mut v___y_6789_: *mut LeanObject,
    mut v___y_6790_: *mut LeanObject,
    mut v___y_6791_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6793_: u8 = 0;
    let mut v___x_6794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6801_: u8 = 0;
    let mut v_fst_6802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6806_: u8 = 0;
    let mut v_____do__lift_6808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6817_: u8 = 0;
    let mut v___x_6818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6821_: u8 = 0;
    let mut v___x_6822_: usize = 0;
    let mut v___x_6823_: usize = 0;
    let mut v___x_6824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6829_: u8 = 0;
    let mut v___x_6831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6833_: u8 = 0;
    let mut v___x_6834_: usize = 0;
    let mut v___x_6835_: usize = 0;
    let mut v___x_6836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6841_: u8 = 0;
    let mut v___x_6843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6845_: u8 = 0;
    let mut v_isSharedCheck_6846_: u8 = 0;
    let mut v_isSharedCheck_6847_: u8 = 0;
    let mut v_a_6848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6851_: u8 = 0;
    let mut v___x_6853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6855_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6793_ = 0;
                v___x_6794_ = lean_box(0);
                v___x_6795_ = lean_unsigned_to_nat(0);
                v___x_6796_ = l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__0;
                v___x_6797_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1(v_f_6785_, v_maxIters_6787_, v___x_6793_, v_goals_6786_, v___x_6794_, v___x_6796_, v___y_6788_, v___y_6789_, v___y_6790_, v___y_6791_);
                if lean_obj_tag(v___x_6797_) == 0 {
                    v_a_6798_ = lean_ctor_get(v___x_6797_, 0);
                    v_isSharedCheck_6847_ = (!lean_is_exclusive(v___x_6797_)) as u8;
                    if v_isSharedCheck_6847_ == 0 {
                        v___x_6800_ = v___x_6797_;
                        v_isShared_6801_ = v_isSharedCheck_6847_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6798_);
                        lean_dec(v___x_6797_);
                        v___x_6800_ = lean_box(0);
                        v_isShared_6801_ = v_isSharedCheck_6847_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6848_ = lean_ctor_get(v___x_6797_, 0);
                    v_isSharedCheck_6855_ = (!lean_is_exclusive(v___x_6797_)) as u8;
                    if v_isSharedCheck_6855_ == 0 {
                        v___x_6850_ = v___x_6797_;
                        v_isShared_6851_ = v_isSharedCheck_6855_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_6848_);
                        lean_dec(v___x_6797_);
                        v___x_6850_ = lean_box(0);
                        v_isShared_6851_ = v_isSharedCheck_6855_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_6802_ = lean_ctor_get(v_a_6798_, 0);
                v_snd_6803_ = lean_ctor_get(v_a_6798_, 1);
                v_isSharedCheck_6846_ = (!lean_is_exclusive(v_a_6798_)) as u8;
                if v_isSharedCheck_6846_ == 0 {
                    v___x_6805_ = v_a_6798_;
                    v_isShared_6806_ = v_isSharedCheck_6846_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_6803_);
                    lean_inc(v_fst_6802_);
                    lean_dec(v_a_6798_);
                    v___x_6805_ = lean_box(0);
                    v_isShared_6806_ = v_isSharedCheck_6846_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6816_ = lean_array_get_size(v_snd_6803_);
                v___x_6817_ = lean_nat_dec_lt(v___x_6795_, v___x_6816_);
                if v___x_6817_ == 0 {
                    lean_del_object(v___x_6805_);
                    lean_dec(v_snd_6803_);
                    lean_del_object(v___x_6800_);
                    v___x_6818_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1_once), _init_l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1);
                    v___x_6819_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_6819_, 0, v_fst_6802_);
                    lean_ctor_set(v___x_6819_, 1, v___x_6818_);
                    v___x_6820_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6820_, 0, v___x_6819_);
                    return v___x_6820_;
                } else {
                    v___x_6821_ = lean_nat_dec_le(v___x_6816_, v___x_6816_);
                    if v___x_6821_ == 0 {
                        if v___x_6817_ == 0 {
                            lean_dec(v_snd_6803_);
                            v_____do__lift_6808_ = v___x_6796_;
                            state = 3;
                            continue;
                        } else {
                            v___x_6822_ = 0usize;
                            v___x_6823_ = lean_usize_of_nat(v___x_6816_);
                            v___x_6824_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(v_snd_6803_, v___x_6822_, v___x_6823_, v___x_6796_, v___y_6788_, v___y_6789_, v___y_6790_, v___y_6791_);
                            lean_dec(v_snd_6803_);
                            if lean_obj_tag(v___x_6824_) == 0 {
                                v_a_6825_ = lean_ctor_get(v___x_6824_, 0);
                                lean_inc(v_a_6825_);
                                lean_dec_ref_known(v___x_6824_, 1);
                                v_____do__lift_6808_ = v_a_6825_;
                                state = 3;
                                continue;
                            } else {
                                lean_del_object(v___x_6805_);
                                lean_dec(v_fst_6802_);
                                lean_del_object(v___x_6800_);
                                v_a_6826_ = lean_ctor_get(v___x_6824_, 0);
                                v_isSharedCheck_6833_ = (!lean_is_exclusive(v___x_6824_)) as u8;
                                if v_isSharedCheck_6833_ == 0 {
                                    v___x_6828_ = v___x_6824_;
                                    v_isShared_6829_ = v_isSharedCheck_6833_;
                                    state = 6;
                                    continue;
                                } else {
                                    lean_inc(v_a_6826_);
                                    lean_dec(v___x_6824_);
                                    v___x_6828_ = lean_box(0);
                                    v_isShared_6829_ = v_isSharedCheck_6833_;
                                    state = 6;
                                    continue;
                                }
                            }
                        }
                    } else {
                        v___x_6834_ = 0usize;
                        v___x_6835_ = lean_usize_of_nat(v___x_6816_);
                        v___x_6836_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(v_snd_6803_, v___x_6834_, v___x_6835_, v___x_6796_, v___y_6788_, v___y_6789_, v___y_6790_, v___y_6791_);
                        lean_dec(v_snd_6803_);
                        if lean_obj_tag(v___x_6836_) == 0 {
                            v_a_6837_ = lean_ctor_get(v___x_6836_, 0);
                            lean_inc(v_a_6837_);
                            lean_dec_ref_known(v___x_6836_, 1);
                            v_____do__lift_6808_ = v_a_6837_;
                            state = 3;
                            continue;
                        } else {
                            lean_del_object(v___x_6805_);
                            lean_dec(v_fst_6802_);
                            lean_del_object(v___x_6800_);
                            v_a_6838_ = lean_ctor_get(v___x_6836_, 0);
                            v_isSharedCheck_6845_ = (!lean_is_exclusive(v___x_6836_)) as u8;
                            if v_isSharedCheck_6845_ == 0 {
                                v___x_6840_ = v___x_6836_;
                                v_isShared_6841_ = v_isSharedCheck_6845_;
                                state = 8;
                                continue;
                            } else {
                                lean_inc(v_a_6838_);
                                lean_dec(v___x_6836_);
                                v___x_6840_ = lean_box(0);
                                v_isShared_6841_ = v_isSharedCheck_6845_;
                                state = 8;
                                continue;
                            }
                        }
                    }
                }
            }
            3 => {
                v___x_6809_ = lean_array_to_list(v_____do__lift_6808_);
                if v_isShared_6806_ == 0 {
                    lean_ctor_set(v___x_6805_, 1, v___x_6809_);
                    v___x_6811_ = v___x_6805_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6815_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6815_, 0, v_fst_6802_);
                    lean_ctor_set(v_reuseFailAlloc_6815_, 1, v___x_6809_);
                    v___x_6811_ = v_reuseFailAlloc_6815_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_6801_ == 0 {
                    lean_ctor_set(v___x_6800_, 0, v___x_6811_);
                    v___x_6813_ = v___x_6800_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6814_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6814_, 0, v___x_6811_);
                    v___x_6813_ = v_reuseFailAlloc_6814_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6813_;
            }
            6 => {
                if v_isShared_6829_ == 0 {
                    v___x_6831_ = v___x_6828_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6832_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6832_, 0, v_a_6826_);
                    v___x_6831_ = v_reuseFailAlloc_6832_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6831_;
            }
            8 => {
                if v_isShared_6841_ == 0 {
                    v___x_6843_ = v___x_6840_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6844_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6844_, 0, v_a_6838_);
                    v___x_6843_ = v_reuseFailAlloc_6844_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_6843_;
            }
            10 => {
                if v_isShared_6851_ == 0 {
                    v___x_6853_ = v___x_6850_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_6854_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6854_, 0, v_a_6848_);
                    v___x_6853_ = v_reuseFailAlloc_6854_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_6853_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___boxed(
    mut v_f_6856_: *mut LeanObject,
    mut v_goals_6857_: *mut LeanObject,
    mut v_maxIters_6858_: *mut LeanObject,
    mut v___y_6859_: *mut LeanObject,
    mut v___y_6860_: *mut LeanObject,
    mut v___y_6861_: *mut LeanObject,
    mut v___y_6862_: *mut LeanObject,
    mut v___y_6863_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6864_: *mut LeanObject = core::ptr::null_mut();
    v_res_6864_ = l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0(v_f_6856_, v_goals_6857_, v_maxIters_6858_, v___y_6859_, v___y_6860_, v___y_6861_, v___y_6862_);
    lean_dec(v___y_6862_);
    lean_dec_ref(v___y_6861_);
    lean_dec(v___y_6860_);
    lean_dec_ref(v___y_6859_);
    return v_res_6864_;
}
pub unsafe fn _init_l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1()
-> *mut LeanObject {
    let mut v___x_6866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6867_: *mut LeanObject = core::ptr::null_mut();
    v___x_6866_ = l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__0;
    v___x_6867_ = l_Lean_stringToMessageData(v___x_6866_);
    return v___x_6867_;
}
pub unsafe fn l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0(
    mut v_f_6868_: *mut LeanObject,
    mut v_goals_6869_: *mut LeanObject,
    mut v_maxIters_6870_: *mut LeanObject,
    mut v___y_6871_: *mut LeanObject,
    mut v___y_6872_: *mut LeanObject,
    mut v___y_6873_: *mut LeanObject,
    mut v___y_6874_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6880_: u8 = 0;
    let mut v_fst_6881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6882_: u8 = 0;
    let mut v_snd_6883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6889_: u8 = 0;
    let mut v_a_6890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6893_: u8 = 0;
    let mut v___x_6895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6897_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6876_ = l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0(v_f_6868_, v_goals_6869_, v_maxIters_6870_, v___y_6871_, v___y_6872_, v___y_6873_, v___y_6874_);
                if lean_obj_tag(v___x_6876_) == 0 {
                    v_a_6877_ = lean_ctor_get(v___x_6876_, 0);
                    v_isSharedCheck_6889_ = (!lean_is_exclusive(v___x_6876_)) as u8;
                    if v_isSharedCheck_6889_ == 0 {
                        v___x_6879_ = v___x_6876_;
                        v_isShared_6880_ = v_isSharedCheck_6889_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6877_);
                        lean_dec(v___x_6876_);
                        v___x_6879_ = lean_box(0);
                        v_isShared_6880_ = v_isSharedCheck_6889_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6890_ = lean_ctor_get(v___x_6876_, 0);
                    v_isSharedCheck_6897_ = (!lean_is_exclusive(v___x_6876_)) as u8;
                    if v_isSharedCheck_6897_ == 0 {
                        v___x_6892_ = v___x_6876_;
                        v_isShared_6893_ = v_isSharedCheck_6897_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6890_);
                        lean_dec(v___x_6876_);
                        v___x_6892_ = lean_box(0);
                        v_isShared_6893_ = v_isSharedCheck_6897_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_6881_ = lean_ctor_get(v_a_6877_, 0);
                v___x_6882_ = (lean_unbox(v_fst_6881_) as u8);
                if v___x_6882_ == 1 {
                    v_snd_6883_ = lean_ctor_get(v_a_6877_, 1);
                    lean_inc(v_snd_6883_);
                    lean_dec(v_a_6877_);
                    if v_isShared_6880_ == 0 {
                        lean_ctor_set(v___x_6879_, 0, v_snd_6883_);
                        v___x_6885_ = v___x_6879_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6886_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6886_, 0, v_snd_6883_);
                        v___x_6885_ = v_reuseFailAlloc_6886_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_6879_);
                    lean_dec(v_a_6877_);
                    v___x_6887_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1_once), _init_l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1);
                    v___x_6888_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_6887_, v___y_6871_, v___y_6872_, v___y_6873_, v___y_6874_);
                    return v___x_6888_;
                }
            }
            2 => {
                return v___x_6885_;
            }
            3 => {
                if v_isShared_6893_ == 0 {
                    v___x_6895_ = v___x_6892_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6896_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6896_, 0, v_a_6890_);
                    v___x_6895_ = v_reuseFailAlloc_6896_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6895_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___boxed(
    mut v_f_6898_: *mut LeanObject,
    mut v_goals_6899_: *mut LeanObject,
    mut v_maxIters_6900_: *mut LeanObject,
    mut v___y_6901_: *mut LeanObject,
    mut v___y_6902_: *mut LeanObject,
    mut v___y_6903_: *mut LeanObject,
    mut v___y_6904_: *mut LeanObject,
    mut v___y_6905_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6906_: *mut LeanObject = core::ptr::null_mut();
    v_res_6906_ = l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0(v_f_6898_, v_goals_6899_, v_maxIters_6900_, v___y_6901_, v___y_6902_, v___y_6903_, v___y_6904_);
    lean_dec(v___y_6904_);
    lean_dec_ref(v___y_6903_);
    lean_dec(v___y_6902_);
    lean_dec_ref(v___y_6901_);
    return v_res_6906_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(
    mut v_lemmas_6907_: *mut LeanObject,
    mut v_ctx_6908_: *mut LeanObject,
    mut v_cfg_6909_: *mut LeanObject,
    mut v_a_6910_: *mut LeanObject,
    mut v_a_6911_: *mut LeanObject,
    mut v_a_6912_: *mut LeanObject,
    mut v_a_6913_: *mut LeanObject,
    mut v_a_6914_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_backtracking_6916_: u8 = 0;
    v_backtracking_6916_ = lean_ctor_get_uint8(
        v_cfg_6909_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
    );
    if v_backtracking_6916_ == 0 {
        let mut v_toApplyRulesConfig_6917_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toBacktrackConfig_6918_: *mut LeanObject = core::ptr::null_mut();
        let mut v_maxDepth_6919_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6920_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6921_: *mut LeanObject = core::ptr::null_mut();
        v_toApplyRulesConfig_6917_ = lean_ctor_get(v_cfg_6909_, 0);
        v_toBacktrackConfig_6918_ = lean_ctor_get(v_toApplyRulesConfig_6917_, 0);
        v_maxDepth_6919_ = lean_ctor_get(v_toBacktrackConfig_6918_, 0);
        lean_inc(v_maxDepth_6919_);
        v___x_6920_ = lean_alloc_closure(
            l_Lean_Meta_SolveByElim_applyFirstLemma___boxed as *mut core::ffi::c_void,
            9,
            3,
        );
        lean_closure_set(v___x_6920_, 0, v_cfg_6909_);
        lean_closure_set(v___x_6920_, 1, v_lemmas_6907_);
        lean_closure_set(v___x_6920_, 2, v_ctx_6908_);
        v___x_6921_ = l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0(v___x_6920_, v_a_6910_, v_maxDepth_6919_, v_a_6911_, v_a_6912_, v_a_6913_, v_a_6914_);
        return v___x_6921_;
    } else {
        let mut v_toApplyRulesConfig_6922_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toBacktrackConfig_6923_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6924_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6925_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6926_: *mut LeanObject = core::ptr::null_mut();
        v_toApplyRulesConfig_6922_ = lean_ctor_get(v_cfg_6909_, 0);
        v_toBacktrackConfig_6923_ = lean_ctor_get(v_toApplyRulesConfig_6922_, 0);
        lean_inc_ref(v_toBacktrackConfig_6923_);
        v___x_6924_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_;
        v___x_6925_ = lean_alloc_closure(
            l_Lean_Meta_SolveByElim_applyLemmas___boxed as *mut core::ffi::c_void,
            9,
            3,
        );
        lean_closure_set(v___x_6925_, 0, v_cfg_6909_);
        lean_closure_set(v___x_6925_, 1, v_lemmas_6907_);
        lean_closure_set(v___x_6925_, 2, v_ctx_6908_);
        v___x_6926_ = l_Lean_Meta_Tactic_Backtrack_backtrack(
            v_toBacktrackConfig_6923_,
            v___x_6924_,
            v___x_6925_,
            v_a_6910_,
            v_a_6911_,
            v_a_6912_,
            v_a_6913_,
            v_a_6914_,
        );
        return v___x_6926_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run___boxed(
    mut v_lemmas_6927_: *mut LeanObject,
    mut v_ctx_6928_: *mut LeanObject,
    mut v_cfg_6929_: *mut LeanObject,
    mut v_a_6930_: *mut LeanObject,
    mut v_a_6931_: *mut LeanObject,
    mut v_a_6932_: *mut LeanObject,
    mut v_a_6933_: *mut LeanObject,
    mut v_a_6934_: *mut LeanObject,
    mut v_a_6935_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6936_: *mut LeanObject = core::ptr::null_mut();
    v_res_6936_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(
        v_lemmas_6927_,
        v_ctx_6928_,
        v_cfg_6929_,
        v_a_6930_,
        v_a_6931_,
        v_a_6932_,
        v_a_6933_,
        v_a_6934_,
    );
    lean_dec(v_a_6934_);
    lean_dec_ref(v_a_6933_);
    lean_dec(v_a_6932_);
    lean_dec_ref(v_a_6931_);
    return v_res_6936_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2(
    mut v_mvarId_6937_: *mut LeanObject,
    mut v___y_6938_: *mut LeanObject,
    mut v___y_6939_: *mut LeanObject,
    mut v___y_6940_: *mut LeanObject,
    mut v___y_6941_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6943_: *mut LeanObject = core::ptr::null_mut();
    v___x_6943_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v_mvarId_6937_, v___y_6939_);
    return v___x_6943_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___boxed(
    mut v_mvarId_6944_: *mut LeanObject,
    mut v___y_6945_: *mut LeanObject,
    mut v___y_6946_: *mut LeanObject,
    mut v___y_6947_: *mut LeanObject,
    mut v___y_6948_: *mut LeanObject,
    mut v___y_6949_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6950_: *mut LeanObject = core::ptr::null_mut();
    v_res_6950_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2(v_mvarId_6944_, v___y_6945_, v___y_6946_, v___y_6947_, v___y_6948_);
    lean_dec(v___y_6948_);
    lean_dec_ref(v___y_6947_);
    lean_dec(v___y_6946_);
    lean_dec_ref(v___y_6945_);
    lean_dec(v_mvarId_6944_);
    return v_res_6950_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4(
    mut v_00_u03b2_6951_: *mut LeanObject,
    mut v_x_6952_: *mut LeanObject,
    mut v_x_6953_: *mut LeanObject,
) -> u8 {
    let mut v___x_6954_: u8 = 0;
    v___x_6954_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(v_x_6952_, v_x_6953_);
    return v___x_6954_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___boxed(
    mut v_00_u03b2_6955_: *mut LeanObject,
    mut v_x_6956_: *mut LeanObject,
    mut v_x_6957_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6958_: u8 = 0;
    let mut v_r_6959_: *mut LeanObject = core::ptr::null_mut();
    v_res_6958_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4(v_00_u03b2_6955_, v_x_6956_, v_x_6957_);
    lean_dec(v_x_6957_);
    lean_dec_ref(v_x_6956_);
    v_r_6959_ = lean_box((v_res_6958_) as usize);
    return v_r_6959_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5(
    mut v_00_u03b2_6960_: *mut LeanObject,
    mut v_x_6961_: *mut LeanObject,
    mut v_x_6962_: usize,
    mut v_x_6963_: *mut LeanObject,
) -> u8 {
    let mut v___x_6964_: u8 = 0;
    v___x_6964_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_6961_, v_x_6962_, v_x_6963_);
    return v___x_6964_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___boxed(
    mut v_00_u03b2_6965_: *mut LeanObject,
    mut v_x_6966_: *mut LeanObject,
    mut v_x_6967_: *mut LeanObject,
    mut v_x_6968_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_2759__boxed_6969_: usize = 0;
    let mut v_res_6970_: u8 = 0;
    let mut v_r_6971_: *mut LeanObject = core::ptr::null_mut();
    v_x_2759__boxed_6969_ = lean_unbox_usize(v_x_6967_);
    lean_dec(v_x_6967_);
    v_res_6970_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5(v_00_u03b2_6965_, v_x_6966_, v_x_2759__boxed_6969_, v_x_6968_);
    lean_dec(v_x_6968_);
    lean_dec_ref(v_x_6966_);
    v_r_6971_ = lean_box((v_res_6970_) as usize);
    return v_r_6971_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7(
    mut v_00_u03b2_6972_: *mut LeanObject,
    mut v_keys_6973_: *mut LeanObject,
    mut v_vals_6974_: *mut LeanObject,
    mut v_heq_6975_: *mut LeanObject,
    mut v_i_6976_: *mut LeanObject,
    mut v_k_6977_: *mut LeanObject,
) -> u8 {
    let mut v___x_6978_: u8 = 0;
    v___x_6978_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(v_keys_6973_, v_i_6976_, v_k_6977_);
    return v___x_6978_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___boxed(
    mut v_00_u03b2_6979_: *mut LeanObject,
    mut v_keys_6980_: *mut LeanObject,
    mut v_vals_6981_: *mut LeanObject,
    mut v_heq_6982_: *mut LeanObject,
    mut v_i_6983_: *mut LeanObject,
    mut v_k_6984_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6985_: u8 = 0;
    let mut v_r_6986_: *mut LeanObject = core::ptr::null_mut();
    v_res_6985_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7(v_00_u03b2_6979_, v_keys_6980_, v_vals_6981_, v_heq_6982_, v_i_6983_, v_k_6984_);
    lean_dec(v_k_6984_);
    lean_dec_ref(v_vals_6981_);
    lean_dec_ref(v_keys_6980_);
    v_r_6986_ = lean_box((v_res_6985_) as usize);
    return v_r_6986_;
}
pub unsafe fn _init_l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1() -> *mut LeanObject {
    let mut v___x_6988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6989_: *mut LeanObject = core::ptr::null_mut();
    v___x_6988_ = l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__0;
    v___x_6989_ = l_Lean_stringToMessageData(v___x_6988_);
    return v___x_6989_;
}
pub unsafe fn l_Lean_Meta_SolveByElim_solveByElim___lam__0(
    mut v_x_6990_: *mut LeanObject,
    mut v___y_6991_: *mut LeanObject,
    mut v___y_6992_: *mut LeanObject,
    mut v___y_6993_: *mut LeanObject,
    mut v___y_6994_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6997_: *mut LeanObject = core::ptr::null_mut();
    v___x_6996_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1_once),
        _init_l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1,
    );
    v___x_6997_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_6997_, 0, v___x_6996_);
    return v___x_6997_;
}
pub unsafe fn l_Lean_Meta_SolveByElim_solveByElim___lam__0___boxed(
    mut v_x_6998_: *mut LeanObject,
    mut v___y_6999_: *mut LeanObject,
    mut v___y_7000_: *mut LeanObject,
    mut v___y_7001_: *mut LeanObject,
    mut v___y_7002_: *mut LeanObject,
    mut v___y_7003_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7004_: *mut LeanObject = core::ptr::null_mut();
    v_res_7004_ = l_Lean_Meta_SolveByElim_solveByElim___lam__0(
        v_x_6998_,
        v___y_6999_,
        v___y_7000_,
        v___y_7001_,
        v___y_7002_,
    );
    lean_dec(v___y_7002_);
    lean_dec_ref(v___y_7001_);
    lean_dec(v___y_7000_);
    lean_dec_ref(v___y_6999_);
    lean_dec_ref(v_x_6998_);
    return v_res_7004_;
}
pub unsafe fn _init_l_Lean_Meta_SolveByElim_solveByElim___closed__1() -> *mut LeanObject {
    let mut v___x_7006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7008_: *mut LeanObject = core::ptr::null_mut();
    v___x_7006_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_;
    v___x_7007_ = l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__1;
    v___x_7008_ = l_Lean_Name_append(v___x_7007_, v___x_7006_);
    return v___x_7008_;
}
pub unsafe fn l_Lean_Meta_SolveByElim_solveByElim(
    mut v_cfg_7009_: *mut LeanObject,
    mut v_lemmas_7010_: *mut LeanObject,
    mut v_ctx_7011_: *mut LeanObject,
    mut v_goals_7012_: *mut LeanObject,
    mut v_a_7013_: *mut LeanObject,
    mut v_a_7014_: *mut LeanObject,
    mut v_a_7015_: *mut LeanObject,
    mut v_a_7016_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cfg_7018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7028_: u8 = 0;
    let mut v___y_7029_: u8 = 0;
    let mut v_a_7030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7032_: f64 = 0.0;
    let mut v___x_7033_: f64 = 0.0;
    let mut v___x_7034_: f64 = 0.0;
    let mut v___x_7035_: f64 = 0.0;
    let mut v___x_7036_: f64 = 0.0;
    let mut v___x_7037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7048_: u8 = 0;
    let mut v___y_7049_: u8 = 0;
    let mut v_a_7050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7058_: u8 = 0;
    let mut v___y_7059_: u8 = 0;
    let mut v_a_7060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7062_: f64 = 0.0;
    let mut v___x_7063_: f64 = 0.0;
    let mut v___x_7064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7075_: u8 = 0;
    let mut v___y_7076_: u8 = 0;
    let mut v_a_7077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7085_: u8 = 0;
    let mut v___y_7086_: u8 = 0;
    let mut v___x_7087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7090_: u8 = 0;
    let mut v___x_7091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7099_: u8 = 0;
    let mut v___x_7101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7103_: u8 = 0;
    let mut v_a_7104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7114_: u8 = 0;
    let mut v___x_7116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7118_: u8 = 0;
    let mut v_a_7119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7122_: u8 = 0;
    let mut v_tail_7123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplyRulesConfig_7124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exfalso_7125_: u8 = 0;
    let mut v_options_7126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_7127_: u8 = 0;
    let mut v_head_7128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7131_: u8 = 0;
    let mut v___x_7132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7141_: u8 = 0;
    let mut v___x_7143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7145_: u8 = 0;
    let mut v_isSharedCheck_7146_: u8 = 0;
    let mut v_unused_7147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_7148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7151_: u8 = 0;
    let mut v_inheritedTraceOptions_7152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7156_: u8 = 0;
    let mut v___x_7157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7158_: u8 = 0;
    let mut v___x_7159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7168_: u8 = 0;
    let mut v___x_7170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7172_: u8 = 0;
    let mut v_isSharedCheck_7173_: u8 = 0;
    let mut v_unused_7174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7175_: u8 = 0;
    let mut v___x_7176_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_cfg_7018_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_processOptions(v_cfg_7009_);
                lean_inc(v_goals_7012_);
                lean_inc_ref(v_cfg_7018_);
                lean_inc_ref(v_ctx_7011_);
                lean_inc(v_lemmas_7010_);
                v___x_7019_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_7010_, v_ctx_7011_, v_cfg_7018_, v_goals_7012_, v_a_7013_, v_a_7014_, v_a_7015_, v_a_7016_);
                if lean_obj_tag(v___x_7019_) == 0 {
                    lean_dec_ref(v_cfg_7018_);
                    lean_dec(v_goals_7012_);
                    lean_dec_ref(v_ctx_7011_);
                    lean_dec(v_lemmas_7010_);
                    return v___x_7019_;
                } else {
                    v_a_7020_ = lean_ctor_get(v___x_7019_, 0);
                    lean_inc(v_a_7020_);
                    v___f_7021_ = l_Lean_Meta_SolveByElim_solveByElim___closed__0;
                    v___x_7175_ = l_Lean_Exception_isInterrupt(v_a_7020_);
                    if v___x_7175_ == 0 {
                        v___x_7176_ = l_Lean_Exception_isRuntime(v_a_7020_);
                        v___y_7122_ = v___x_7176_;
                        state = 10;
                        continue;
                    } else {
                        lean_dec(v_a_7020_);
                        v___y_7122_ = v___x_7175_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7031_ = lean_io_mono_nanos_now();
                v___x_7032_ = lean_float_of_nat(v___y_7023_);
                v___x_7033_ = lean_float_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2_once
                    ),
                    _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2,
                );
                v___x_7034_ = lean_float_div(v___x_7032_, v___x_7033_);
                v___x_7035_ = lean_float_of_nat(v___x_7031_);
                v___x_7036_ = lean_float_div(v___x_7035_, v___x_7033_);
                v___x_7037_ = lean_box_float(v___x_7034_);
                v___x_7038_ = lean_box_float(v___x_7036_);
                v___x_7039_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_7039_, 0, v___x_7037_);
                lean_ctor_set(v___x_7039_, 1, v___x_7038_);
                v___x_7040_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_7040_, 0, v_a_7030_);
                lean_ctor_set(v___x_7040_, 1, v___x_7039_);
                lean_inc_ref(v___y_7027_);
                lean_inc(v___y_7024_);
                v___x_7041_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___y_7024_, v___y_7029_, v___y_7027_, v___y_7026_, v___y_7028_, v___y_7025_, v___f_7021_, v___x_7040_, v_a_7013_, v_a_7014_, v_a_7015_, v_a_7016_);
                return v___x_7041_;
            }
            2 => {
                v___x_7051_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7051_, 0, v_a_7050_);
                v___y_7023_ = v___y_7043_;
                v___y_7024_ = v___y_7044_;
                v___y_7025_ = v___y_7045_;
                v___y_7026_ = v___y_7046_;
                v___y_7027_ = v___y_7047_;
                v___y_7028_ = v___y_7049_;
                v___y_7029_ = v___y_7048_;
                v_a_7030_ = v___x_7051_;
                state = 1;
                continue;
            }
            3 => {
                v___x_7061_ = lean_io_get_num_heartbeats();
                v___x_7062_ = lean_float_of_nat(v___y_7055_);
                v___x_7063_ = lean_float_of_nat(v___x_7061_);
                v___x_7064_ = lean_box_float(v___x_7062_);
                v___x_7065_ = lean_box_float(v___x_7063_);
                v___x_7066_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_7066_, 0, v___x_7064_);
                lean_ctor_set(v___x_7066_, 1, v___x_7065_);
                v___x_7067_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_7067_, 0, v_a_7060_);
                lean_ctor_set(v___x_7067_, 1, v___x_7066_);
                lean_inc_ref(v___y_7057_);
                lean_inc(v___y_7053_);
                v___x_7068_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___y_7053_, v___y_7059_, v___y_7057_, v___y_7056_, v___y_7058_, v___y_7054_, v___f_7021_, v___x_7067_, v_a_7013_, v_a_7014_, v_a_7015_, v_a_7016_);
                return v___x_7068_;
            }
            4 => {
                v___x_7078_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7078_, 0, v_a_7077_);
                v___y_7053_ = v___y_7070_;
                v___y_7054_ = v___y_7071_;
                v___y_7055_ = v___y_7072_;
                v___y_7056_ = v___y_7073_;
                v___y_7057_ = v___y_7074_;
                v___y_7058_ = v___y_7076_;
                v___y_7059_ = v___y_7075_;
                v_a_7060_ = v___x_7078_;
                state = 3;
                continue;
            }
            5 => {
                v___x_7087_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg(v_a_7016_);
                v_a_7088_ = lean_ctor_get(v___x_7087_, 0);
                lean_inc(v_a_7088_);
                lean_dec_ref(v___x_7087_);
                v___x_7089_ = l_Lean_trace_profiler_useHeartbeats;
                v___x_7090_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(
                    v___y_7083_,
                    v___x_7089_,
                );
                if v___x_7090_ == 0 {
                    v___x_7091_ = lean_io_mono_nanos_now();
                    v___x_7092_ = l_Lean_MVarId_exfalso(
                        v___y_7080_,
                        v_a_7013_,
                        v_a_7014_,
                        v_a_7015_,
                        v_a_7016_,
                    );
                    if lean_obj_tag(v___x_7092_) == 0 {
                        v_a_7093_ = lean_ctor_get(v___x_7092_, 0);
                        lean_inc(v_a_7093_);
                        lean_dec_ref_known(v___x_7092_, 1);
                        v___x_7094_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_7094_, 0, v_a_7093_);
                        lean_ctor_set(v___x_7094_, 1, v___y_7081_);
                        v___x_7095_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_7010_, v_ctx_7011_, v_cfg_7018_, v___x_7094_, v_a_7013_, v_a_7014_, v_a_7015_, v_a_7016_);
                        if lean_obj_tag(v___x_7095_) == 0 {
                            v_a_7096_ = lean_ctor_get(v___x_7095_, 0);
                            v_isSharedCheck_7103_ = (!lean_is_exclusive(v___x_7095_)) as u8;
                            if v_isSharedCheck_7103_ == 0 {
                                v___x_7098_ = v___x_7095_;
                                v_isShared_7099_ = v_isSharedCheck_7103_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_7096_);
                                lean_dec(v___x_7095_);
                                v___x_7098_ = lean_box(0);
                                v_isShared_7099_ = v_isSharedCheck_7103_;
                                state = 6;
                                continue;
                            }
                        } else {
                            v_a_7104_ = lean_ctor_get(v___x_7095_, 0);
                            lean_inc(v_a_7104_);
                            lean_dec_ref_known(v___x_7095_, 1);
                            v___y_7043_ = v___x_7091_;
                            v___y_7044_ = v___y_7082_;
                            v___y_7045_ = v_a_7088_;
                            v___y_7046_ = v___y_7083_;
                            v___y_7047_ = v___y_7084_;
                            v___y_7048_ = v___y_7085_;
                            v___y_7049_ = v___y_7086_;
                            v_a_7050_ = v_a_7104_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v___y_7081_);
                        lean_dec_ref(v_cfg_7018_);
                        lean_dec_ref(v_ctx_7011_);
                        lean_dec(v_lemmas_7010_);
                        v_a_7105_ = lean_ctor_get(v___x_7092_, 0);
                        lean_inc(v_a_7105_);
                        lean_dec_ref_known(v___x_7092_, 1);
                        v___y_7043_ = v___x_7091_;
                        v___y_7044_ = v___y_7082_;
                        v___y_7045_ = v_a_7088_;
                        v___y_7046_ = v___y_7083_;
                        v___y_7047_ = v___y_7084_;
                        v___y_7048_ = v___y_7085_;
                        v___y_7049_ = v___y_7086_;
                        v_a_7050_ = v_a_7105_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_7106_ = lean_io_get_num_heartbeats();
                    v___x_7107_ = l_Lean_MVarId_exfalso(
                        v___y_7080_,
                        v_a_7013_,
                        v_a_7014_,
                        v_a_7015_,
                        v_a_7016_,
                    );
                    if lean_obj_tag(v___x_7107_) == 0 {
                        v_a_7108_ = lean_ctor_get(v___x_7107_, 0);
                        lean_inc(v_a_7108_);
                        lean_dec_ref_known(v___x_7107_, 1);
                        v___x_7109_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_7109_, 0, v_a_7108_);
                        lean_ctor_set(v___x_7109_, 1, v___y_7081_);
                        v___x_7110_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_7010_, v_ctx_7011_, v_cfg_7018_, v___x_7109_, v_a_7013_, v_a_7014_, v_a_7015_, v_a_7016_);
                        if lean_obj_tag(v___x_7110_) == 0 {
                            v_a_7111_ = lean_ctor_get(v___x_7110_, 0);
                            v_isSharedCheck_7118_ = (!lean_is_exclusive(v___x_7110_)) as u8;
                            if v_isSharedCheck_7118_ == 0 {
                                v___x_7113_ = v___x_7110_;
                                v_isShared_7114_ = v_isSharedCheck_7118_;
                                state = 8;
                                continue;
                            } else {
                                lean_inc(v_a_7111_);
                                lean_dec(v___x_7110_);
                                v___x_7113_ = lean_box(0);
                                v_isShared_7114_ = v_isSharedCheck_7118_;
                                state = 8;
                                continue;
                            }
                        } else {
                            v_a_7119_ = lean_ctor_get(v___x_7110_, 0);
                            lean_inc(v_a_7119_);
                            lean_dec_ref_known(v___x_7110_, 1);
                            v___y_7070_ = v___y_7082_;
                            v___y_7071_ = v_a_7088_;
                            v___y_7072_ = v___x_7106_;
                            v___y_7073_ = v___y_7083_;
                            v___y_7074_ = v___y_7084_;
                            v___y_7075_ = v___y_7085_;
                            v___y_7076_ = v___y_7086_;
                            v_a_7077_ = v_a_7119_;
                            state = 4;
                            continue;
                        }
                    } else {
                        lean_dec(v___y_7081_);
                        lean_dec_ref(v_cfg_7018_);
                        lean_dec_ref(v_ctx_7011_);
                        lean_dec(v_lemmas_7010_);
                        v_a_7120_ = lean_ctor_get(v___x_7107_, 0);
                        lean_inc(v_a_7120_);
                        lean_dec_ref_known(v___x_7107_, 1);
                        v___y_7070_ = v___y_7082_;
                        v___y_7071_ = v_a_7088_;
                        v___y_7072_ = v___x_7106_;
                        v___y_7073_ = v___y_7083_;
                        v___y_7074_ = v___y_7084_;
                        v___y_7075_ = v___y_7085_;
                        v___y_7076_ = v___y_7086_;
                        v_a_7077_ = v_a_7120_;
                        state = 4;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_7099_ == 0 {
                    lean_ctor_set_tag(v___x_7098_, 1);
                    v___x_7101_ = v___x_7098_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_7102_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7102_, 0, v_a_7096_);
                    v___x_7101_ = v_reuseFailAlloc_7102_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_7023_ = v___x_7091_;
                v___y_7024_ = v___y_7082_;
                v___y_7025_ = v_a_7088_;
                v___y_7026_ = v___y_7083_;
                v___y_7027_ = v___y_7084_;
                v___y_7028_ = v___y_7086_;
                v___y_7029_ = v___y_7085_;
                v_a_7030_ = v___x_7101_;
                state = 1;
                continue;
            }
            8 => {
                if v_isShared_7114_ == 0 {
                    lean_ctor_set_tag(v___x_7113_, 1);
                    v___x_7116_ = v___x_7113_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_7117_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7117_, 0, v_a_7111_);
                    v___x_7116_ = v_reuseFailAlloc_7117_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___y_7053_ = v___y_7082_;
                v___y_7054_ = v_a_7088_;
                v___y_7055_ = v___x_7106_;
                v___y_7056_ = v___y_7083_;
                v___y_7057_ = v___y_7084_;
                v___y_7058_ = v___y_7086_;
                v___y_7059_ = v___y_7085_;
                v_a_7060_ = v___x_7116_;
                state = 3;
                continue;
            }
            10 => {
                if v___y_7122_ == 0 {
                    if lean_obj_tag(v_goals_7012_) == 1 {
                        v_tail_7123_ = lean_ctor_get(v_goals_7012_, 1);
                        lean_inc(v_tail_7123_);
                        if lean_obj_tag(v_tail_7123_) == 0 {
                            v_toApplyRulesConfig_7124_ = lean_ctor_get(v_cfg_7018_, 0);
                            lean_inc_ref(v_toApplyRulesConfig_7124_);
                            v_exfalso_7125_ = lean_ctor_get_uint8(
                                v_toApplyRulesConfig_7124_,
                                (core::mem::size_of::<*mut LeanObject>() * 2 + 2) as u32,
                            );
                            lean_dec_ref(v_toApplyRulesConfig_7124_);
                            if v_exfalso_7125_ == 1 {
                                lean_dec_ref_known(v___x_7019_, 1);
                                v_options_7126_ = lean_ctor_get(v_a_7015_, 2);
                                v_hasTrace_7127_ = lean_ctor_get_uint8(
                                    v_options_7126_,
                                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                                );
                                if v_hasTrace_7127_ == 0 {
                                    v_head_7128_ = lean_ctor_get(v_goals_7012_, 0);
                                    v_isSharedCheck_7146_ =
                                        (!lean_is_exclusive(v_goals_7012_)) as u8;
                                    if v_isSharedCheck_7146_ == 0 {
                                        v_unused_7147_ = lean_ctor_get(v_goals_7012_, 1);
                                        lean_dec(v_unused_7147_);
                                        v___x_7130_ = v_goals_7012_;
                                        v_isShared_7131_ = v_isSharedCheck_7146_;
                                        state = 11;
                                        continue;
                                    } else {
                                        lean_inc(v_head_7128_);
                                        lean_dec(v_goals_7012_);
                                        v___x_7130_ = lean_box(0);
                                        v_isShared_7131_ = v_isSharedCheck_7146_;
                                        state = 11;
                                        continue;
                                    }
                                } else {
                                    v_head_7148_ = lean_ctor_get(v_goals_7012_, 0);
                                    v_isSharedCheck_7173_ =
                                        (!lean_is_exclusive(v_goals_7012_)) as u8;
                                    if v_isSharedCheck_7173_ == 0 {
                                        v_unused_7174_ = lean_ctor_get(v_goals_7012_, 1);
                                        lean_dec(v_unused_7174_);
                                        v___x_7150_ = v_goals_7012_;
                                        v_isShared_7151_ = v_isSharedCheck_7173_;
                                        state = 15;
                                        continue;
                                    } else {
                                        lean_inc(v_head_7148_);
                                        lean_dec(v_goals_7012_);
                                        v___x_7150_ = lean_box(0);
                                        v_isShared_7151_ = v_isSharedCheck_7173_;
                                        state = 15;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec_ref_known(v_goals_7012_, 2);
                                lean_dec_ref(v_cfg_7018_);
                                lean_dec_ref(v_ctx_7011_);
                                lean_dec(v_lemmas_7010_);
                                return v___x_7019_;
                            }
                        } else {
                            lean_dec(v_tail_7123_);
                            lean_dec_ref_known(v_goals_7012_, 2);
                            lean_dec_ref(v_cfg_7018_);
                            lean_dec_ref(v_ctx_7011_);
                            lean_dec(v_lemmas_7010_);
                            return v___x_7019_;
                        }
                    } else {
                        lean_dec_ref(v_cfg_7018_);
                        lean_dec(v_goals_7012_);
                        lean_dec_ref(v_ctx_7011_);
                        lean_dec(v_lemmas_7010_);
                        return v___x_7019_;
                    }
                } else {
                    lean_dec_ref(v_cfg_7018_);
                    lean_dec(v_goals_7012_);
                    lean_dec_ref(v_ctx_7011_);
                    lean_dec(v_lemmas_7010_);
                    return v___x_7019_;
                }
            }
            11 => {
                v___x_7132_ =
                    l_Lean_MVarId_exfalso(v_head_7128_, v_a_7013_, v_a_7014_, v_a_7015_, v_a_7016_);
                if lean_obj_tag(v___x_7132_) == 0 {
                    v_a_7133_ = lean_ctor_get(v___x_7132_, 0);
                    lean_inc(v_a_7133_);
                    lean_dec_ref_known(v___x_7132_, 1);
                    if v_isShared_7131_ == 0 {
                        lean_ctor_set(v___x_7130_, 0, v_a_7133_);
                        v___x_7135_ = v___x_7130_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_7137_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7137_, 0, v_a_7133_);
                        lean_ctor_set(v_reuseFailAlloc_7137_, 1, v_tail_7123_);
                        v___x_7135_ = v_reuseFailAlloc_7137_;
                        state = 12;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_7130_);
                    lean_dec_ref(v_cfg_7018_);
                    lean_dec_ref(v_ctx_7011_);
                    lean_dec(v_lemmas_7010_);
                    v_a_7138_ = lean_ctor_get(v___x_7132_, 0);
                    v_isSharedCheck_7145_ = (!lean_is_exclusive(v___x_7132_)) as u8;
                    if v_isSharedCheck_7145_ == 0 {
                        v___x_7140_ = v___x_7132_;
                        v_isShared_7141_ = v_isSharedCheck_7145_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_a_7138_);
                        lean_dec(v___x_7132_);
                        v___x_7140_ = lean_box(0);
                        v_isShared_7141_ = v_isSharedCheck_7145_;
                        state = 13;
                        continue;
                    }
                }
            }
            12 => {
                v___x_7136_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_7010_, v_ctx_7011_, v_cfg_7018_, v___x_7135_, v_a_7013_, v_a_7014_, v_a_7015_, v_a_7016_);
                return v___x_7136_;
            }
            13 => {
                if v_isShared_7141_ == 0 {
                    v___x_7143_ = v___x_7140_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_7144_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7144_, 0, v_a_7138_);
                    v___x_7143_ = v_reuseFailAlloc_7144_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_7143_;
            }
            15 => {
                v_inheritedTraceOptions_7152_ = lean_ctor_get(v_a_7015_, 13);
                v___x_7153_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_;
                v___x_7154_ = l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___closed__0;
                v___x_7155_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_SolveByElim_solveByElim___closed__1),
                    core::ptr::addr_of_mut!(l_Lean_Meta_SolveByElim_solveByElim___closed__1_once),
                    _init_l_Lean_Meta_SolveByElim_solveByElim___closed__1,
                );
                v___x_7156_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                    v_inheritedTraceOptions_7152_,
                    v_options_7126_,
                    v___x_7155_,
                );
                if v___x_7156_ == 0 {
                    v___x_7157_ = l_Lean_trace_profiler;
                    v___x_7158_ =
                        l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(
                            v_options_7126_,
                            v___x_7157_,
                        );
                    if v___x_7158_ == 0 {
                        v___x_7159_ = l_Lean_MVarId_exfalso(
                            v_head_7148_,
                            v_a_7013_,
                            v_a_7014_,
                            v_a_7015_,
                            v_a_7016_,
                        );
                        if lean_obj_tag(v___x_7159_) == 0 {
                            v_a_7160_ = lean_ctor_get(v___x_7159_, 0);
                            lean_inc(v_a_7160_);
                            lean_dec_ref_known(v___x_7159_, 1);
                            if v_isShared_7151_ == 0 {
                                lean_ctor_set(v___x_7150_, 0, v_a_7160_);
                                v___x_7162_ = v___x_7150_;
                                state = 16;
                                continue;
                            } else {
                                v_reuseFailAlloc_7164_ = lean_alloc_ctor(1, 2, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_7164_, 0, v_a_7160_);
                                lean_ctor_set(v_reuseFailAlloc_7164_, 1, v_tail_7123_);
                                v___x_7162_ = v_reuseFailAlloc_7164_;
                                state = 16;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_7150_);
                            lean_dec_ref(v_cfg_7018_);
                            lean_dec_ref(v_ctx_7011_);
                            lean_dec(v_lemmas_7010_);
                            v_a_7165_ = lean_ctor_get(v___x_7159_, 0);
                            v_isSharedCheck_7172_ = (!lean_is_exclusive(v___x_7159_)) as u8;
                            if v_isSharedCheck_7172_ == 0 {
                                v___x_7167_ = v___x_7159_;
                                v_isShared_7168_ = v_isSharedCheck_7172_;
                                state = 17;
                                continue;
                            } else {
                                lean_inc(v_a_7165_);
                                lean_dec(v___x_7159_);
                                v___x_7167_ = lean_box(0);
                                v_isShared_7168_ = v_isSharedCheck_7172_;
                                state = 17;
                                continue;
                            }
                        }
                    } else {
                        lean_del_object(v___x_7150_);
                        v___y_7080_ = v_head_7148_;
                        v___y_7081_ = v_tail_7123_;
                        v___y_7082_ = v___x_7153_;
                        v___y_7083_ = v_options_7126_;
                        v___y_7084_ = v___x_7154_;
                        v___y_7085_ = v_exfalso_7125_;
                        v___y_7086_ = v___x_7156_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_7150_);
                    v___y_7080_ = v_head_7148_;
                    v___y_7081_ = v_tail_7123_;
                    v___y_7082_ = v___x_7153_;
                    v___y_7083_ = v_options_7126_;
                    v___y_7084_ = v___x_7154_;
                    v___y_7085_ = v_exfalso_7125_;
                    v___y_7086_ = v___x_7156_;
                    state = 5;
                    continue;
                }
            }
            16 => {
                v___x_7163_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_7010_, v_ctx_7011_, v_cfg_7018_, v___x_7162_, v_a_7013_, v_a_7014_, v_a_7015_, v_a_7016_);
                return v___x_7163_;
            }
            17 => {
                if v_isShared_7168_ == 0 {
                    v___x_7170_ = v___x_7167_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_7171_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7171_, 0, v_a_7165_);
                    v___x_7170_ = v_reuseFailAlloc_7171_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_7170_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_SolveByElim_solveByElim___boxed(
    mut v_cfg_7177_: *mut LeanObject,
    mut v_lemmas_7178_: *mut LeanObject,
    mut v_ctx_7179_: *mut LeanObject,
    mut v_goals_7180_: *mut LeanObject,
    mut v_a_7181_: *mut LeanObject,
    mut v_a_7182_: *mut LeanObject,
    mut v_a_7183_: *mut LeanObject,
    mut v_a_7184_: *mut LeanObject,
    mut v_a_7185_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7186_: *mut LeanObject = core::ptr::null_mut();
    v_res_7186_ = l_Lean_Meta_SolveByElim_solveByElim(
        v_cfg_7177_,
        v_lemmas_7178_,
        v_ctx_7179_,
        v_goals_7180_,
        v_a_7181_,
        v_a_7182_,
        v_a_7183_,
        v_a_7184_,
    );
    lean_dec(v_a_7184_);
    lean_dec_ref(v_a_7183_);
    lean_dec(v_a_7182_);
    lean_dec_ref(v_a_7181_);
    return v_res_7186_;
}
pub unsafe fn l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0(
    mut v_x_7187_: *mut LeanObject,
    mut v_x_7188_: *mut LeanObject,
    mut v___y_7189_: *mut LeanObject,
    mut v___y_7190_: *mut LeanObject,
    mut v___y_7191_: *mut LeanObject,
    mut v___y_7192_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_7196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_7197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7200_: u8 = 0;
    let mut v___x_7201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7210_: u8 = 0;
    let mut v___y_7212_: u8 = 0;
    let mut v___x_7215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7217_: u8 = 0;
    let mut v___x_7218_: u8 = 0;
    let mut v_isSharedCheck_7219_: u8 = 0;
    let mut v_isSharedCheck_7220_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_7187_) == 0 {
                    v___x_7194_ = l_List_reverse___redArg(v_x_7188_);
                    v___x_7195_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_7195_, 0, v___x_7194_);
                    return v___x_7195_;
                } else {
                    v_head_7196_ = lean_ctor_get(v_x_7187_, 0);
                    v_tail_7197_ = lean_ctor_get(v_x_7187_, 1);
                    v_isSharedCheck_7220_ = (!lean_is_exclusive(v_x_7187_)) as u8;
                    if v_isSharedCheck_7220_ == 0 {
                        v___x_7199_ = v_x_7187_;
                        v_isShared_7200_ = v_isSharedCheck_7220_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_7197_);
                        lean_inc(v_head_7196_);
                        lean_dec(v_x_7187_);
                        v___x_7199_ = lean_box(0);
                        v_isShared_7200_ = v_isSharedCheck_7220_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7201_ = l_Lean_Expr_applySymm(
                    v_head_7196_,
                    v___y_7189_,
                    v___y_7190_,
                    v___y_7191_,
                    v___y_7192_,
                );
                if lean_obj_tag(v___x_7201_) == 0 {
                    v_a_7202_ = lean_ctor_get(v___x_7201_, 0);
                    lean_inc(v_a_7202_);
                    lean_dec_ref_known(v___x_7201_, 1);
                    if v_isShared_7200_ == 0 {
                        lean_ctor_set(v___x_7199_, 1, v_x_7188_);
                        lean_ctor_set(v___x_7199_, 0, v_a_7202_);
                        v___x_7204_ = v___x_7199_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_7206_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7206_, 0, v_a_7202_);
                        lean_ctor_set(v_reuseFailAlloc_7206_, 1, v_x_7188_);
                        v___x_7204_ = v_reuseFailAlloc_7206_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_7199_);
                    v_a_7207_ = lean_ctor_get(v___x_7201_, 0);
                    v_isSharedCheck_7219_ = (!lean_is_exclusive(v___x_7201_)) as u8;
                    if v_isSharedCheck_7219_ == 0 {
                        v___x_7209_ = v___x_7201_;
                        v_isShared_7210_ = v_isSharedCheck_7219_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_7207_);
                        lean_dec(v___x_7201_);
                        v___x_7209_ = lean_box(0);
                        v_isShared_7210_ = v_isSharedCheck_7219_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v_x_7187_ = v_tail_7197_;
                v_x_7188_ = v___x_7204_;
                state = 0;
                continue;
            }
            3 => {
                v___x_7217_ = l_Lean_Exception_isInterrupt(v_a_7207_);
                if v___x_7217_ == 0 {
                    lean_inc(v_a_7207_);
                    v___x_7218_ = l_Lean_Exception_isRuntime(v_a_7207_);
                    v___y_7212_ = v___x_7218_;
                    state = 4;
                    continue;
                } else {
                    v___y_7212_ = v___x_7217_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v___y_7212_ == 0 {
                    lean_del_object(v___x_7209_);
                    lean_dec(v_a_7207_);
                    v_x_7187_ = v_tail_7197_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_tail_7197_);
                    lean_dec(v_x_7188_);
                    if v_isShared_7210_ == 0 {
                        v___x_7215_ = v___x_7209_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_7216_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7216_, 0, v_a_7207_);
                        v___x_7215_ = v_reuseFailAlloc_7216_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_7215_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0___boxed(
    mut v_x_7221_: *mut LeanObject,
    mut v_x_7222_: *mut LeanObject,
    mut v___y_7223_: *mut LeanObject,
    mut v___y_7224_: *mut LeanObject,
    mut v___y_7225_: *mut LeanObject,
    mut v___y_7226_: *mut LeanObject,
    mut v___y_7227_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7228_: *mut LeanObject = core::ptr::null_mut();
    v_res_7228_ = l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0(
        v_x_7221_,
        v_x_7222_,
        v___y_7223_,
        v___y_7224_,
        v___y_7225_,
        v___y_7226_,
    );
    lean_dec(v___y_7226_);
    lean_dec_ref(v___y_7225_);
    lean_dec(v___y_7224_);
    lean_dec_ref(v___y_7223_);
    return v_res_7228_;
}
pub unsafe fn l_Lean_Meta_SolveByElim_saturateSymm(
    mut v_symm_7229_: u8,
    mut v_hyps_7230_: *mut LeanObject,
    mut v_a_7231_: *mut LeanObject,
    mut v_a_7232_: *mut LeanObject,
    mut v_a_7233_: *mut LeanObject,
    mut v_a_7234_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7242_: u8 = 0;
    let mut v___x_7243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7247_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_symm_7229_ == 0 {
                    v___x_7236_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_7236_, 0, v_hyps_7230_);
                    return v___x_7236_;
                } else {
                    v___x_7237_ = lean_box(0);
                    lean_inc(v_hyps_7230_);
                    v___x_7238_ =
                        l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0(
                            v_hyps_7230_,
                            v___x_7237_,
                            v_a_7231_,
                            v_a_7232_,
                            v_a_7233_,
                            v_a_7234_,
                        );
                    if lean_obj_tag(v___x_7238_) == 0 {
                        v_a_7239_ = lean_ctor_get(v___x_7238_, 0);
                        v_isSharedCheck_7247_ = (!lean_is_exclusive(v___x_7238_)) as u8;
                        if v_isSharedCheck_7247_ == 0 {
                            v___x_7241_ = v___x_7238_;
                            v_isShared_7242_ = v_isSharedCheck_7247_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_7239_);
                            lean_dec(v___x_7238_);
                            v___x_7241_ = lean_box(0);
                            v_isShared_7242_ = v_isSharedCheck_7247_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_hyps_7230_);
                        return v___x_7238_;
                    }
                }
            }
            1 => {
                v___x_7243_ = l_List_appendTR___redArg(v_hyps_7230_, v_a_7239_);
                if v_isShared_7242_ == 0 {
                    lean_ctor_set(v___x_7241_, 0, v___x_7243_);
                    v___x_7245_ = v___x_7241_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7246_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7246_, 0, v___x_7243_);
                    v___x_7245_ = v_reuseFailAlloc_7246_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7245_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_SolveByElim_saturateSymm___boxed(
    mut v_symm_7248_: *mut LeanObject,
    mut v_hyps_7249_: *mut LeanObject,
    mut v_a_7250_: *mut LeanObject,
    mut v_a_7251_: *mut LeanObject,
    mut v_a_7252_: *mut LeanObject,
    mut v_a_7253_: *mut LeanObject,
    mut v_a_7254_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_symm_boxed_7255_: u8 = 0;
    let mut v_res_7256_: *mut LeanObject = core::ptr::null_mut();
    v_symm_boxed_7255_ = (lean_unbox(v_symm_7248_) as u8);
    v_res_7256_ = l_Lean_Meta_SolveByElim_saturateSymm(
        v_symm_boxed_7255_,
        v_hyps_7249_,
        v_a_7250_,
        v_a_7251_,
        v_a_7252_,
        v_a_7253_,
    );
    lean_dec(v_a_7253_);
    lean_dec_ref(v_a_7252_);
    lean_dec(v_a_7251_);
    lean_dec_ref(v_a_7250_);
    return v_res_7256_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(
    mut v_as_7257_: *mut LeanObject,
    mut v_sz_7258_: usize,
    mut v_i_7259_: usize,
    mut v_b_7260_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7262_: u8 = 0;
    let mut v___x_7263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7267_: u8 = 0;
    let mut v___x_7268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7273_: usize = 0;
    let mut v___x_7274_: usize = 0;
    let mut v_reuseFailAlloc_7276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7279_: u8 = 0;
    let mut v___x_7280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7282_: u8 = 0;
    let mut v_unused_7283_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7262_ = lean_usize_dec_lt(v_i_7259_, v_sz_7258_);
                if v___x_7262_ == 0 {
                    v___x_7263_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_7263_, 0, v_b_7260_);
                    return v___x_7263_;
                } else {
                    v_snd_7264_ = lean_ctor_get(v_b_7260_, 1);
                    v_isSharedCheck_7282_ = (!lean_is_exclusive(v_b_7260_)) as u8;
                    if v_isSharedCheck_7282_ == 0 {
                        v_unused_7283_ = lean_ctor_get(v_b_7260_, 0);
                        lean_dec(v_unused_7283_);
                        v___x_7266_ = v_b_7260_;
                        v_isShared_7267_ = v_isSharedCheck_7282_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_7264_);
                        lean_dec(v_b_7260_);
                        v___x_7266_ = lean_box(0);
                        v_isShared_7267_ = v_isSharedCheck_7282_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7268_ = lean_box(0);
                v_a_7277_ = lean_array_uget_borrowed(v_as_7257_, v_i_7259_);
                if lean_obj_tag(v_a_7277_) == 0 {
                    v_a_7270_ = v_snd_7264_;
                    state = 2;
                    continue;
                } else {
                    v_val_7278_ = lean_ctor_get(v_a_7277_, 0);
                    v___x_7279_ = l_Lean_LocalDecl_isImplementationDetail(v_val_7278_);
                    if v___x_7279_ == 0 {
                        lean_inc(v_val_7278_);
                        v___x_7280_ = l_Lean_LocalDecl_toExpr(v_val_7278_);
                        v___x_7281_ = lean_array_push(v_snd_7264_, v___x_7280_);
                        v_a_7270_ = v___x_7281_;
                        state = 2;
                        continue;
                    } else {
                        v_a_7270_ = v_snd_7264_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_7267_ == 0 {
                    lean_ctor_set(v___x_7266_, 1, v_a_7270_);
                    lean_ctor_set(v___x_7266_, 0, v___x_7268_);
                    v___x_7272_ = v___x_7266_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7276_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7276_, 0, v___x_7268_);
                    lean_ctor_set(v_reuseFailAlloc_7276_, 1, v_a_7270_);
                    v___x_7272_ = v_reuseFailAlloc_7276_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_7273_ = 1usize;
                v___x_7274_ = lean_usize_add(v_i_7259_, v___x_7273_);
                v_i_7259_ = v___x_7274_;
                v_b_7260_ = v___x_7272_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg___boxed(
    mut v_as_7284_: *mut LeanObject,
    mut v_sz_7285_: *mut LeanObject,
    mut v_i_7286_: *mut LeanObject,
    mut v_b_7287_: *mut LeanObject,
    mut v___y_7288_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_7289_: usize = 0;
    let mut v_i_boxed_7290_: usize = 0;
    let mut v_res_7291_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_7289_ = lean_unbox_usize(v_sz_7285_);
    lean_dec(v_sz_7285_);
    v_i_boxed_7290_ = lean_unbox_usize(v_i_7286_);
    lean_dec(v_i_7286_);
    v_res_7291_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(v_as_7284_, v_sz_boxed_7289_, v_i_boxed_7290_, v_b_7287_);
    lean_dec_ref(v_as_7284_);
    return v_res_7291_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2(
    mut v_as_7292_: *mut LeanObject,
    mut v_sz_7293_: usize,
    mut v_i_7294_: usize,
    mut v_b_7295_: *mut LeanObject,
    mut v___y_7296_: *mut LeanObject,
    mut v___y_7297_: *mut LeanObject,
    mut v___y_7298_: *mut LeanObject,
    mut v___y_7299_: *mut LeanObject,
    mut v___y_7300_: *mut LeanObject,
    mut v___y_7301_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7303_: u8 = 0;
    let mut v___x_7304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7308_: u8 = 0;
    let mut v___x_7309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7314_: usize = 0;
    let mut v___x_7315_: usize = 0;
    let mut v___x_7316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7320_: u8 = 0;
    let mut v___x_7321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7323_: u8 = 0;
    let mut v_unused_7324_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7303_ = lean_usize_dec_lt(v_i_7294_, v_sz_7293_);
                if v___x_7303_ == 0 {
                    v___x_7304_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_7304_, 0, v_b_7295_);
                    return v___x_7304_;
                } else {
                    v_snd_7305_ = lean_ctor_get(v_b_7295_, 1);
                    v_isSharedCheck_7323_ = (!lean_is_exclusive(v_b_7295_)) as u8;
                    if v_isSharedCheck_7323_ == 0 {
                        v_unused_7324_ = lean_ctor_get(v_b_7295_, 0);
                        lean_dec(v_unused_7324_);
                        v___x_7307_ = v_b_7295_;
                        v_isShared_7308_ = v_isSharedCheck_7323_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_7305_);
                        lean_dec(v_b_7295_);
                        v___x_7307_ = lean_box(0);
                        v_isShared_7308_ = v_isSharedCheck_7323_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7309_ = lean_box(0);
                v_a_7318_ = lean_array_uget_borrowed(v_as_7292_, v_i_7294_);
                if lean_obj_tag(v_a_7318_) == 0 {
                    v_a_7311_ = v_snd_7305_;
                    state = 2;
                    continue;
                } else {
                    v_val_7319_ = lean_ctor_get(v_a_7318_, 0);
                    v___x_7320_ = l_Lean_LocalDecl_isImplementationDetail(v_val_7319_);
                    if v___x_7320_ == 0 {
                        lean_inc(v_val_7319_);
                        v___x_7321_ = l_Lean_LocalDecl_toExpr(v_val_7319_);
                        v___x_7322_ = lean_array_push(v_snd_7305_, v___x_7321_);
                        v_a_7311_ = v___x_7322_;
                        state = 2;
                        continue;
                    } else {
                        v_a_7311_ = v_snd_7305_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_7308_ == 0 {
                    lean_ctor_set(v___x_7307_, 1, v_a_7311_);
                    lean_ctor_set(v___x_7307_, 0, v___x_7309_);
                    v___x_7313_ = v___x_7307_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7317_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7317_, 0, v___x_7309_);
                    lean_ctor_set(v_reuseFailAlloc_7317_, 1, v_a_7311_);
                    v___x_7313_ = v_reuseFailAlloc_7317_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_7314_ = 1usize;
                v___x_7315_ = lean_usize_add(v_i_7294_, v___x_7314_);
                v___x_7316_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(v_as_7292_, v_sz_7293_, v___x_7315_, v___x_7313_);
                return v___x_7316_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2___boxed(
    mut v_as_7325_: *mut LeanObject,
    mut v_sz_7326_: *mut LeanObject,
    mut v_i_7327_: *mut LeanObject,
    mut v_b_7328_: *mut LeanObject,
    mut v___y_7329_: *mut LeanObject,
    mut v___y_7330_: *mut LeanObject,
    mut v___y_7331_: *mut LeanObject,
    mut v___y_7332_: *mut LeanObject,
    mut v___y_7333_: *mut LeanObject,
    mut v___y_7334_: *mut LeanObject,
    mut v___y_7335_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_7336_: usize = 0;
    let mut v_i_boxed_7337_: usize = 0;
    let mut v_res_7338_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_7336_ = lean_unbox_usize(v_sz_7326_);
    lean_dec(v_sz_7326_);
    v_i_boxed_7337_ = lean_unbox_usize(v_i_7327_);
    lean_dec(v_i_7327_);
    v_res_7338_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2(v_as_7325_, v_sz_boxed_7336_, v_i_boxed_7337_, v_b_7328_, v___y_7329_, v___y_7330_, v___y_7331_, v___y_7332_, v___y_7333_, v___y_7334_);
    lean_dec(v___y_7334_);
    lean_dec_ref(v___y_7333_);
    lean_dec(v___y_7332_);
    lean_dec_ref(v___y_7331_);
    lean_dec(v___y_7330_);
    lean_dec_ref(v___y_7329_);
    lean_dec_ref(v_as_7325_);
    return v_res_7338_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(
    mut v_as_7339_: *mut LeanObject,
    mut v_sz_7340_: usize,
    mut v_i_7341_: usize,
    mut v_b_7342_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7344_: u8 = 0;
    let mut v___x_7345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7349_: u8 = 0;
    let mut v___x_7350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7355_: usize = 0;
    let mut v___x_7356_: usize = 0;
    let mut v_reuseFailAlloc_7358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7361_: u8 = 0;
    let mut v___x_7362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7364_: u8 = 0;
    let mut v_unused_7365_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7344_ = lean_usize_dec_lt(v_i_7341_, v_sz_7340_);
                if v___x_7344_ == 0 {
                    v___x_7345_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_7345_, 0, v_b_7342_);
                    return v___x_7345_;
                } else {
                    v_snd_7346_ = lean_ctor_get(v_b_7342_, 1);
                    v_isSharedCheck_7364_ = (!lean_is_exclusive(v_b_7342_)) as u8;
                    if v_isSharedCheck_7364_ == 0 {
                        v_unused_7365_ = lean_ctor_get(v_b_7342_, 0);
                        lean_dec(v_unused_7365_);
                        v___x_7348_ = v_b_7342_;
                        v_isShared_7349_ = v_isSharedCheck_7364_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_7346_);
                        lean_dec(v_b_7342_);
                        v___x_7348_ = lean_box(0);
                        v_isShared_7349_ = v_isSharedCheck_7364_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7350_ = lean_box(0);
                v_a_7359_ = lean_array_uget_borrowed(v_as_7339_, v_i_7341_);
                if lean_obj_tag(v_a_7359_) == 0 {
                    v_a_7352_ = v_snd_7346_;
                    state = 2;
                    continue;
                } else {
                    v_val_7360_ = lean_ctor_get(v_a_7359_, 0);
                    v___x_7361_ = l_Lean_LocalDecl_isImplementationDetail(v_val_7360_);
                    if v___x_7361_ == 0 {
                        lean_inc(v_val_7360_);
                        v___x_7362_ = l_Lean_LocalDecl_toExpr(v_val_7360_);
                        v___x_7363_ = lean_array_push(v_snd_7346_, v___x_7362_);
                        v_a_7352_ = v___x_7363_;
                        state = 2;
                        continue;
                    } else {
                        v_a_7352_ = v_snd_7346_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_7349_ == 0 {
                    lean_ctor_set(v___x_7348_, 1, v_a_7352_);
                    lean_ctor_set(v___x_7348_, 0, v___x_7350_);
                    v___x_7354_ = v___x_7348_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7358_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7358_, 0, v___x_7350_);
                    lean_ctor_set(v_reuseFailAlloc_7358_, 1, v_a_7352_);
                    v___x_7354_ = v_reuseFailAlloc_7358_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_7355_ = 1usize;
                v___x_7356_ = lean_usize_add(v_i_7341_, v___x_7355_);
                v_i_7341_ = v___x_7356_;
                v_b_7342_ = v___x_7354_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg___boxed(
    mut v_as_7366_: *mut LeanObject,
    mut v_sz_7367_: *mut LeanObject,
    mut v_i_7368_: *mut LeanObject,
    mut v_b_7369_: *mut LeanObject,
    mut v___y_7370_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_7371_: usize = 0;
    let mut v_i_boxed_7372_: usize = 0;
    let mut v_res_7373_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_7371_ = lean_unbox_usize(v_sz_7367_);
    lean_dec(v_sz_7367_);
    v_i_boxed_7372_ = lean_unbox_usize(v_i_7368_);
    lean_dec(v_i_7368_);
    v_res_7373_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_as_7366_, v_sz_boxed_7371_, v_i_boxed_7372_, v_b_7369_);
    lean_dec_ref(v_as_7366_);
    return v_res_7373_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3(
    mut v_as_7374_: *mut LeanObject,
    mut v_sz_7375_: usize,
    mut v_i_7376_: usize,
    mut v_b_7377_: *mut LeanObject,
    mut v___y_7378_: *mut LeanObject,
    mut v___y_7379_: *mut LeanObject,
    mut v___y_7380_: *mut LeanObject,
    mut v___y_7381_: *mut LeanObject,
    mut v___y_7382_: *mut LeanObject,
    mut v___y_7383_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7385_: u8 = 0;
    let mut v___x_7386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7390_: u8 = 0;
    let mut v___x_7391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7396_: usize = 0;
    let mut v___x_7397_: usize = 0;
    let mut v___x_7398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7402_: u8 = 0;
    let mut v___x_7403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7405_: u8 = 0;
    let mut v_unused_7406_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7385_ = lean_usize_dec_lt(v_i_7376_, v_sz_7375_);
                if v___x_7385_ == 0 {
                    v___x_7386_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_7386_, 0, v_b_7377_);
                    return v___x_7386_;
                } else {
                    v_snd_7387_ = lean_ctor_get(v_b_7377_, 1);
                    v_isSharedCheck_7405_ = (!lean_is_exclusive(v_b_7377_)) as u8;
                    if v_isSharedCheck_7405_ == 0 {
                        v_unused_7406_ = lean_ctor_get(v_b_7377_, 0);
                        lean_dec(v_unused_7406_);
                        v___x_7389_ = v_b_7377_;
                        v_isShared_7390_ = v_isSharedCheck_7405_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_7387_);
                        lean_dec(v_b_7377_);
                        v___x_7389_ = lean_box(0);
                        v_isShared_7390_ = v_isSharedCheck_7405_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7391_ = lean_box(0);
                v_a_7400_ = lean_array_uget_borrowed(v_as_7374_, v_i_7376_);
                if lean_obj_tag(v_a_7400_) == 0 {
                    v_a_7393_ = v_snd_7387_;
                    state = 2;
                    continue;
                } else {
                    v_val_7401_ = lean_ctor_get(v_a_7400_, 0);
                    v___x_7402_ = l_Lean_LocalDecl_isImplementationDetail(v_val_7401_);
                    if v___x_7402_ == 0 {
                        lean_inc(v_val_7401_);
                        v___x_7403_ = l_Lean_LocalDecl_toExpr(v_val_7401_);
                        v___x_7404_ = lean_array_push(v_snd_7387_, v___x_7403_);
                        v_a_7393_ = v___x_7404_;
                        state = 2;
                        continue;
                    } else {
                        v_a_7393_ = v_snd_7387_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_7390_ == 0 {
                    lean_ctor_set(v___x_7389_, 1, v_a_7393_);
                    lean_ctor_set(v___x_7389_, 0, v___x_7391_);
                    v___x_7395_ = v___x_7389_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7399_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7399_, 0, v___x_7391_);
                    lean_ctor_set(v_reuseFailAlloc_7399_, 1, v_a_7393_);
                    v___x_7395_ = v_reuseFailAlloc_7399_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_7396_ = 1usize;
                v___x_7397_ = lean_usize_add(v_i_7376_, v___x_7396_);
                v___x_7398_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_as_7374_, v_sz_7375_, v___x_7397_, v___x_7395_);
                return v___x_7398_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3___boxed(
    mut v_as_7407_: *mut LeanObject,
    mut v_sz_7408_: *mut LeanObject,
    mut v_i_7409_: *mut LeanObject,
    mut v_b_7410_: *mut LeanObject,
    mut v___y_7411_: *mut LeanObject,
    mut v___y_7412_: *mut LeanObject,
    mut v___y_7413_: *mut LeanObject,
    mut v___y_7414_: *mut LeanObject,
    mut v___y_7415_: *mut LeanObject,
    mut v___y_7416_: *mut LeanObject,
    mut v___y_7417_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_7418_: usize = 0;
    let mut v_i_boxed_7419_: usize = 0;
    let mut v_res_7420_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_7418_ = lean_unbox_usize(v_sz_7408_);
    lean_dec(v_sz_7408_);
    v_i_boxed_7419_ = lean_unbox_usize(v_i_7409_);
    lean_dec(v_i_7409_);
    v_res_7420_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3(v_as_7407_, v_sz_boxed_7418_, v_i_boxed_7419_, v_b_7410_, v___y_7411_, v___y_7412_, v___y_7413_, v___y_7414_, v___y_7415_, v___y_7416_);
    lean_dec(v___y_7416_);
    lean_dec_ref(v___y_7415_);
    lean_dec(v___y_7414_);
    lean_dec_ref(v___y_7413_);
    lean_dec(v___y_7412_);
    lean_dec_ref(v___y_7411_);
    lean_dec_ref(v_as_7407_);
    return v_res_7420_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(
    mut v_init_7421_: *mut LeanObject,
    mut v_n_7422_: *mut LeanObject,
    mut v_b_7423_: *mut LeanObject,
    mut v___y_7424_: *mut LeanObject,
    mut v___y_7425_: *mut LeanObject,
    mut v___y_7426_: *mut LeanObject,
    mut v___y_7427_: *mut LeanObject,
    mut v___y_7428_: *mut LeanObject,
    mut v___y_7429_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cs_7431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_7434_: usize = 0;
    let mut v___x_7435_: usize = 0;
    let mut v___x_7436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7440_: u8 = 0;
    let mut v_fst_7441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7451_: u8 = 0;
    let mut v_a_7452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7455_: u8 = 0;
    let mut v___x_7457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7459_: u8 = 0;
    let mut v_vs_7460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_7463_: usize = 0;
    let mut v___x_7464_: usize = 0;
    let mut v___x_7465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7469_: u8 = 0;
    let mut v_fst_7470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7480_: u8 = 0;
    let mut v_a_7481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7484_: u8 = 0;
    let mut v___x_7486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7488_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_n_7422_) == 0 {
                    v_cs_7431_ = lean_ctor_get(v_n_7422_, 0);
                    v___x_7432_ = lean_box(0);
                    v___x_7433_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_7433_, 0, v___x_7432_);
                    lean_ctor_set(v___x_7433_, 1, v_b_7423_);
                    v_sz_7434_ = lean_array_size(v_cs_7431_);
                    v___x_7435_ = 0usize;
                    v___x_7436_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2(v_init_7421_, v_cs_7431_, v_sz_7434_, v___x_7435_, v___x_7433_, v___y_7424_, v___y_7425_, v___y_7426_, v___y_7427_, v___y_7428_, v___y_7429_);
                    if lean_obj_tag(v___x_7436_) == 0 {
                        v_a_7437_ = lean_ctor_get(v___x_7436_, 0);
                        v_isSharedCheck_7451_ = (!lean_is_exclusive(v___x_7436_)) as u8;
                        if v_isSharedCheck_7451_ == 0 {
                            v___x_7439_ = v___x_7436_;
                            v_isShared_7440_ = v_isSharedCheck_7451_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_7437_);
                            lean_dec(v___x_7436_);
                            v___x_7439_ = lean_box(0);
                            v_isShared_7440_ = v_isSharedCheck_7451_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_7452_ = lean_ctor_get(v___x_7436_, 0);
                        v_isSharedCheck_7459_ = (!lean_is_exclusive(v___x_7436_)) as u8;
                        if v_isSharedCheck_7459_ == 0 {
                            v___x_7454_ = v___x_7436_;
                            v_isShared_7455_ = v_isSharedCheck_7459_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_7452_);
                            lean_dec(v___x_7436_);
                            v___x_7454_ = lean_box(0);
                            v_isShared_7455_ = v_isSharedCheck_7459_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_7460_ = lean_ctor_get(v_n_7422_, 0);
                    v___x_7461_ = lean_box(0);
                    v___x_7462_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_7462_, 0, v___x_7461_);
                    lean_ctor_set(v___x_7462_, 1, v_b_7423_);
                    v_sz_7463_ = lean_array_size(v_vs_7460_);
                    v___x_7464_ = 0usize;
                    v___x_7465_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3(v_vs_7460_, v_sz_7463_, v___x_7464_, v___x_7462_, v___y_7424_, v___y_7425_, v___y_7426_, v___y_7427_, v___y_7428_, v___y_7429_);
                    if lean_obj_tag(v___x_7465_) == 0 {
                        v_a_7466_ = lean_ctor_get(v___x_7465_, 0);
                        v_isSharedCheck_7480_ = (!lean_is_exclusive(v___x_7465_)) as u8;
                        if v_isSharedCheck_7480_ == 0 {
                            v___x_7468_ = v___x_7465_;
                            v_isShared_7469_ = v_isSharedCheck_7480_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_7466_);
                            lean_dec(v___x_7465_);
                            v___x_7468_ = lean_box(0);
                            v_isShared_7469_ = v_isSharedCheck_7480_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_7481_ = lean_ctor_get(v___x_7465_, 0);
                        v_isSharedCheck_7488_ = (!lean_is_exclusive(v___x_7465_)) as u8;
                        if v_isSharedCheck_7488_ == 0 {
                            v___x_7483_ = v___x_7465_;
                            v_isShared_7484_ = v_isSharedCheck_7488_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_7481_);
                            lean_dec(v___x_7465_);
                            v___x_7483_ = lean_box(0);
                            v_isShared_7484_ = v_isSharedCheck_7488_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_7441_ = lean_ctor_get(v_a_7437_, 0);
                if lean_obj_tag(v_fst_7441_) == 0 {
                    v_snd_7442_ = lean_ctor_get(v_a_7437_, 1);
                    lean_inc(v_snd_7442_);
                    lean_dec(v_a_7437_);
                    v___x_7443_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_7443_, 0, v_snd_7442_);
                    if v_isShared_7440_ == 0 {
                        lean_ctor_set(v___x_7439_, 0, v___x_7443_);
                        v___x_7445_ = v___x_7439_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_7446_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7446_, 0, v___x_7443_);
                        v___x_7445_ = v_reuseFailAlloc_7446_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_7441_);
                    lean_dec(v_a_7437_);
                    v_val_7447_ = lean_ctor_get(v_fst_7441_, 0);
                    lean_inc(v_val_7447_);
                    lean_dec_ref_known(v_fst_7441_, 1);
                    if v_isShared_7440_ == 0 {
                        lean_ctor_set(v___x_7439_, 0, v_val_7447_);
                        v___x_7449_ = v___x_7439_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_7450_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7450_, 0, v_val_7447_);
                        v___x_7449_ = v_reuseFailAlloc_7450_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_7445_;
            }
            3 => {
                return v___x_7449_;
            }
            4 => {
                if v_isShared_7455_ == 0 {
                    v___x_7457_ = v___x_7454_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7458_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7458_, 0, v_a_7452_);
                    v___x_7457_ = v_reuseFailAlloc_7458_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_7457_;
            }
            6 => {
                v_fst_7470_ = lean_ctor_get(v_a_7466_, 0);
                if lean_obj_tag(v_fst_7470_) == 0 {
                    v_snd_7471_ = lean_ctor_get(v_a_7466_, 1);
                    lean_inc(v_snd_7471_);
                    lean_dec(v_a_7466_);
                    v___x_7472_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_7472_, 0, v_snd_7471_);
                    if v_isShared_7469_ == 0 {
                        lean_ctor_set(v___x_7468_, 0, v___x_7472_);
                        v___x_7474_ = v___x_7468_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_7475_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7475_, 0, v___x_7472_);
                        v___x_7474_ = v_reuseFailAlloc_7475_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_7470_);
                    lean_dec(v_a_7466_);
                    v_val_7476_ = lean_ctor_get(v_fst_7470_, 0);
                    lean_inc(v_val_7476_);
                    lean_dec_ref_known(v_fst_7470_, 1);
                    if v_isShared_7469_ == 0 {
                        lean_ctor_set(v___x_7468_, 0, v_val_7476_);
                        v___x_7478_ = v___x_7468_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_7479_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7479_, 0, v_val_7476_);
                        v___x_7478_ = v_reuseFailAlloc_7479_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_7474_;
            }
            8 => {
                return v___x_7478_;
            }
            9 => {
                if v_isShared_7484_ == 0 {
                    v___x_7486_ = v___x_7483_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_7487_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7487_, 0, v_a_7481_);
                    v___x_7486_ = v_reuseFailAlloc_7487_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_7486_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2(
    mut v_init_7489_: *mut LeanObject,
    mut v_as_7490_: *mut LeanObject,
    mut v_sz_7491_: usize,
    mut v_i_7492_: usize,
    mut v_b_7493_: *mut LeanObject,
    mut v___y_7494_: *mut LeanObject,
    mut v___y_7495_: *mut LeanObject,
    mut v___y_7496_: *mut LeanObject,
    mut v___y_7497_: *mut LeanObject,
    mut v___y_7498_: *mut LeanObject,
    mut v___y_7499_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7501_: u8 = 0;
    let mut v___x_7502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7506_: u8 = 0;
    let mut v_a_7507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7512_: u8 = 0;
    let mut v___x_7513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7524_: usize = 0;
    let mut v___x_7525_: usize = 0;
    let mut v_reuseFailAlloc_7527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7528_: u8 = 0;
    let mut v_a_7529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7532_: u8 = 0;
    let mut v___x_7534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7536_: u8 = 0;
    let mut v_isSharedCheck_7537_: u8 = 0;
    let mut v_unused_7538_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7501_ = lean_usize_dec_lt(v_i_7492_, v_sz_7491_);
                if v___x_7501_ == 0 {
                    v___x_7502_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_7502_, 0, v_b_7493_);
                    return v___x_7502_;
                } else {
                    v_snd_7503_ = lean_ctor_get(v_b_7493_, 1);
                    v_isSharedCheck_7537_ = (!lean_is_exclusive(v_b_7493_)) as u8;
                    if v_isSharedCheck_7537_ == 0 {
                        v_unused_7538_ = lean_ctor_get(v_b_7493_, 0);
                        lean_dec(v_unused_7538_);
                        v___x_7505_ = v_b_7493_;
                        v_isShared_7506_ = v_isSharedCheck_7537_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_7503_);
                        lean_dec(v_b_7493_);
                        v___x_7505_ = lean_box(0);
                        v_isShared_7506_ = v_isSharedCheck_7537_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_7507_ = lean_array_uget_borrowed(v_as_7490_, v_i_7492_);
                lean_inc(v_snd_7503_);
                v___x_7508_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(v_init_7489_, v_a_7507_, v_snd_7503_, v___y_7494_, v___y_7495_, v___y_7496_, v___y_7497_, v___y_7498_, v___y_7499_);
                if lean_obj_tag(v___x_7508_) == 0 {
                    v_a_7509_ = lean_ctor_get(v___x_7508_, 0);
                    v_isSharedCheck_7528_ = (!lean_is_exclusive(v___x_7508_)) as u8;
                    if v_isSharedCheck_7528_ == 0 {
                        v___x_7511_ = v___x_7508_;
                        v_isShared_7512_ = v_isSharedCheck_7528_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_7509_);
                        lean_dec(v___x_7508_);
                        v___x_7511_ = lean_box(0);
                        v_isShared_7512_ = v_isSharedCheck_7528_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_7505_);
                    lean_dec(v_snd_7503_);
                    v_a_7529_ = lean_ctor_get(v___x_7508_, 0);
                    v_isSharedCheck_7536_ = (!lean_is_exclusive(v___x_7508_)) as u8;
                    if v_isSharedCheck_7536_ == 0 {
                        v___x_7531_ = v___x_7508_;
                        v_isShared_7532_ = v_isSharedCheck_7536_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_7529_);
                        lean_dec(v___x_7508_);
                        v___x_7531_ = lean_box(0);
                        v_isShared_7532_ = v_isSharedCheck_7536_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_7509_) == 0 {
                    v___x_7513_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_7513_, 0, v_a_7509_);
                    if v_isShared_7506_ == 0 {
                        lean_ctor_set(v___x_7505_, 0, v___x_7513_);
                        v___x_7515_ = v___x_7505_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_7519_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7519_, 0, v___x_7513_);
                        lean_ctor_set(v_reuseFailAlloc_7519_, 1, v_snd_7503_);
                        v___x_7515_ = v_reuseFailAlloc_7519_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_7511_);
                    lean_dec(v_snd_7503_);
                    v_a_7520_ = lean_ctor_get(v_a_7509_, 0);
                    lean_inc(v_a_7520_);
                    lean_dec_ref_known(v_a_7509_, 1);
                    v___x_7521_ = lean_box(0);
                    if v_isShared_7506_ == 0 {
                        lean_ctor_set(v___x_7505_, 1, v_a_7520_);
                        lean_ctor_set(v___x_7505_, 0, v___x_7521_);
                        v___x_7523_ = v___x_7505_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_7527_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7527_, 0, v___x_7521_);
                        lean_ctor_set(v_reuseFailAlloc_7527_, 1, v_a_7520_);
                        v___x_7523_ = v_reuseFailAlloc_7527_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_7512_ == 0 {
                    lean_ctor_set(v___x_7511_, 0, v___x_7515_);
                    v___x_7517_ = v___x_7511_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7518_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7518_, 0, v___x_7515_);
                    v___x_7517_ = v_reuseFailAlloc_7518_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7517_;
            }
            5 => {
                v___x_7524_ = 1usize;
                v___x_7525_ = lean_usize_add(v_i_7492_, v___x_7524_);
                v_i_7492_ = v___x_7525_;
                v_b_7493_ = v___x_7523_;
                state = 0;
                continue;
            }
            6 => {
                if v_isShared_7532_ == 0 {
                    v___x_7534_ = v___x_7531_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_7535_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7535_, 0, v_a_7529_);
                    v___x_7534_ = v_reuseFailAlloc_7535_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_7534_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2___boxed(
    mut v_init_7539_: *mut LeanObject,
    mut v_as_7540_: *mut LeanObject,
    mut v_sz_7541_: *mut LeanObject,
    mut v_i_7542_: *mut LeanObject,
    mut v_b_7543_: *mut LeanObject,
    mut v___y_7544_: *mut LeanObject,
    mut v___y_7545_: *mut LeanObject,
    mut v___y_7546_: *mut LeanObject,
    mut v___y_7547_: *mut LeanObject,
    mut v___y_7548_: *mut LeanObject,
    mut v___y_7549_: *mut LeanObject,
    mut v___y_7550_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_7551_: usize = 0;
    let mut v_i_boxed_7552_: usize = 0;
    let mut v_res_7553_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_7551_ = lean_unbox_usize(v_sz_7541_);
    lean_dec(v_sz_7541_);
    v_i_boxed_7552_ = lean_unbox_usize(v_i_7542_);
    lean_dec(v_i_7542_);
    v_res_7553_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2(v_init_7539_, v_as_7540_, v_sz_boxed_7551_, v_i_boxed_7552_, v_b_7543_, v___y_7544_, v___y_7545_, v___y_7546_, v___y_7547_, v___y_7548_, v___y_7549_);
    lean_dec(v___y_7549_);
    lean_dec_ref(v___y_7548_);
    lean_dec(v___y_7547_);
    lean_dec_ref(v___y_7546_);
    lean_dec(v___y_7545_);
    lean_dec_ref(v___y_7544_);
    lean_dec_ref(v_as_7540_);
    lean_dec_ref(v_init_7539_);
    return v_res_7553_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1___boxed(
    mut v_init_7554_: *mut LeanObject,
    mut v_n_7555_: *mut LeanObject,
    mut v_b_7556_: *mut LeanObject,
    mut v___y_7557_: *mut LeanObject,
    mut v___y_7558_: *mut LeanObject,
    mut v___y_7559_: *mut LeanObject,
    mut v___y_7560_: *mut LeanObject,
    mut v___y_7561_: *mut LeanObject,
    mut v___y_7562_: *mut LeanObject,
    mut v___y_7563_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7564_: *mut LeanObject = core::ptr::null_mut();
    v_res_7564_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(v_init_7554_, v_n_7555_, v_b_7556_, v___y_7557_, v___y_7558_, v___y_7559_, v___y_7560_, v___y_7561_, v___y_7562_);
    lean_dec(v___y_7562_);
    lean_dec_ref(v___y_7561_);
    lean_dec(v___y_7560_);
    lean_dec_ref(v___y_7559_);
    lean_dec(v___y_7558_);
    lean_dec_ref(v___y_7557_);
    lean_dec_ref(v_n_7555_);
    lean_dec_ref(v_init_7554_);
    return v_res_7564_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0(
    mut v_t_7565_: *mut LeanObject,
    mut v_init_7566_: *mut LeanObject,
    mut v___y_7567_: *mut LeanObject,
    mut v___y_7568_: *mut LeanObject,
    mut v___y_7569_: *mut LeanObject,
    mut v___y_7570_: *mut LeanObject,
    mut v___y_7571_: *mut LeanObject,
    mut v___y_7572_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_root_7574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_7575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7580_: u8 = 0;
    let mut v_a_7581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_7588_: usize = 0;
    let mut v___x_7589_: usize = 0;
    let mut v___x_7590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7594_: u8 = 0;
    let mut v_fst_7595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7604_: u8 = 0;
    let mut v_a_7605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7608_: u8 = 0;
    let mut v___x_7610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7612_: u8 = 0;
    let mut v_isSharedCheck_7613_: u8 = 0;
    let mut v_a_7614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7617_: u8 = 0;
    let mut v___x_7619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7621_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_7574_ = lean_ctor_get(v_t_7565_, 0);
                v_tail_7575_ = lean_ctor_get(v_t_7565_, 1);
                lean_inc_ref(v_init_7566_);
                v___x_7576_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(v_init_7566_, v_root_7574_, v_init_7566_, v___y_7567_, v___y_7568_, v___y_7569_, v___y_7570_, v___y_7571_, v___y_7572_);
                lean_dec_ref(v_init_7566_);
                if lean_obj_tag(v___x_7576_) == 0 {
                    v_a_7577_ = lean_ctor_get(v___x_7576_, 0);
                    v_isSharedCheck_7613_ = (!lean_is_exclusive(v___x_7576_)) as u8;
                    if v_isSharedCheck_7613_ == 0 {
                        v___x_7579_ = v___x_7576_;
                        v_isShared_7580_ = v_isSharedCheck_7613_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7577_);
                        lean_dec(v___x_7576_);
                        v___x_7579_ = lean_box(0);
                        v_isShared_7580_ = v_isSharedCheck_7613_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_7614_ = lean_ctor_get(v___x_7576_, 0);
                    v_isSharedCheck_7621_ = (!lean_is_exclusive(v___x_7576_)) as u8;
                    if v_isSharedCheck_7621_ == 0 {
                        v___x_7616_ = v___x_7576_;
                        v_isShared_7617_ = v_isSharedCheck_7621_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_7614_);
                        lean_dec(v___x_7576_);
                        v___x_7616_ = lean_box(0);
                        v_isShared_7617_ = v_isSharedCheck_7621_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_7577_) == 0 {
                    v_a_7581_ = lean_ctor_get(v_a_7577_, 0);
                    lean_inc(v_a_7581_);
                    lean_dec_ref_known(v_a_7577_, 1);
                    if v_isShared_7580_ == 0 {
                        lean_ctor_set(v___x_7579_, 0, v_a_7581_);
                        v___x_7583_ = v___x_7579_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_7584_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7584_, 0, v_a_7581_);
                        v___x_7583_ = v_reuseFailAlloc_7584_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_7579_);
                    v_a_7585_ = lean_ctor_get(v_a_7577_, 0);
                    lean_inc(v_a_7585_);
                    lean_dec_ref_known(v_a_7577_, 1);
                    v___x_7586_ = lean_box(0);
                    v___x_7587_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_7587_, 0, v___x_7586_);
                    lean_ctor_set(v___x_7587_, 1, v_a_7585_);
                    v_sz_7588_ = lean_array_size(v_tail_7575_);
                    v___x_7589_ = 0usize;
                    v___x_7590_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2(v_tail_7575_, v_sz_7588_, v___x_7589_, v___x_7587_, v___y_7567_, v___y_7568_, v___y_7569_, v___y_7570_, v___y_7571_, v___y_7572_);
                    if lean_obj_tag(v___x_7590_) == 0 {
                        v_a_7591_ = lean_ctor_get(v___x_7590_, 0);
                        v_isSharedCheck_7604_ = (!lean_is_exclusive(v___x_7590_)) as u8;
                        if v_isSharedCheck_7604_ == 0 {
                            v___x_7593_ = v___x_7590_;
                            v_isShared_7594_ = v_isSharedCheck_7604_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_7591_);
                            lean_dec(v___x_7590_);
                            v___x_7593_ = lean_box(0);
                            v_isShared_7594_ = v_isSharedCheck_7604_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_7605_ = lean_ctor_get(v___x_7590_, 0);
                        v_isSharedCheck_7612_ = (!lean_is_exclusive(v___x_7590_)) as u8;
                        if v_isSharedCheck_7612_ == 0 {
                            v___x_7607_ = v___x_7590_;
                            v_isShared_7608_ = v_isSharedCheck_7612_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_7605_);
                            lean_dec(v___x_7590_);
                            v___x_7607_ = lean_box(0);
                            v_isShared_7608_ = v_isSharedCheck_7612_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_7583_;
            }
            3 => {
                v_fst_7595_ = lean_ctor_get(v_a_7591_, 0);
                if lean_obj_tag(v_fst_7595_) == 0 {
                    v_snd_7596_ = lean_ctor_get(v_a_7591_, 1);
                    lean_inc(v_snd_7596_);
                    lean_dec(v_a_7591_);
                    if v_isShared_7594_ == 0 {
                        lean_ctor_set(v___x_7593_, 0, v_snd_7596_);
                        v___x_7598_ = v___x_7593_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_7599_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7599_, 0, v_snd_7596_);
                        v___x_7598_ = v_reuseFailAlloc_7599_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_7595_);
                    lean_dec(v_a_7591_);
                    v_val_7600_ = lean_ctor_get(v_fst_7595_, 0);
                    lean_inc(v_val_7600_);
                    lean_dec_ref_known(v_fst_7595_, 1);
                    if v_isShared_7594_ == 0 {
                        lean_ctor_set(v___x_7593_, 0, v_val_7600_);
                        v___x_7602_ = v___x_7593_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_7603_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7603_, 0, v_val_7600_);
                        v___x_7602_ = v_reuseFailAlloc_7603_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_7598_;
            }
            5 => {
                return v___x_7602_;
            }
            6 => {
                if v_isShared_7608_ == 0 {
                    v___x_7610_ = v___x_7607_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_7611_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7611_, 0, v_a_7605_);
                    v___x_7610_ = v_reuseFailAlloc_7611_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_7610_;
            }
            8 => {
                if v_isShared_7617_ == 0 {
                    v___x_7619_ = v___x_7616_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_7620_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7620_, 0, v_a_7614_);
                    v___x_7619_ = v_reuseFailAlloc_7620_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_7619_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0___boxed(
    mut v_t_7622_: *mut LeanObject,
    mut v_init_7623_: *mut LeanObject,
    mut v___y_7624_: *mut LeanObject,
    mut v___y_7625_: *mut LeanObject,
    mut v___y_7626_: *mut LeanObject,
    mut v___y_7627_: *mut LeanObject,
    mut v___y_7628_: *mut LeanObject,
    mut v___y_7629_: *mut LeanObject,
    mut v___y_7630_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7631_: *mut LeanObject = core::ptr::null_mut();
    v_res_7631_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0(v_t_7622_, v_init_7623_, v___y_7624_, v___y_7625_, v___y_7626_, v___y_7627_, v___y_7628_, v___y_7629_);
    lean_dec(v___y_7629_);
    lean_dec_ref(v___y_7628_);
    lean_dec(v___y_7627_);
    lean_dec_ref(v___y_7626_);
    lean_dec(v___y_7625_);
    lean_dec_ref(v___y_7624_);
    lean_dec_ref(v_t_7622_);
    return v_res_7631_;
}
pub unsafe fn l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(
    mut v___y_7634_: *mut LeanObject,
    mut v___y_7635_: *mut LeanObject,
    mut v___y_7636_: *mut LeanObject,
    mut v___y_7637_: *mut LeanObject,
    mut v___y_7638_: *mut LeanObject,
    mut v___y_7639_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lctx_7641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_7642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hs_7643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7644_: *mut LeanObject = core::ptr::null_mut();
    v_lctx_7641_ = lean_ctor_get(v___y_7636_, 2);
    v_decls_7642_ = lean_ctor_get(v_lctx_7641_, 1);
    v_hs_7643_ = l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0___closed__0;
    v___x_7644_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0(v_decls_7642_, v_hs_7643_, v___y_7634_, v___y_7635_, v___y_7636_, v___y_7637_, v___y_7638_, v___y_7639_);
    return v___x_7644_;
}
pub unsafe fn l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0___boxed(
    mut v___y_7645_: *mut LeanObject,
    mut v___y_7646_: *mut LeanObject,
    mut v___y_7647_: *mut LeanObject,
    mut v___y_7648_: *mut LeanObject,
    mut v___y_7649_: *mut LeanObject,
    mut v___y_7650_: *mut LeanObject,
    mut v___y_7651_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7652_: *mut LeanObject = core::ptr::null_mut();
    v_res_7652_ = l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(
        v___y_7645_,
        v___y_7646_,
        v___y_7647_,
        v___y_7648_,
        v___y_7649_,
        v___y_7650_,
    );
    lean_dec(v___y_7650_);
    lean_dec_ref(v___y_7649_);
    lean_dec(v___y_7648_);
    lean_dec_ref(v___y_7647_);
    lean_dec(v___y_7646_);
    lean_dec_ref(v___y_7645_);
    return v_res_7652_;
}
pub unsafe fn l_Lean_MVarId_applyRules___lam__0(
    mut v_only_7653_: u8,
    mut v_cfg_7654_: *mut LeanObject,
    mut v___y_7655_: *mut LeanObject,
    mut v___y_7656_: *mut LeanObject,
    mut v___y_7657_: *mut LeanObject,
    mut v___y_7658_: *mut LeanObject,
    mut v___y_7659_: *mut LeanObject,
    mut v___y_7660_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplyRulesConfig_7663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_symm_7665_: u8 = 0;
    let mut v___x_7666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7671_: u8 = 0;
    let mut v___x_7673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7675_: u8 = 0;
    let mut v___x_7676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7677_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_only_7653_ == 0 {
                    v___x_7662_ = l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(
                        v___y_7655_,
                        v___y_7656_,
                        v___y_7657_,
                        v___y_7658_,
                        v___y_7659_,
                        v___y_7660_,
                    );
                    if lean_obj_tag(v___x_7662_) == 0 {
                        v_toApplyRulesConfig_7663_ = lean_ctor_get(v_cfg_7654_, 0);
                        v_a_7664_ = lean_ctor_get(v___x_7662_, 0);
                        lean_inc(v_a_7664_);
                        lean_dec_ref_known(v___x_7662_, 1);
                        v_symm_7665_ = lean_ctor_get_uint8(
                            v_toApplyRulesConfig_7663_,
                            (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                        );
                        v___x_7666_ = lean_array_to_list(v_a_7664_);
                        v___x_7667_ = l_Lean_Meta_SolveByElim_saturateSymm(
                            v_symm_7665_,
                            v___x_7666_,
                            v___y_7657_,
                            v___y_7658_,
                            v___y_7659_,
                            v___y_7660_,
                        );
                        return v___x_7667_;
                    } else {
                        v_a_7668_ = lean_ctor_get(v___x_7662_, 0);
                        v_isSharedCheck_7675_ = (!lean_is_exclusive(v___x_7662_)) as u8;
                        if v_isSharedCheck_7675_ == 0 {
                            v___x_7670_ = v___x_7662_;
                            v_isShared_7671_ = v_isSharedCheck_7675_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_7668_);
                            lean_dec(v___x_7662_);
                            v___x_7670_ = lean_box(0);
                            v_isShared_7671_ = v_isSharedCheck_7675_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v___x_7676_ = lean_box(0);
                    v___x_7677_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_7677_, 0, v___x_7676_);
                    return v___x_7677_;
                }
            }
            1 => {
                if v_isShared_7671_ == 0 {
                    v___x_7673_ = v___x_7670_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7674_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7674_, 0, v_a_7668_);
                    v___x_7673_ = v_reuseFailAlloc_7674_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7673_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_applyRules___lam__0___boxed(
    mut v_only_7678_: *mut LeanObject,
    mut v_cfg_7679_: *mut LeanObject,
    mut v___y_7680_: *mut LeanObject,
    mut v___y_7681_: *mut LeanObject,
    mut v___y_7682_: *mut LeanObject,
    mut v___y_7683_: *mut LeanObject,
    mut v___y_7684_: *mut LeanObject,
    mut v___y_7685_: *mut LeanObject,
    mut v___y_7686_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_only_boxed_7687_: u8 = 0;
    let mut v_res_7688_: *mut LeanObject = core::ptr::null_mut();
    v_only_boxed_7687_ = (lean_unbox(v_only_7678_) as u8);
    v_res_7688_ = l_Lean_MVarId_applyRules___lam__0(
        v_only_boxed_7687_,
        v_cfg_7679_,
        v___y_7680_,
        v___y_7681_,
        v___y_7682_,
        v___y_7683_,
        v___y_7684_,
        v___y_7685_,
    );
    lean_dec(v___y_7685_);
    lean_dec_ref(v___y_7684_);
    lean_dec(v___y_7683_);
    lean_dec_ref(v___y_7682_);
    lean_dec(v___y_7681_);
    lean_dec_ref(v___y_7680_);
    lean_dec_ref(v_cfg_7679_);
    return v_res_7688_;
}
pub unsafe fn l_Lean_MVarId_applyRules(
    mut v_cfg_7689_: *mut LeanObject,
    mut v_lemmas_7690_: *mut LeanObject,
    mut v_only_7691_: u8,
    mut v_g_7692_: *mut LeanObject,
    mut v_a_7693_: *mut LeanObject,
    mut v_a_7694_: *mut LeanObject,
    mut v_a_7695_: *mut LeanObject,
    mut v_a_7696_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplyRulesConfig_7698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_intro_7699_: u8 = 0;
    let mut v_constructor_7700_: u8 = 0;
    let mut v_suggestions_7701_: u8 = 0;
    let mut v___x_7703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7704_: u8 = 0;
    let mut v___x_7705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctx_7706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7707_: u8 = 0;
    let mut v___x_7709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7714_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplyRulesConfig_7698_ = lean_ctor_get(v_cfg_7689_, 0);
                v_intro_7699_ = lean_ctor_get_uint8(
                    v_cfg_7689_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                );
                v_constructor_7700_ = lean_ctor_get_uint8(
                    v_cfg_7689_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 2) as u32,
                );
                v_suggestions_7701_ = lean_ctor_get_uint8(
                    v_cfg_7689_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 3) as u32,
                );
                v_isSharedCheck_7714_ = (!lean_is_exclusive(v_cfg_7689_)) as u8;
                if v_isSharedCheck_7714_ == 0 {
                    v___x_7703_ = v_cfg_7689_;
                    v_isShared_7704_ = v_isSharedCheck_7714_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toApplyRulesConfig_7698_);
                    lean_dec(v_cfg_7689_);
                    v___x_7703_ = lean_box(0);
                    v_isShared_7704_ = v_isSharedCheck_7714_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7705_ = lean_box((v_only_7691_) as usize);
                v_ctx_7706_ = lean_alloc_closure(
                    l_Lean_MVarId_applyRules___lam__0___boxed as *mut core::ffi::c_void,
                    9,
                    1,
                );
                lean_closure_set(v_ctx_7706_, 0, v___x_7705_);
                v___x_7707_ = 0;
                if v_isShared_7704_ == 0 {
                    v___x_7709_ = v___x_7703_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7713_ = lean_alloc_ctor(0, 1, (4) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7713_, 0, v_toApplyRulesConfig_7698_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_7713_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                        v_intro_7699_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_7713_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 2) as u32,
                        v_constructor_7700_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_7713_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 3) as u32,
                        v_suggestions_7701_,
                    );
                    v___x_7709_ = v_reuseFailAlloc_7713_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_ctor_set_uint8(
                    v___x_7709_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_7707_,
                );
                v___x_7710_ = lean_box(0);
                v___x_7711_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_7711_, 0, v_g_7692_);
                lean_ctor_set(v___x_7711_, 1, v___x_7710_);
                v___x_7712_ = l_Lean_Meta_SolveByElim_solveByElim(
                    v___x_7709_,
                    v_lemmas_7690_,
                    v_ctx_7706_,
                    v___x_7711_,
                    v_a_7693_,
                    v_a_7694_,
                    v_a_7695_,
                    v_a_7696_,
                );
                return v___x_7712_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_applyRules___boxed(
    mut v_cfg_7715_: *mut LeanObject,
    mut v_lemmas_7716_: *mut LeanObject,
    mut v_only_7717_: *mut LeanObject,
    mut v_g_7718_: *mut LeanObject,
    mut v_a_7719_: *mut LeanObject,
    mut v_a_7720_: *mut LeanObject,
    mut v_a_7721_: *mut LeanObject,
    mut v_a_7722_: *mut LeanObject,
    mut v_a_7723_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_only_boxed_7724_: u8 = 0;
    let mut v_res_7725_: *mut LeanObject = core::ptr::null_mut();
    v_only_boxed_7724_ = (lean_unbox(v_only_7717_) as u8);
    v_res_7725_ = l_Lean_MVarId_applyRules(
        v_cfg_7715_,
        v_lemmas_7716_,
        v_only_boxed_7724_,
        v_g_7718_,
        v_a_7719_,
        v_a_7720_,
        v_a_7721_,
        v_a_7722_,
    );
    lean_dec(v_a_7722_);
    lean_dec_ref(v_a_7721_);
    lean_dec(v_a_7720_);
    lean_dec_ref(v_a_7719_);
    return v_res_7725_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5(
    mut v_as_7726_: *mut LeanObject,
    mut v_sz_7727_: usize,
    mut v_i_7728_: usize,
    mut v_b_7729_: *mut LeanObject,
    mut v___y_7730_: *mut LeanObject,
    mut v___y_7731_: *mut LeanObject,
    mut v___y_7732_: *mut LeanObject,
    mut v___y_7733_: *mut LeanObject,
    mut v___y_7734_: *mut LeanObject,
    mut v___y_7735_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7737_: *mut LeanObject = core::ptr::null_mut();
    v___x_7737_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(v_as_7726_, v_sz_7727_, v_i_7728_, v_b_7729_);
    return v___x_7737_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___boxed(
    mut v_as_7738_: *mut LeanObject,
    mut v_sz_7739_: *mut LeanObject,
    mut v_i_7740_: *mut LeanObject,
    mut v_b_7741_: *mut LeanObject,
    mut v___y_7742_: *mut LeanObject,
    mut v___y_7743_: *mut LeanObject,
    mut v___y_7744_: *mut LeanObject,
    mut v___y_7745_: *mut LeanObject,
    mut v___y_7746_: *mut LeanObject,
    mut v___y_7747_: *mut LeanObject,
    mut v___y_7748_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_7749_: usize = 0;
    let mut v_i_boxed_7750_: usize = 0;
    let mut v_res_7751_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_7749_ = lean_unbox_usize(v_sz_7739_);
    lean_dec(v_sz_7739_);
    v_i_boxed_7750_ = lean_unbox_usize(v_i_7740_);
    lean_dec(v_i_7740_);
    v_res_7751_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5(v_as_7738_, v_sz_boxed_7749_, v_i_boxed_7750_, v_b_7741_, v___y_7742_, v___y_7743_, v___y_7744_, v___y_7745_, v___y_7746_, v___y_7747_);
    lean_dec(v___y_7747_);
    lean_dec_ref(v___y_7746_);
    lean_dec(v___y_7745_);
    lean_dec_ref(v___y_7744_);
    lean_dec(v___y_7743_);
    lean_dec_ref(v___y_7742_);
    lean_dec_ref(v_as_7738_);
    return v_res_7751_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4(
    mut v_as_7752_: *mut LeanObject,
    mut v_sz_7753_: usize,
    mut v_i_7754_: usize,
    mut v_b_7755_: *mut LeanObject,
    mut v___y_7756_: *mut LeanObject,
    mut v___y_7757_: *mut LeanObject,
    mut v___y_7758_: *mut LeanObject,
    mut v___y_7759_: *mut LeanObject,
    mut v___y_7760_: *mut LeanObject,
    mut v___y_7761_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7763_: *mut LeanObject = core::ptr::null_mut();
    v___x_7763_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_as_7752_, v_sz_7753_, v_i_7754_, v_b_7755_);
    return v___x_7763_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(
    mut v_as_7764_: *mut LeanObject,
    mut v_sz_7765_: *mut LeanObject,
    mut v_i_7766_: *mut LeanObject,
    mut v_b_7767_: *mut LeanObject,
    mut v___y_7768_: *mut LeanObject,
    mut v___y_7769_: *mut LeanObject,
    mut v___y_7770_: *mut LeanObject,
    mut v___y_7771_: *mut LeanObject,
    mut v___y_7772_: *mut LeanObject,
    mut v___y_7773_: *mut LeanObject,
    mut v___y_7774_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_7775_: usize = 0;
    let mut v_i_boxed_7776_: usize = 0;
    let mut v_res_7777_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_7775_ = lean_unbox_usize(v_sz_7765_);
    lean_dec(v_sz_7765_);
    v_i_boxed_7776_ = lean_unbox_usize(v_i_7766_);
    lean_dec(v_i_7766_);
    v_res_7777_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4(v_as_7764_, v_sz_boxed_7775_, v_i_boxed_7776_, v_b_7767_, v___y_7768_, v___y_7769_, v___y_7770_, v___y_7771_, v___y_7772_, v___y_7773_);
    lean_dec(v___y_7773_);
    lean_dec_ref(v___y_7772_);
    lean_dec(v___y_7771_);
    lean_dec_ref(v___y_7770_);
    lean_dec(v___y_7769_);
    lean_dec_ref(v___y_7768_);
    lean_dec_ref(v_as_7764_);
    return v_res_7777_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(
    mut v_t_7778_: *mut LeanObject,
    mut v_a_7779_: *mut LeanObject,
    mut v_a_7780_: *mut LeanObject,
    mut v_a_7781_: *mut LeanObject,
    mut v_a_7782_: *mut LeanObject,
    mut v_a_7783_: *mut LeanObject,
    mut v_a_7784_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7787_: u8 = 0;
    let mut v___x_7788_: *mut LeanObject = core::ptr::null_mut();
    v___x_7786_ = lean_box(0);
    v___x_7787_ = 1;
    v___x_7788_ = l_Lean_Elab_Term_elabTerm(
        v_t_7778_,
        v___x_7786_,
        v___x_7787_,
        v___x_7787_,
        v_a_7779_,
        v_a_7780_,
        v_a_7781_,
        v_a_7782_,
        v_a_7783_,
        v_a_7784_,
    );
    return v___x_7788_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27___boxed(
    mut v_t_7789_: *mut LeanObject,
    mut v_a_7790_: *mut LeanObject,
    mut v_a_7791_: *mut LeanObject,
    mut v_a_7792_: *mut LeanObject,
    mut v_a_7793_: *mut LeanObject,
    mut v_a_7794_: *mut LeanObject,
    mut v_a_7795_: *mut LeanObject,
    mut v_a_7796_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7797_: *mut LeanObject = core::ptr::null_mut();
    v_res_7797_ =
        l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(
            v_t_7789_, v_a_7790_, v_a_7791_, v_a_7792_, v_a_7793_, v_a_7794_, v_a_7795_,
        );
    lean_dec(v_a_7795_);
    lean_dec_ref(v_a_7794_);
    lean_dec(v_a_7793_);
    lean_dec_ref(v_a_7792_);
    lean_dec(v_a_7791_);
    lean_dec_ref(v_a_7790_);
    return v_res_7797_;
}
pub unsafe fn l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(
    mut v___y_7798_: *mut LeanObject,
    mut v___y_7799_: *mut LeanObject,
    mut v___y_7800_: *mut LeanObject,
    mut v___y_7801_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_7803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7804_: u8 = 0;
    let mut v___x_7805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7806_: *mut LeanObject = core::ptr::null_mut();
    v_ref_7803_ = lean_ctor_get(v___y_7800_, 5);
    v___x_7804_ = 0;
    v___x_7805_ = l_Lean_SourceInfo_fromRef(v_ref_7803_, v___x_7804_);
    v___x_7806_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_7806_, 0, v___x_7805_);
    return v___x_7806_;
}
pub unsafe fn l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0___boxed(
    mut v___y_7807_: *mut LeanObject,
    mut v___y_7808_: *mut LeanObject,
    mut v___y_7809_: *mut LeanObject,
    mut v___y_7810_: *mut LeanObject,
    mut v___y_7811_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7812_: *mut LeanObject = core::ptr::null_mut();
    v_res_7812_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(
        v___y_7807_,
        v___y_7808_,
        v___y_7809_,
        v___y_7810_,
    );
    lean_dec(v___y_7810_);
    lean_dec_ref(v___y_7809_);
    lean_dec(v___y_7808_);
    lean_dec_ref(v___y_7807_);
    return v_res_7812_;
}
pub unsafe fn l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2_spec__2(
    mut v_a_7813_: *mut LeanObject,
    mut v_x_7814_: *mut LeanObject,
) -> u8 {
    let mut v___x_7815_: u8 = 0;
    let mut v_head_7816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_7817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7818_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_7814_) == 0 {
                    v___x_7815_ = 0;
                    return v___x_7815_;
                } else {
                    v_head_7816_ = lean_ctor_get(v_x_7814_, 0);
                    v_tail_7817_ = lean_ctor_get(v_x_7814_, 1);
                    v___x_7818_ = lean_expr_eqv(v_a_7813_, v_head_7816_);
                    if v___x_7818_ == 0 {
                        v_x_7814_ = v_tail_7817_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_7818_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2_spec__2___boxed(
    mut v_a_7820_: *mut LeanObject,
    mut v_x_7821_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7822_: u8 = 0;
    let mut v_r_7823_: *mut LeanObject = core::ptr::null_mut();
    v_res_7822_ = l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2_spec__2(v_a_7820_, v_x_7821_);
    lean_dec(v_x_7821_);
    lean_dec_ref(v_a_7820_);
    v_r_7823_ = lean_box((v_res_7822_) as usize);
    return v_r_7823_;
}
pub unsafe fn l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2___lam__0(
    mut v_ys_7824_: *mut LeanObject,
    mut v_x_7825_: *mut LeanObject,
) -> u8 {
    let mut v___x_7826_: u8 = 0;
    v___x_7826_ = l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2_spec__2(v_x_7825_, v_ys_7824_);
    if v___x_7826_ == 0 {
        let mut v___x_7827_: u8 = 0;
        v___x_7827_ = 1;
        return v___x_7827_;
    } else {
        let mut v___x_7828_: u8 = 0;
        v___x_7828_ = 0;
        return v___x_7828_;
    }
}
pub unsafe fn l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2___lam__0___boxed(
    mut v_ys_7829_: *mut LeanObject,
    mut v_x_7830_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7831_: u8 = 0;
    let mut v_r_7832_: *mut LeanObject = core::ptr::null_mut();
    v_res_7831_ = l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2___lam__0(
        v_ys_7829_, v_x_7830_,
    );
    lean_dec_ref(v_x_7830_);
    lean_dec(v_ys_7829_);
    v_r_7832_ = lean_box((v_res_7831_) as usize);
    return v_r_7832_;
}
pub unsafe fn l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2(
    mut v_xs_7833_: *mut LeanObject,
    mut v_ys_7834_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_7835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7836_: *mut LeanObject = core::ptr::null_mut();
    v___f_7835_ = lean_alloc_closure(
        l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2___lam__0___boxed
            as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_7835_, 0, v_ys_7834_);
    v___x_7836_ = l_List_filter___redArg(v___f_7835_, v_xs_7833_);
    return v___x_7836_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1(
    mut v_x_7837_: *mut LeanObject,
    mut v_x_7838_: *mut LeanObject,
    mut v___y_7839_: *mut LeanObject,
    mut v___y_7840_: *mut LeanObject,
    mut v___y_7841_: *mut LeanObject,
    mut v___y_7842_: *mut LeanObject,
    mut v___y_7843_: *mut LeanObject,
    mut v___y_7844_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_7848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_7849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7852_: u8 = 0;
    let mut v___x_7853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7862_: u8 = 0;
    let mut v___x_7864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7866_: u8 = 0;
    let mut v_isSharedCheck_7867_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_7837_) == 0 {
                    v___x_7846_ = l_List_reverse___redArg(v_x_7838_);
                    v___x_7847_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_7847_, 0, v___x_7846_);
                    return v___x_7847_;
                } else {
                    v_head_7848_ = lean_ctor_get(v_x_7837_, 0);
                    v_tail_7849_ = lean_ctor_get(v_x_7837_, 1);
                    v_isSharedCheck_7867_ = (!lean_is_exclusive(v_x_7837_)) as u8;
                    if v_isSharedCheck_7867_ == 0 {
                        v___x_7851_ = v_x_7837_;
                        v_isShared_7852_ = v_isSharedCheck_7867_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_7849_);
                        lean_inc(v_head_7848_);
                        lean_dec(v_x_7837_);
                        v___x_7851_ = lean_box(0);
                        v_isShared_7852_ = v_isSharedCheck_7867_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7853_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(v_head_7848_, v___y_7839_, v___y_7840_, v___y_7841_, v___y_7842_, v___y_7843_, v___y_7844_);
                if lean_obj_tag(v___x_7853_) == 0 {
                    v_a_7854_ = lean_ctor_get(v___x_7853_, 0);
                    lean_inc(v_a_7854_);
                    lean_dec_ref_known(v___x_7853_, 1);
                    if v_isShared_7852_ == 0 {
                        lean_ctor_set(v___x_7851_, 1, v_x_7838_);
                        lean_ctor_set(v___x_7851_, 0, v_a_7854_);
                        v___x_7856_ = v___x_7851_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_7858_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7858_, 0, v_a_7854_);
                        lean_ctor_set(v_reuseFailAlloc_7858_, 1, v_x_7838_);
                        v___x_7856_ = v_reuseFailAlloc_7858_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_7851_);
                    lean_dec(v_tail_7849_);
                    lean_dec(v_x_7838_);
                    v_a_7859_ = lean_ctor_get(v___x_7853_, 0);
                    v_isSharedCheck_7866_ = (!lean_is_exclusive(v___x_7853_)) as u8;
                    if v_isSharedCheck_7866_ == 0 {
                        v___x_7861_ = v___x_7853_;
                        v_isShared_7862_ = v_isSharedCheck_7866_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_7859_);
                        lean_dec(v___x_7853_);
                        v___x_7861_ = lean_box(0);
                        v_isShared_7862_ = v_isSharedCheck_7866_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v_x_7837_ = v_tail_7849_;
                v_x_7838_ = v___x_7856_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_7862_ == 0 {
                    v___x_7864_ = v___x_7861_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7865_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7865_, 0, v_a_7859_);
                    v___x_7864_ = v_reuseFailAlloc_7865_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7864_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1___boxed(
    mut v_x_7868_: *mut LeanObject,
    mut v_x_7869_: *mut LeanObject,
    mut v___y_7870_: *mut LeanObject,
    mut v___y_7871_: *mut LeanObject,
    mut v___y_7872_: *mut LeanObject,
    mut v___y_7873_: *mut LeanObject,
    mut v___y_7874_: *mut LeanObject,
    mut v___y_7875_: *mut LeanObject,
    mut v___y_7876_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7877_: *mut LeanObject = core::ptr::null_mut();
    v_res_7877_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1(
        v_x_7868_,
        v_x_7869_,
        v___y_7870_,
        v___y_7871_,
        v___y_7872_,
        v___y_7873_,
        v___y_7874_,
        v___y_7875_,
    );
    lean_dec(v___y_7875_);
    lean_dec_ref(v___y_7874_);
    lean_dec(v___y_7873_);
    lean_dec_ref(v___y_7872_);
    lean_dec(v___y_7871_);
    lean_dec_ref(v___y_7870_);
    return v_res_7877_;
}
pub unsafe fn l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1(
    mut v_remove_7878_: *mut LeanObject,
    mut v_noDefaults_7879_: u8,
    mut v_star_7880_: u8,
    mut v_cfg_7881_: *mut LeanObject,
    mut v___y_7882_: *mut LeanObject,
    mut v___y_7883_: *mut LeanObject,
    mut v___y_7884_: *mut LeanObject,
    mut v___y_7885_: *mut LeanObject,
    mut v___y_7886_: *mut LeanObject,
    mut v___y_7887_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplyRulesConfig_7894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_symm_7896_: u8 = 0;
    let mut v___x_7897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7903_: u8 = 0;
    let mut v___x_7905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7907_: u8 = 0;
    let mut v___x_7908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7909_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_noDefaults_7879_ == 0 {
                    state = 1;
                    continue;
                } else {
                    if v_star_7880_ == 0 {
                        lean_dec(v_remove_7878_);
                        v___x_7908_ = lean_box(0);
                        v___x_7909_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_7909_, 0, v___x_7908_);
                        return v___x_7909_;
                    } else {
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7890_ = l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(
                    v___y_7882_,
                    v___y_7883_,
                    v___y_7884_,
                    v___y_7885_,
                    v___y_7886_,
                    v___y_7887_,
                );
                if lean_obj_tag(v___x_7890_) == 0 {
                    v_a_7891_ = lean_ctor_get(v___x_7890_, 0);
                    lean_inc(v_a_7891_);
                    lean_dec_ref_known(v___x_7890_, 1);
                    v___x_7892_ = lean_box(0);
                    v___x_7893_ =
                        l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1(
                            v_remove_7878_,
                            v___x_7892_,
                            v___y_7882_,
                            v___y_7883_,
                            v___y_7884_,
                            v___y_7885_,
                            v___y_7886_,
                            v___y_7887_,
                        );
                    if lean_obj_tag(v___x_7893_) == 0 {
                        v_toApplyRulesConfig_7894_ = lean_ctor_get(v_cfg_7881_, 0);
                        v_a_7895_ = lean_ctor_get(v___x_7893_, 0);
                        lean_inc(v_a_7895_);
                        lean_dec_ref_known(v___x_7893_, 1);
                        v_symm_7896_ = lean_ctor_get_uint8(
                            v_toApplyRulesConfig_7894_,
                            (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                        );
                        v___x_7897_ = lean_array_to_list(v_a_7891_);
                        v___x_7898_ =
                            l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2(
                                v___x_7897_,
                                v_a_7895_,
                            );
                        v___x_7899_ = l_Lean_Meta_SolveByElim_saturateSymm(
                            v_symm_7896_,
                            v___x_7898_,
                            v___y_7884_,
                            v___y_7885_,
                            v___y_7886_,
                            v___y_7887_,
                        );
                        return v___x_7899_;
                    } else {
                        lean_dec(v_a_7891_);
                        return v___x_7893_;
                    }
                } else {
                    lean_dec(v_remove_7878_);
                    v_a_7900_ = lean_ctor_get(v___x_7890_, 0);
                    v_isSharedCheck_7907_ = (!lean_is_exclusive(v___x_7890_)) as u8;
                    if v_isSharedCheck_7907_ == 0 {
                        v___x_7902_ = v___x_7890_;
                        v_isShared_7903_ = v_isSharedCheck_7907_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_7900_);
                        lean_dec(v___x_7890_);
                        v___x_7902_ = lean_box(0);
                        v_isShared_7903_ = v_isSharedCheck_7907_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_7903_ == 0 {
                    v___x_7905_ = v___x_7902_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7906_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7906_, 0, v_a_7900_);
                    v___x_7905_ = v_reuseFailAlloc_7906_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_7905_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1___boxed(
    mut v_remove_7910_: *mut LeanObject,
    mut v_noDefaults_7911_: *mut LeanObject,
    mut v_star_7912_: *mut LeanObject,
    mut v_cfg_7913_: *mut LeanObject,
    mut v___y_7914_: *mut LeanObject,
    mut v___y_7915_: *mut LeanObject,
    mut v___y_7916_: *mut LeanObject,
    mut v___y_7917_: *mut LeanObject,
    mut v___y_7918_: *mut LeanObject,
    mut v___y_7919_: *mut LeanObject,
    mut v___y_7920_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_noDefaults_boxed_7921_: u8 = 0;
    let mut v_star_boxed_7922_: u8 = 0;
    let mut v_res_7923_: *mut LeanObject = core::ptr::null_mut();
    v_noDefaults_boxed_7921_ = (lean_unbox(v_noDefaults_7911_) as u8);
    v_star_boxed_7922_ = (lean_unbox(v_star_7912_) as u8);
    v_res_7923_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1(
        v_remove_7910_,
        v_noDefaults_boxed_7921_,
        v_star_boxed_7922_,
        v_cfg_7913_,
        v___y_7914_,
        v___y_7915_,
        v___y_7916_,
        v___y_7917_,
        v___y_7918_,
        v___y_7919_,
    );
    lean_dec(v___y_7919_);
    lean_dec_ref(v___y_7918_);
    lean_dec(v___y_7917_);
    lean_dec_ref(v___y_7916_);
    lean_dec(v___y_7915_);
    lean_dec_ref(v___y_7914_);
    lean_dec_ref(v_cfg_7913_);
    return v_res_7923_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(
    mut v_as_7924_: *mut LeanObject,
    mut v_i_7925_: usize,
    mut v_stop_7926_: usize,
    mut v_b_7927_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7928_: u8 = 0;
    let mut v___x_7929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7931_: usize = 0;
    let mut v___x_7932_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7928_ = lean_usize_dec_eq(v_i_7925_, v_stop_7926_);
                if v___x_7928_ == 0 {
                    v___x_7929_ = lean_array_uget_borrowed(v_as_7924_, v_i_7925_);
                    v___x_7930_ = l_Array_append___redArg(v_b_7927_, v___x_7929_);
                    v___x_7931_ = 1usize;
                    v___x_7932_ = lean_usize_add(v_i_7925_, v___x_7931_);
                    v_i_7925_ = v___x_7932_;
                    v_b_7927_ = v___x_7930_;
                    state = 0;
                    continue;
                } else {
                    return v_b_7927_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5___boxed(
    mut v_as_7934_: *mut LeanObject,
    mut v_i_7935_: *mut LeanObject,
    mut v_stop_7936_: *mut LeanObject,
    mut v_b_7937_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_7938_: usize = 0;
    let mut v_stop_boxed_7939_: usize = 0;
    let mut v_res_7940_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_7938_ = lean_unbox_usize(v_i_7935_);
    lean_dec(v_i_7935_);
    v_stop_boxed_7939_ = lean_unbox_usize(v_stop_7936_);
    lean_dec(v_stop_7936_);
    v_res_7940_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(v_as_7934_, v_i_boxed_7938_, v_stop_boxed_7939_, v_b_7937_);
    lean_dec_ref(v_as_7934_);
    return v_res_7940_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(
    mut v_a_7941_: *mut LeanObject,
    mut v_a_7942_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_7944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_7945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7948_: u8 = 0;
    let mut v___x_7949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7954_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_7941_) == 0 {
                    v___x_7943_ = l_List_reverse___redArg(v_a_7942_);
                    return v___x_7943_;
                } else {
                    v_head_7944_ = lean_ctor_get(v_a_7941_, 0);
                    v_tail_7945_ = lean_ctor_get(v_a_7941_, 1);
                    v_isSharedCheck_7954_ = (!lean_is_exclusive(v_a_7941_)) as u8;
                    if v_isSharedCheck_7954_ == 0 {
                        v___x_7947_ = v_a_7941_;
                        v_isShared_7948_ = v_isSharedCheck_7954_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_7945_);
                        lean_inc(v_head_7944_);
                        lean_dec(v_a_7941_);
                        v___x_7947_ = lean_box(0);
                        v_isShared_7948_ = v_isSharedCheck_7954_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7949_ = lean_alloc_closure(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27___boxed as *mut core::ffi::c_void, 8, 1);
                lean_closure_set(v___x_7949_, 0, v_head_7944_);
                if v_isShared_7948_ == 0 {
                    lean_ctor_set(v___x_7947_, 1, v_a_7942_);
                    lean_ctor_set(v___x_7947_, 0, v___x_7949_);
                    v___x_7951_ = v___x_7947_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7953_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7953_, 0, v___x_7949_);
                    lean_ctor_set(v_reuseFailAlloc_7953_, 1, v_a_7942_);
                    v___x_7951_ = v_reuseFailAlloc_7953_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_7941_ = v_tail_7945_;
                v_a_7942_ = v___x_7951_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg(
    mut v_sz_7955_: usize,
    mut v_i_7956_: usize,
    mut v_bs_7957_: *mut LeanObject,
    mut v___y_7958_: *mut LeanObject,
    mut v___y_7959_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7961_: u8 = 0;
    let mut v___x_7962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_7963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_7968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7969_: usize = 0;
    let mut v___x_7970_: usize = 0;
    let mut v___x_7971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7976_: u8 = 0;
    let mut v___x_7978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7980_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7961_ = lean_usize_dec_lt(v_i_7956_, v_sz_7955_);
                if v___x_7961_ == 0 {
                    v___x_7962_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_7962_, 0, v_bs_7957_);
                    return v___x_7962_;
                } else {
                    v_v_7963_ = lean_array_uget_borrowed(v_bs_7957_, v_i_7956_);
                    v___x_7964_ = l_Lean_Syntax_getId(v_v_7963_);
                    v___x_7965_ = l_Lean_labelled(v___x_7964_, v___y_7958_, v___y_7959_);
                    if lean_obj_tag(v___x_7965_) == 0 {
                        v_a_7966_ = lean_ctor_get(v___x_7965_, 0);
                        lean_inc(v_a_7966_);
                        lean_dec_ref_known(v___x_7965_, 1);
                        v___x_7967_ = lean_unsigned_to_nat(0);
                        v_bs_x27_7968_ = lean_array_uset(v_bs_7957_, v_i_7956_, v___x_7967_);
                        v___x_7969_ = 1usize;
                        v___x_7970_ = lean_usize_add(v_i_7956_, v___x_7969_);
                        v___x_7971_ = lean_array_uset(v_bs_x27_7968_, v_i_7956_, v_a_7966_);
                        v_i_7956_ = v___x_7970_;
                        v_bs_7957_ = v___x_7971_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_bs_7957_);
                        v_a_7973_ = lean_ctor_get(v___x_7965_, 0);
                        v_isSharedCheck_7980_ = (!lean_is_exclusive(v___x_7965_)) as u8;
                        if v_isSharedCheck_7980_ == 0 {
                            v___x_7975_ = v___x_7965_;
                            v_isShared_7976_ = v_isSharedCheck_7980_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_7973_);
                            lean_dec(v___x_7965_);
                            v___x_7975_ = lean_box(0);
                            v_isShared_7976_ = v_isSharedCheck_7980_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_7976_ == 0 {
                    v___x_7978_ = v___x_7975_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7979_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7979_, 0, v_a_7973_);
                    v___x_7978_ = v_reuseFailAlloc_7979_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7978_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg___boxed(
    mut v_sz_7981_: *mut LeanObject,
    mut v_i_7982_: *mut LeanObject,
    mut v_bs_7983_: *mut LeanObject,
    mut v___y_7984_: *mut LeanObject,
    mut v___y_7985_: *mut LeanObject,
    mut v___y_7986_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_7987_: usize = 0;
    let mut v_i_boxed_7988_: usize = 0;
    let mut v_res_7989_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_7987_ = lean_unbox_usize(v_sz_7981_);
    lean_dec(v_sz_7981_);
    v_i_boxed_7988_ = lean_unbox_usize(v_i_7982_);
    lean_dec(v_i_7982_);
    v_res_7989_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg(v_sz_boxed_7987_, v_i_boxed_7988_, v_bs_7983_, v___y_7984_, v___y_7985_);
    lean_dec(v___y_7985_);
    lean_dec_ref(v___y_7984_);
    return v_res_7989_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0(
    mut v_head_7990_: *mut LeanObject,
    mut v___y_7991_: *mut LeanObject,
    mut v___y_7992_: *mut LeanObject,
    mut v___y_7993_: *mut LeanObject,
    mut v___y_7994_: *mut LeanObject,
    mut v___y_7995_: *mut LeanObject,
    mut v___y_7996_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7998_: *mut LeanObject = core::ptr::null_mut();
    v___x_7998_ = l_Lean_Meta_mkConstWithFreshMVarLevels(
        v_head_7990_,
        v___y_7993_,
        v___y_7994_,
        v___y_7995_,
        v___y_7996_,
    );
    return v___x_7998_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0___boxed(
    mut v_head_7999_: *mut LeanObject,
    mut v___y_8000_: *mut LeanObject,
    mut v___y_8001_: *mut LeanObject,
    mut v___y_8002_: *mut LeanObject,
    mut v___y_8003_: *mut LeanObject,
    mut v___y_8004_: *mut LeanObject,
    mut v___y_8005_: *mut LeanObject,
    mut v___y_8006_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8007_: *mut LeanObject = core::ptr::null_mut();
    v_res_8007_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0(
        v_head_7999_,
        v___y_8000_,
        v___y_8001_,
        v___y_8002_,
        v___y_8003_,
        v___y_8004_,
        v___y_8005_,
    );
    lean_dec(v___y_8005_);
    lean_dec_ref(v___y_8004_);
    lean_dec(v___y_8003_);
    lean_dec_ref(v___y_8002_);
    lean_dec(v___y_8001_);
    lean_dec_ref(v___y_8000_);
    return v_res_8007_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4(
    mut v_a_8008_: *mut LeanObject,
    mut v_a_8009_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_8011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_8012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8015_: u8 = 0;
    let mut v___f_8016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8021_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_8008_) == 0 {
                    v___x_8010_ = l_List_reverse___redArg(v_a_8009_);
                    return v___x_8010_;
                } else {
                    v_head_8011_ = lean_ctor_get(v_a_8008_, 0);
                    v_tail_8012_ = lean_ctor_get(v_a_8008_, 1);
                    v_isSharedCheck_8021_ = (!lean_is_exclusive(v_a_8008_)) as u8;
                    if v_isSharedCheck_8021_ == 0 {
                        v___x_8014_ = v_a_8008_;
                        v_isShared_8015_ = v_isSharedCheck_8021_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_8012_);
                        lean_inc(v_head_8011_);
                        lean_dec(v_a_8008_);
                        v___x_8014_ = lean_box(0);
                        v_isShared_8015_ = v_isSharedCheck_8021_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___f_8016_ = lean_alloc_closure(l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                lean_closure_set(v___f_8016_, 0, v_head_8011_);
                if v_isShared_8015_ == 0 {
                    lean_ctor_set(v___x_8014_, 1, v_a_8009_);
                    lean_ctor_set(v___x_8014_, 0, v___f_8016_);
                    v___x_8018_ = v___x_8014_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8020_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8020_, 0, v___f_8016_);
                    lean_ctor_set(v_reuseFailAlloc_8020_, 1, v_a_8009_);
                    v___x_8018_ = v_reuseFailAlloc_8020_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_8008_ = v_tail_8012_;
                v_a_8009_ = v___x_8018_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1() -> *mut LeanObject {
    let mut v___x_8023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8024_: *mut LeanObject = core::ptr::null_mut();
    v___x_8023_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__0;
    v___x_8024_ = l_Lean_stringToMessageData(v___x_8023_);
    return v___x_8024_;
}
pub unsafe fn _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3() -> *mut LeanObject {
    let mut v___x_8026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8027_: *mut LeanObject = core::ptr::null_mut();
    v___x_8026_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__2;
    v___x_8027_ = l_String_toRawSubstring_x27(v___x_8026_);
    return v___x_8027_;
}
pub unsafe fn _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6() -> *mut LeanObject {
    let mut v___x_8031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8032_: *mut LeanObject = core::ptr::null_mut();
    v___x_8031_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__5;
    v___x_8032_ = l_String_toRawSubstring_x27(v___x_8031_);
    return v___x_8032_;
}
pub unsafe fn _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9() -> *mut LeanObject {
    let mut v___x_8036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8037_: *mut LeanObject = core::ptr::null_mut();
    v___x_8036_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__8;
    v___x_8037_ = l_String_toRawSubstring_x27(v___x_8036_);
    return v___x_8037_;
}
pub unsafe fn _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12() -> *mut LeanObject {
    let mut v___x_8041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8042_: *mut LeanObject = core::ptr::null_mut();
    v___x_8041_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__11;
    v___x_8042_ = l_String_toRawSubstring_x27(v___x_8041_);
    return v___x_8042_;
}
pub unsafe fn _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24() -> *mut LeanObject {
    let mut v___x_8072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8073_: *mut LeanObject = core::ptr::null_mut();
    v___x_8072_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__23;
    v___x_8073_ = l_Lean_stringToMessageData(v___x_8072_);
    return v___x_8073_;
}
pub unsafe fn l_Lean_Meta_SolveByElim_mkAssumptionSet(
    mut v_noDefaults_8074_: u8,
    mut v_star_8075_: u8,
    mut v_add_8076_: *mut LeanObject,
    mut v_remove_8077_: *mut LeanObject,
    mut v_use_8078_: *mut LeanObject,
    mut v_a_8079_: *mut LeanObject,
    mut v_a_8080_: *mut LeanObject,
    mut v_a_8081_: *mut LeanObject,
    mut v_a_8082_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_8085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8096_: u8 = 0;
    let mut v___x_8097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8102_: u8 = 0;
    let mut v___x_8104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8106_: u8 = 0;
    let mut v___x_8107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_8130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_8131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_8132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_8146_: usize = 0;
    let mut v___x_8147_: usize = 0;
    let mut v___x_8148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8155_: u8 = 0;
    let mut v___x_8156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8174_: u8 = 0;
    let mut v___x_8175_: u8 = 0;
    let mut v___x_8176_: usize = 0;
    let mut v___x_8177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8178_: usize = 0;
    let mut v___x_8179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8183_: u8 = 0;
    let mut v___x_8185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8187_: u8 = 0;
    let mut v___x_8188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8193_: u8 = 0;
    let mut v___x_8195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8197_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8107_ = lean_box((v_noDefaults_8074_) as usize);
                v___x_8108_ = lean_box((v_star_8075_) as usize);
                lean_inc(v_remove_8077_);
                v___f_8109_ = lean_alloc_closure(
                    l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1___boxed
                        as *mut core::ffi::c_void,
                    11,
                    3,
                );
                lean_closure_set(v___f_8109_, 0, v_remove_8077_);
                lean_closure_set(v___f_8109_, 1, v___x_8107_);
                lean_closure_set(v___f_8109_, 2, v___x_8108_);
                if v_star_8075_ == 0 {
                    v___y_8126_ = v_a_8079_;
                    v___y_8127_ = v_a_8080_;
                    v___y_8128_ = v_a_8081_;
                    v___y_8129_ = v_a_8082_;
                    state = 6;
                    continue;
                } else {
                    if v_noDefaults_8074_ == 0 {
                        lean_dec_ref(v___f_8109_);
                        lean_dec_ref(v_use_8078_);
                        lean_dec(v_remove_8077_);
                        lean_dec(v_add_8076_);
                        v___x_8188_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24_once
                            ),
                            _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24,
                        );
                        v___x_8189_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_8188_, v_a_8079_, v_a_8080_, v_a_8081_, v_a_8082_);
                        v_a_8190_ = lean_ctor_get(v___x_8189_, 0);
                        v_isSharedCheck_8197_ = (!lean_is_exclusive(v___x_8189_)) as u8;
                        if v_isSharedCheck_8197_ == 0 {
                            v___x_8192_ = v___x_8189_;
                            v_isShared_8193_ = v_isSharedCheck_8197_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_8190_);
                            lean_dec(v___x_8189_);
                            v___x_8192_ = lean_box(0);
                            v_isShared_8193_ = v_isSharedCheck_8197_;
                            state = 9;
                            continue;
                        }
                    } else {
                        v___y_8126_ = v_a_8079_;
                        v___y_8127_ = v_a_8080_;
                        v___y_8128_ = v_a_8081_;
                        v___y_8129_ = v_a_8082_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_8087_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_8087_, 0, v___y_8085_);
                lean_ctor_set(v___x_8087_, 1, v___y_8086_);
                v___x_8088_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_8088_, 0, v___x_8087_);
                return v___x_8088_;
            }
            2 => {
                v___x_8096_ = l_List_isEmpty___redArg(v_remove_8077_);
                lean_dec(v_remove_8077_);
                if v___x_8096_ == 0 {
                    if v_noDefaults_8074_ == 0 {
                        v___y_8085_ = v___y_8095_;
                        v___y_8086_ = v___y_8094_;
                        state = 1;
                        continue;
                    } else {
                        if v_star_8075_ == 0 {
                            lean_dec(v___y_8095_);
                            lean_dec_ref(v___y_8094_);
                            v___x_8097_ = lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1_once
                                ),
                                _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1,
                            );
                            v___x_8098_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_8097_, v___y_8091_, v___y_8090_, v___y_8093_, v___y_8092_);
                            v_a_8099_ = lean_ctor_get(v___x_8098_, 0);
                            v_isSharedCheck_8106_ = (!lean_is_exclusive(v___x_8098_)) as u8;
                            if v_isSharedCheck_8106_ == 0 {
                                v___x_8101_ = v___x_8098_;
                                v_isShared_8102_ = v_isSharedCheck_8106_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_8099_);
                                lean_dec(v___x_8098_);
                                v___x_8101_ = lean_box(0);
                                v_isShared_8102_ = v_isSharedCheck_8106_;
                                state = 3;
                                continue;
                            }
                        } else {
                            v___y_8085_ = v___y_8095_;
                            v___y_8086_ = v___y_8094_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v___y_8085_ = v___y_8095_;
                    v___y_8086_ = v___y_8094_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v_isShared_8102_ == 0 {
                    v___x_8104_ = v___x_8101_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8105_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8105_, 0, v_a_8099_);
                    v___x_8104_ = v_reuseFailAlloc_8105_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_8104_;
            }
            5 => {
                v___x_8118_ = lean_array_to_list(v___y_8117_);
                lean_inc(v___y_8113_);
                v___x_8119_ =
                    l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4(
                        v___x_8118_,
                        v___y_8113_,
                    );
                if v_noDefaults_8074_ == 0 {
                    v___x_8120_ =
                        l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(
                            v_add_8076_,
                            v___y_8113_,
                        );
                    v___x_8121_ = l_List_appendTR___redArg(v___x_8120_, v___x_8119_);
                    v___x_8122_ = l_List_appendTR___redArg(v___x_8121_, v___y_8116_);
                    v___y_8090_ = v___y_8111_;
                    v___y_8091_ = v___y_8112_;
                    v___y_8092_ = v___y_8114_;
                    v___y_8093_ = v___y_8115_;
                    v___y_8094_ = v___f_8109_;
                    v___y_8095_ = v___x_8122_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v___y_8116_);
                    v___x_8123_ =
                        l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(
                            v_add_8076_,
                            v___y_8113_,
                        );
                    v___x_8124_ = l_List_appendTR___redArg(v___x_8123_, v___x_8119_);
                    v___y_8090_ = v___y_8111_;
                    v___y_8091_ = v___y_8112_;
                    v___y_8092_ = v___y_8114_;
                    v___y_8093_ = v___y_8115_;
                    v___y_8094_ = v___f_8109_;
                    v___y_8095_ = v___x_8124_;
                    state = 2;
                    continue;
                }
            }
            6 => {
                v_ref_8130_ = lean_ctor_get(v___y_8128_, 5);
                v_quotContext_8131_ = lean_ctor_get(v___y_8128_, 10);
                v_currMacroScope_8132_ = lean_ctor_get(v___y_8128_, 11);
                v___x_8133_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(
                    v___y_8126_,
                    v___y_8127_,
                    v___y_8128_,
                    v___y_8129_,
                );
                v_a_8134_ = lean_ctor_get(v___x_8133_, 0);
                lean_inc(v_a_8134_);
                lean_dec_ref(v___x_8133_);
                v___x_8135_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3_once
                    ),
                    _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3,
                );
                v___x_8136_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(
                    v___y_8126_,
                    v___y_8127_,
                    v___y_8128_,
                    v___y_8129_,
                );
                v_a_8137_ = lean_ctor_get(v___x_8136_, 0);
                lean_inc(v_a_8137_);
                lean_dec_ref(v___x_8136_);
                v___x_8138_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__4;
                lean_inc_n(v_currMacroScope_8132_, 2);
                lean_inc_n(v_quotContext_8131_, 2);
                v___x_8139_ =
                    l_Lean_addMacroScope(v_quotContext_8131_, v___x_8138_, v_currMacroScope_8132_);
                v___x_8140_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6_once
                    ),
                    _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6,
                );
                v___x_8141_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(
                    v___y_8126_,
                    v___y_8127_,
                    v___y_8128_,
                    v___y_8129_,
                );
                v_a_8142_ = lean_ctor_get(v___x_8141_, 0);
                lean_inc(v_a_8142_);
                lean_dec_ref(v___x_8141_);
                v___x_8143_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__7;
                v___x_8144_ =
                    l_Lean_addMacroScope(v_quotContext_8131_, v___x_8143_, v_currMacroScope_8132_);
                v___x_8145_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9_once
                    ),
                    _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9,
                );
                v_sz_8146_ = lean_array_size(v_use_8078_);
                v___x_8147_ = 0usize;
                v___x_8148_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg(v_sz_8146_, v___x_8147_, v_use_8078_, v___y_8128_, v___y_8129_);
                if lean_obj_tag(v___x_8148_) == 0 {
                    v_a_8149_ = lean_ctor_get(v___x_8148_, 0);
                    lean_inc(v_a_8149_);
                    lean_dec_ref_known(v___x_8148_, 1);
                    v___x_8150_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__10;
                    lean_inc_n(v_currMacroScope_8132_, 2);
                    lean_inc_n(v_quotContext_8131_, 2);
                    v___x_8151_ = l_Lean_addMacroScope(
                        v_quotContext_8131_,
                        v___x_8150_,
                        v_currMacroScope_8132_,
                    );
                    v___x_8152_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12_once
                        ),
                        _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12,
                    );
                    v___x_8153_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__13;
                    v___x_8154_ = l_Lean_addMacroScope(
                        v_quotContext_8131_,
                        v___x_8153_,
                        v_currMacroScope_8132_,
                    );
                    v___x_8155_ = 0;
                    v___x_8156_ = l_Lean_SourceInfo_fromRef(v_ref_8130_, v___x_8155_);
                    v___x_8157_ = lean_box(0);
                    v___x_8158_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__15;
                    v___x_8159_ = lean_alloc_ctor(3, 4, (0) as u32);
                    lean_ctor_set(v___x_8159_, 0, v___x_8156_);
                    lean_ctor_set(v___x_8159_, 1, v___x_8135_);
                    lean_ctor_set(v___x_8159_, 2, v___x_8139_);
                    lean_ctor_set(v___x_8159_, 3, v___x_8158_);
                    v___x_8160_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__17;
                    v___x_8161_ = lean_alloc_ctor(3, 4, (0) as u32);
                    lean_ctor_set(v___x_8161_, 0, v_a_8134_);
                    lean_ctor_set(v___x_8161_, 1, v___x_8140_);
                    lean_ctor_set(v___x_8161_, 2, v___x_8144_);
                    lean_ctor_set(v___x_8161_, 3, v___x_8160_);
                    v___x_8162_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__19;
                    v___x_8163_ = lean_alloc_ctor(3, 4, (0) as u32);
                    lean_ctor_set(v___x_8163_, 0, v_a_8137_);
                    lean_ctor_set(v___x_8163_, 1, v___x_8145_);
                    lean_ctor_set(v___x_8163_, 2, v___x_8151_);
                    lean_ctor_set(v___x_8163_, 3, v___x_8162_);
                    v___x_8164_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__21;
                    v___x_8165_ = lean_alloc_ctor(3, 4, (0) as u32);
                    lean_ctor_set(v___x_8165_, 0, v_a_8142_);
                    lean_ctor_set(v___x_8165_, 1, v___x_8152_);
                    lean_ctor_set(v___x_8165_, 2, v___x_8154_);
                    lean_ctor_set(v___x_8165_, 3, v___x_8164_);
                    v___x_8166_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_8166_, 0, v___x_8165_);
                    lean_ctor_set(v___x_8166_, 1, v___x_8157_);
                    v___x_8167_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_8167_, 0, v___x_8163_);
                    lean_ctor_set(v___x_8167_, 1, v___x_8166_);
                    v___x_8168_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_8168_, 0, v___x_8161_);
                    lean_ctor_set(v___x_8168_, 1, v___x_8167_);
                    v___x_8169_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_8169_, 0, v___x_8159_);
                    lean_ctor_set(v___x_8169_, 1, v___x_8168_);
                    v___x_8170_ =
                        l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(
                            v___x_8169_,
                            v___x_8157_,
                        );
                    v___x_8171_ = lean_unsigned_to_nat(0);
                    v___x_8172_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__22;
                    v___x_8173_ = lean_array_get_size(v_a_8149_);
                    v___x_8174_ = lean_nat_dec_lt(v___x_8171_, v___x_8173_);
                    if v___x_8174_ == 0 {
                        lean_dec(v_a_8149_);
                        v___y_8111_ = v___y_8127_;
                        v___y_8112_ = v___y_8126_;
                        v___y_8113_ = v___x_8157_;
                        v___y_8114_ = v___y_8129_;
                        v___y_8115_ = v___y_8128_;
                        v___y_8116_ = v___x_8170_;
                        v___y_8117_ = v___x_8172_;
                        state = 5;
                        continue;
                    } else {
                        v___x_8175_ = lean_nat_dec_le(v___x_8173_, v___x_8173_);
                        if v___x_8175_ == 0 {
                            if v___x_8174_ == 0 {
                                lean_dec(v_a_8149_);
                                v___y_8111_ = v___y_8127_;
                                v___y_8112_ = v___y_8126_;
                                v___y_8113_ = v___x_8157_;
                                v___y_8114_ = v___y_8129_;
                                v___y_8115_ = v___y_8128_;
                                v___y_8116_ = v___x_8170_;
                                v___y_8117_ = v___x_8172_;
                                state = 5;
                                continue;
                            } else {
                                v___x_8176_ = lean_usize_of_nat(v___x_8173_);
                                v___x_8177_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(v_a_8149_, v___x_8147_, v___x_8176_, v___x_8172_);
                                lean_dec(v_a_8149_);
                                v___y_8111_ = v___y_8127_;
                                v___y_8112_ = v___y_8126_;
                                v___y_8113_ = v___x_8157_;
                                v___y_8114_ = v___y_8129_;
                                v___y_8115_ = v___y_8128_;
                                v___y_8116_ = v___x_8170_;
                                v___y_8117_ = v___x_8177_;
                                state = 5;
                                continue;
                            }
                        } else {
                            v___x_8178_ = lean_usize_of_nat(v___x_8173_);
                            v___x_8179_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(v_a_8149_, v___x_8147_, v___x_8178_, v___x_8172_);
                            lean_dec(v_a_8149_);
                            v___y_8111_ = v___y_8127_;
                            v___y_8112_ = v___y_8126_;
                            v___y_8113_ = v___x_8157_;
                            v___y_8114_ = v___y_8129_;
                            v___y_8115_ = v___y_8128_;
                            v___y_8116_ = v___x_8170_;
                            v___y_8117_ = v___x_8179_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_8144_);
                    lean_dec(v_a_8142_);
                    lean_dec(v___x_8139_);
                    lean_dec(v_a_8137_);
                    lean_dec(v_a_8134_);
                    lean_dec_ref(v___f_8109_);
                    lean_dec(v_remove_8077_);
                    lean_dec(v_add_8076_);
                    v_a_8180_ = lean_ctor_get(v___x_8148_, 0);
                    v_isSharedCheck_8187_ = (!lean_is_exclusive(v___x_8148_)) as u8;
                    if v_isSharedCheck_8187_ == 0 {
                        v___x_8182_ = v___x_8148_;
                        v_isShared_8183_ = v_isSharedCheck_8187_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_8180_);
                        lean_dec(v___x_8148_);
                        v___x_8182_ = lean_box(0);
                        v_isShared_8183_ = v_isSharedCheck_8187_;
                        state = 7;
                        continue;
                    }
                }
            }
            7 => {
                if v_isShared_8183_ == 0 {
                    v___x_8185_ = v___x_8182_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_8186_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8186_, 0, v_a_8180_);
                    v___x_8185_ = v_reuseFailAlloc_8186_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_8185_;
            }
            9 => {
                if v_isShared_8193_ == 0 {
                    v___x_8195_ = v___x_8192_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_8196_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8196_, 0, v_a_8190_);
                    v___x_8195_ = v_reuseFailAlloc_8196_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_8195_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_SolveByElim_mkAssumptionSet___boxed(
    mut v_noDefaults_8198_: *mut LeanObject,
    mut v_star_8199_: *mut LeanObject,
    mut v_add_8200_: *mut LeanObject,
    mut v_remove_8201_: *mut LeanObject,
    mut v_use_8202_: *mut LeanObject,
    mut v_a_8203_: *mut LeanObject,
    mut v_a_8204_: *mut LeanObject,
    mut v_a_8205_: *mut LeanObject,
    mut v_a_8206_: *mut LeanObject,
    mut v_a_8207_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_noDefaults_boxed_8208_: u8 = 0;
    let mut v_star_boxed_8209_: u8 = 0;
    let mut v_res_8210_: *mut LeanObject = core::ptr::null_mut();
    v_noDefaults_boxed_8208_ = (lean_unbox(v_noDefaults_8198_) as u8);
    v_star_boxed_8209_ = (lean_unbox(v_star_8199_) as u8);
    v_res_8210_ = l_Lean_Meta_SolveByElim_mkAssumptionSet(
        v_noDefaults_boxed_8208_,
        v_star_boxed_8209_,
        v_add_8200_,
        v_remove_8201_,
        v_use_8202_,
        v_a_8203_,
        v_a_8204_,
        v_a_8205_,
        v_a_8206_,
    );
    lean_dec(v_a_8206_);
    lean_dec_ref(v_a_8205_);
    lean_dec(v_a_8204_);
    lean_dec_ref(v_a_8203_);
    return v_res_8210_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0(
    mut v_sz_8211_: usize,
    mut v_i_8212_: usize,
    mut v_bs_8213_: *mut LeanObject,
    mut v___y_8214_: *mut LeanObject,
    mut v___y_8215_: *mut LeanObject,
    mut v___y_8216_: *mut LeanObject,
    mut v___y_8217_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8219_: *mut LeanObject = core::ptr::null_mut();
    v___x_8219_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg(v_sz_8211_, v_i_8212_, v_bs_8213_, v___y_8216_, v___y_8217_);
    return v___x_8219_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___boxed(
    mut v_sz_8220_: *mut LeanObject,
    mut v_i_8221_: *mut LeanObject,
    mut v_bs_8222_: *mut LeanObject,
    mut v___y_8223_: *mut LeanObject,
    mut v___y_8224_: *mut LeanObject,
    mut v___y_8225_: *mut LeanObject,
    mut v___y_8226_: *mut LeanObject,
    mut v___y_8227_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_8228_: usize = 0;
    let mut v_i_boxed_8229_: usize = 0;
    let mut v_res_8230_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_8228_ = lean_unbox_usize(v_sz_8220_);
    lean_dec(v_sz_8220_);
    v_i_boxed_8229_ = lean_unbox_usize(v_i_8221_);
    lean_dec(v_i_8221_);
    v_res_8230_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0(v_sz_boxed_8228_, v_i_boxed_8229_, v_bs_8222_, v___y_8223_, v___y_8224_, v___y_8225_, v___y_8226_);
    lean_dec(v___y_8226_);
    lean_dec_ref(v___y_8225_);
    lean_dec(v___y_8224_);
    lean_dec_ref(v___y_8223_);
    return v_res_8230_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_SolveByElim(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Sum(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_LabelAttribute(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Backtrack(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Constructor(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Repeat(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Symm(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Term(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_SolveByElim(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_SolveByElim(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Sum(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_LabelAttribute(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Backtrack(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Constructor(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Repeat(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Symm(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Term(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_SolveByElim(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_SolveByElim(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_SolveByElim(builtin);
}
